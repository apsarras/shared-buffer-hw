/**
 * @info   Multi-queue Shared Buffer
 *
 * @author Anastasios Psarras (a.psarras4225@gmail.com)
 *
 * @license MIT license -- check license.md
 *
 * @brief  Buffer supporting multiple queues and dynamic buffer space allocation.
 *         Single-clock implementation (common write-read clocks) of the dual-clock (separate write-read clocks) implementation appearing in:
 *           -- "A Dual-Clock Multiple-Queue Shared Buffer", A. Psarras, M. Paschou, C. Nicopoulos, G. Dimitrakopoulos @ IEEE Transactions on Computers, 2017
 *              Check it out here: https://goo.gl/8f9gBy
 *
 *         For more information on the design & operation of Multiple Parallel Queues with Dynamic Shared Buffer Allocation, check:
 *           -- Chapter 6.3 "Buffer Sharing" @ "Microarchitecture of Network-on-Chip Routers", G. Dimitrakopoulos, A. Psarras, I. Seitanidis, 2014
 *              Check it out in google books: https://goo.gl/WNBVqH
 *           -- Chapter 3.2 "Buffer Memory" @ "Designing Network-on-Chip Architectures in the Nanoscale Era", J. Flich, D. Bertozzi (editors), 2010
 *              Check it out in google books: https://goo.gl/nqoMfQ
 *
 * @param DW        data width
 * @param D         total buffer depth
 * @param Q         number of queues
 * @param DBG_CHECK debug-only -- when asserted, rigorous checks are performed for correct operation
 * @param DBG_PRIV  debug-only -- indicates the number of private slots for each queue
 *                  effective only when checks are enabled (DBG_CHECK asserted)
 */

module shared_buff
#(
    parameter int   DW          = 16,
    parameter int   D           = 4,
    parameter int   Q           = 4,
    parameter logic DBG_CHECK   = 1'b0,
    parameter int   DBG_PRIV    = 1
)
(
    input  logic                clk,            // common read-write @posedge clock
    input  logic                arst_n,         // async reset -- active low
    // input channel
    output logic                ready_o,        // not with respect to RTT -- '1' when at least one buffer slot is available
    input  logic[DW-1:0]        push_data_i,    // input data to be pushed
    input  logic[Q-1:0]         push_sel_i,     // one-hot signal selecting the queue where the push will occur
    input  logic                push_i,         // one-bit signal confirms push
    // output channel
    output logic[Q-1:0]         valid_o,        // indicates whether Queue[q] has valid data (i.e. is not empty)
    output logic[Q-1:0][DW-1:0] pop_data_o,     // for temporary peek into the data (NOT for normal reading!) -- check *CAUTION* comment section below*
    input  logic[Q-1:0]         pop_sel_i,      // one-hot signal selecting the queue where the pop will occur
    output logic[DW-1:0]        data_o,         // output data of the queue selected for pop
    input  logic                pop_i           // one-bit signal confirms pop
);

// -- *Caution* ----------------------------------------------------------------------------------- //
// A word of caution on pop_data_o output signal:
//
// This signal outputs the front element of ALL Queues. What this output is *NOT* intended for:
//   + *NOT* intended for reading all DW bits out of it.
//   + *NOT* intended for reading the data of the popping queue (this will appear @ data_o)
//   
// The intention is to be able to "peek" on each queue's front element, possibly for reading the
// data header containing control info. E.g. in NoCs it could be the type of the flit
// (e.g. Head/Body/Tail), QoS attributes etc, which can be checked before the final pop is decided
//   
// Note that *** Q x DW-bit Q:1 MUXes *** generates the output. Therefore, if we only read a couple of
// bits out of them, the MUXes are drastically simplified in synthesis.
// If ALL bits are read out, expect a *serious* area overhead, especially as Q and DW increase.
// ------------------------------------------------------------------------------------------------ //

// Fixed Priority Arbiter: returns a one-hot vector where the '1' is found at
// the position where the first '1' is located in inp_vec (returns "0..00" if none)
function automatic logic[D-1:0] get_first_one(logic[D-1:0] inp_vec);
    for (int d=0; d<D; d++) begin
        if (inp_vec[d]) begin
            return 1 << d;
        end
    end
    return 0;
endfunction

// -- Local Parameters ---------------------------------------------------------------------------- //
localparam logic[D-1:0]    NULL_PTR = {D{1'b0}};

// -- Signal Definitions -------------------------------------------------------------------------- //
logic[D-1:0][DW-1:0]    mem;
logic[D-1:0][D-1:0]     l_list;
logic[D-1:0]            avail_slots;
logic[D-1:0]            slot_push, slot_pop;
logic                   any_avail;

logic[Q-1:0]            last_entry;
logic[Q-1:0][D-1:0]     pnt_linked_to_head, pnt_linked_to_tail;
logic[Q-1:0][D-1:0]     q_head_pnt;
logic[Q-1:0][D-1:0]     q_tail_pnt;

logic[D-1:0]            tail_pnt_of_push;
logic[D-1:0]            head_pnt_of_pop;
logic[D-1:0]            update_ll_pnt;
logic[D-1:0][D-1:0]     new_ll_pnt_val;

// -- Available slots Registers ------------------------------------------------------------------- //
// One-bit registers indicating memory availability (if avail[d] = 1, it's free)
always_ff @(posedge clk, negedge arst_n) begin: ff_avail
    if (!arst_n) begin
        avail_slots <= {D{1'b1}};
    end else begin
        for (int d=0; d<D; d++) begin
            if (push_i && slot_push[d]) begin
                avail_slots[d] <= 1'b0;
            end else if (pop_i && slot_pop[d]) begin
                avail_slots[d] <= 1'b1;
            end
        end
    end
end

// get current free slot using a Fixed Priority Arbiter (FPA)
assign slot_push = get_first_one(avail_slots);
assign any_avail = |avail_slots;

ast_avail_slots_if_push: assert property (@(posedge clk) disable iff(!arst_n)
    push_i |-> any_avail) else $fatal(1, "No free slots at shared buffer!");
ast_onehot_slot_push_if_push: assert property (@(posedge clk) disable iff(!arst_n)
    push_i |-> $onehot(slot_push)) else $fatal(1, "pushing to non-onehot slot!");

// -- Per Queue Pointers -------------------------------------------------------------------------- //
shared_buff_head_tail_pnts
#(
    .D (D),
    .Q (Q)
)
i_head_tail_pnts
(
    .clk                    (clk),
    .arst_n                 (rst),
    
    .push_i                 (push_i),
    .push_sel_i             (push_sel_i),
    .slot_push_i            (slot_push),
    
    .valid_o                (valid_o),
    .pop_sel_i              (pop_sel_i),
    .pop_i                  (pop_i),
    
    .q_head_pnt_o           (q_head_pnt),
    .q_tail_pnt_o           (q_tail_pnt),
    .pnt_linked_to_head_i   (pnt_linked_to_head),
    
    .last_entry_o           (last_entry)
);

// -- Linked List --------------------------------------------------------------------------------- //
// Calculate next-pointers, pointed by Head & Tail pointers of each Queue
for (genvar q=0; q<Q; q++) begin: gen_for_q_head_tail
    // MUX next-pointer list to get the pointer linked to Head
    and_or_mux
    #(
        .N  (D),
        .DW (D)
    )
    i_mux_pnt_of_head
    (
        .data_i (l_list),
        .sel_i  (q_head_pnt[q]),
        .data_o (pnt_linked_to_head[q])
    );
    
    // MUX next-pointer list to get the pointer linked to Tail
    and_or_mux
    #(
        .N  (D),
        .DW (D)
    )
    i_mux_pnt_of_tail
    (
        .data_i     (l_list),
        .sel_i      (q_tail_pnt[q]),
        .data_o     (pnt_linked_to_tail[q])
    );
end

assign slot_pop = head_pnt_of_pop;

// Get the Tail pointer of the queue selected for push
and_or_mux
#(
    .N  (Q),
    .DW (D)
)
i_mux_tail_pnt
(
    .data_i     (q_tail_pnt),
    .sel_i      (push_sel_i),
    .data_o     (tail_pnt_of_push)
);

// Get the Head pointer of the queue selected for pop
and_or_mux
#(
    .N  (Q),
    .DW (D)
)
i_mux_head_pnt
(
    .data_i     (q_head_pnt),
    .sel_i      (pop_sel_i),
    .data_o     (head_pnt_of_pop)
);

for (genvar d=0; d<D; d++) begin: gen_for_d
    assign update_ll_pnt[d] = (push_i & (tail_pnt_of_push[d] | slot_push[d])) | (pop_i & head_pnt_of_pop[d]);
    assign new_ll_pnt_val[d] = (push_i && tail_pnt_of_push[d]) ? slot_push :
                               (pop_i && head_pnt_of_pop[d])   ? NULL_PTR  :
                                                                 l_list[d];
end

// -- Linked List Registers -- //
always_ff @(posedge clk, negedge arst_n) begin: ff_linked_list
    if (!arst_n) begin
        l_list <= {D{NULL_PTR}};
    end else begin
        for (int d=0; d<D; d++) begin
            if (update_ll_pnt[d]) begin
                l_list[d] <= new_ll_pnt_val[d];
            end
        end
    end
end

// -- Data Ops ------------------------------------------------------------------------------------ //
// Data MUXes
for (genvar q=0; q<Q; q++) begin: gen_for_q_data
    and_or_mux
    #(
        .N  (D),
        .DW (DW)
    )
    mux_data_o
    (
        .data_i     (mem),
        .sel_i      (q_head_pnt[q]),
        .data_o     (pop_data_o[q])
    );
end

and_or_mux
#(
    .N  (D),
    .DW (DW)
)
i_mux_data_o
(
    .data_i     (mem),
    .sel_i      (head_pnt_of_pop),
    .data_o     (data_o)
);

// Data registers
always_ff @(posedge clk) begin: ff_data_mem
    if (push_i) begin
        for (int b=0; b<D; b++) begin
            if (slot_push[b]) begin
                mem[b] <= push_data_i;
            end
        end
    end
end

assign ready_o = any_avail;


// -- Self-checking Logic (assertions) ------------------------------------------------------------ //
// pragma synthesis_off
// pragma translate_off
if (DBG_CHECK) begin: dbg_gen_checks
    int DBG_status_cnt[Q-1:0];
    logic[Q-1:0] DBG_the_push, DBG_the_pop;

    for (genvar s=0; s<Q; s++) begin
        assign DBG_the_push[s] = push_i & push_sel_i[s];
        assign DBG_the_pop[s]  = pop_i & pop_sel_i[s];

        always_ff @(posedge clk, negedge arst_n) begin: DBG_cnt
            if (!arst_n) begin
                DBG_status_cnt[s] <= 0;
            end else begin
                if (DBG_the_push[s] && !DBG_the_pop[s]) begin
                    DBG_status_cnt[s] <= DBG_status_cnt[s] + 1;
                end else if (!DBG_the_push[s] && DBG_the_pop[s]) begin
                    DBG_status_cnt[s] <= DBG_status_cnt[s] - 1;
                end
            end
        end
    end

    initial begin
        assert (DBG_PRIV == 1) else $warning("Can only check 1 private per Sharer");
        forever begin
            @(posedge(clk));
            if (!rst) begin
                automatic int free_slots_cnt = 0;
                automatic int b = 0;
                automatic logic check_it = 1'b1;
                while (b < D && check_it) begin
                    if (avail_slots[b]) begin
                        free_slots_cnt++;
                        if (free_slots_cnt >= Q) begin
                            // enough slots to fit all sharers (no need to check)
                            check_it = 1'b0;
                        end
                    end
                    b++;
                end
                
                if (check_it) begin
                    // small number of slots (check if private slots are violated)
                    automatic int non_valids_cnt = 0;
                    for (int s=0; s<Q; s++) begin
                        if (!valid_o[s]) begin
                            non_valids_cnt++;
                        end
                    end
                    
                    assert (free_slots_cnt >= non_valids_cnt) else
                        $fatal(1, "Not enough free slots for all sharers! ->%0d<- of them have not occupied their slot and free_slots==%0d", non_valids_cnt, free_slots_cnt);
                end
            end
        end
    end
end
// pragma translate_on
// pragma synthesis_on

endmodule
