/**
 * @info Head/Tail pointer management for multi-queue shared buffer
 *
 * @author Anastasios Psarras (a.psarras4225@gmail.com)
 *
 * @brief Head/Tail pointer management for multi-queue shared buffer
 *
 * @param D total depth of the shared buffer
 * @param Q number of queues
 */

module shared_buff_head_tail_pnts
#(
    parameter int D = 4,
    parameter int Q = 4
)
(
    input  logic                clk,
    input  logic                arst_n,
    // pushing
    input  logic                push_i,
    input  logic[Q-1:0]         push_sel_i,
    input  logic[D-1:0]         slot_push_i,
    // popping
    output logic[Q-1:0]         valid_o,
    input  logic[Q-1:0]         pop_sel_i,
    input  logic                pop_i,
    // Pointers
    output logic[Q-1:0][D-1:0]  q_head_pnt_o,
    output logic[Q-1:0][D-1:0]  q_tail_pnt_o,
    input  logic[Q-1:0][D-1:0]  pnt_linked_to_head_i,
    // Info
    output logic[Q-1:0]         last_entry_o
);

// -- Local Parameters ---------------------------------------------------------------------------- //
localparam logic[D-1:0]    NULL_PTR = {D{1'b0}};
// -- Signal Definitions -------------------------------------------------------------------------- //
logic[Q-1:0]            upd_head_pnt, upd_tail_pnt;
logic[Q-1:0][D-1:0]     next_head_pnt, next_tail_pnt;
logic[Q-1:0][D:0]       status_cnt;
logic[Q-1:0]            push_ultimate, pop_ultimate;

// -- Combinational Logic ------------------------------------------------------------------------- //
for (genvar q=0; q<Q; q++) begin: gen_for_q
    // one-hot signal of a *verified* push_i for each queue
    assign push_ultimate[q]    = push_i & push_sel_i[q];
    assign pop_ultimate[q]     = pop_i & pop_sel_i[q];
    
    // one-hot ring counter for tracking the number of elements in each queue
    always_ff @(posedge clk, negedge arst_n) begin: ff_cnt
        if (!arst_n) begin
            status_cnt[q] <= 1;
        end else begin
            if (push_ultimate[q] && !pop_ultimate[q]) begin
                // push without pop --> ++
                status_cnt[q] <= { status_cnt[q][D-1:0],1'b0 } ;
            end else if (!push_ultimate[q] && pop_ultimate[q]) begin
                // pop without push --> --
                status_cnt[q] <= {1'b0, status_cnt[q][D:1] };
            end
        end
    end
    // valid (i.e. not empty) means number of elements > 0
    assign valid_o[q]         = ~status_cnt[q][0];
    assign last_entry_o[q]    = q_tail_pnt_o[q] == q_head_pnt_o[q];

    // -- Head -------------------------------------------- //
    // update head pointer: [ALWAYS when popped] OR [when a push occurs on an empty Queue]
    // Specifically, Head's next value can be:
    //  - [Popping non-last] next_head_pnt
    //  - [Popping last]     NULL
    //  - [Pushing on Empty] slot_push_i
    assign upd_head_pnt[q] = pop_ultimate[q] | (push_ultimate[q] & ~valid_o[q]);
    assign next_head_pnt[q] = ( (pop_ultimate[q] && push_ultimate[q] && last_entry_o[q]) || (!valid_o[q] && push_ultimate[q]) ) ? slot_push_i                                     :
                              (pop_ultimate[q])                                                                                 ? pnt_linked_to_head_i[q] & {D{~last_entry_o[q]}} :
                                                                                                                                  q_head_pnt_o[q];
    // -- Tail -- //
    // update tail pointer: [ALWAYS when pushed] OR [a pop occurs on a one-entry queue]
    assign upd_tail_pnt[q] = (push_i & push_sel_i[q]) | (push_ultimate[q] & last_entry_o[q]);
    // Tail's next value can be:
    //  - [Push]         slot_push_i
    //  - [Popping last] NULL       (NOT obligatory! keep for error checking!)
    assign next_tail_pnt[q] = {D{(push_ultimate[q])}} & slot_push_i;
end

// -- Head/Tail Registers ------------------------------------------------------------------------- //
always_ff @(posedge clk, negedge arst_n) begin: ff_head_pnts
    if (!arst_n) begin
        q_head_pnt_o <= '{NULL_PTR};
    end else begin
        for (int q=0; q<Q; q++) begin
            if (upd_head_pnt[q]) begin
                q_head_pnt_o[q] <= next_head_pnt[q];
            end
        end
    end
end

always_ff @(posedge clk, negedge arst_n) begin: ff_tail_pnts
    if (!arst_n) begin
        q_tail_pnt_o <= '{NULL_PTR};
    end else begin
        for (int q=0; q<Q; q++) begin
            if (upd_tail_pnt[q]) begin
                q_tail_pnt_o[q] <= next_tail_pnt[q];
            end
        end
    end
end

endmodule
