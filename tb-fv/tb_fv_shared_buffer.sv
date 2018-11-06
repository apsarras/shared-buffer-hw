/**
 * @info   Formal Verification Testbench for Multi-queue Shared Buffer (./rtl/shared_buff.sv)
 *
 * @author Anastasios Psarras (a.psarras4225@gmail.com)
 *
 * @license MIT license -- check license.md
 *
 * @brief  Formal Verification Testbench for Multi-queue Shared Buffer. Detailed info @ ./rtl/shared_buff.sv.
 *         Note on Testbench approach:
 *           Instead of generating checks for ALL Q queues, we only check *one* random queue, 
 *           as specified by 'specimen_id' var. Since the 'specimen_id' can get any random value,
 *           the FV tool will check properties for *any random* queue, which is equivalent to checking them for *all queues*.
 *           The random variable, named 'specimen_id' is constrained using assumptions to only get legal values:
 *           can only get a value 0...Q-1, without unknown 'X' bits and should remain stable
 *
 *         --> Author got to know about this technique in DVCON Europe 2016 Tutorial:
 *             "Formal Verification: Too Good to Miss" by Jonathan Bromley and Jason Sprott (Verilab)
 *
 * @param DW            data width
 * @param D             total buffer depth
 * @param Q             number of queues
 * @param PRIVATE_SLOTS indicates the number of private slots for each queue
 */

module tb_fv_shared_buffer
#(
    parameter int   DW              = 16,
    parameter int   D               = 4,
    parameter int   Q               = 4,
    parameter int   PRIVATE_SLOTS   = 1
)
(
    input  logic                clk,
    input  logic                arst_n,
    // input channel
    input  logic                ready,
    input  logic[DW-1:0]        push_data,
    input  logic[Q-1:0]         push_sel,
    input  logic                push,
    // output channel
    input  logic[Q-1:0]         valid,
    input  logic[Q-1:0][DW-1:0] pop_data,
    input  logic[Q-1:0]         pop_sel,
    input  logic[DW-1:0]        data_out,
    input  logic                pop
);

default clocking @(posedge clk); endclocking
default disable iff(!arst_n);

// ------------------------------------------------------------------------------------------------ //
localparam int MAX_SLOTS = D - PRIVATE_SLOTS;
// -- Assume -------------------------------------------------------------------------------------- //
int inflight_total_cnt;
int inflight_total_cnt_next;
int inflight_specimen_cnt;
int inflight_specimen_head;
int inflight_specimen_tail;
int specimen_id;

logic push_specimen;
logic pop_specimen;
logic valid_specimen;

logic[DW-1:0] data_inflight[MAX_SLOTS-1:0];

// -- RTL-equivalent logic (golden model) --------------------------------------------------------- //
// In-flight data counter registers & update logic
assign inflight_total_cnt_next = ( push & ~pop) ? inflight_total_cnt + 1 :
                                 (~push &  pop) ? inflight_total_cnt - 1 :
                                                  inflight_total_cnt;
always_ff @(posedge clk, negedge arst_n) begin
    if (!arst_n) begin
        inflight_total_cnt <= 0;
    end else begin
        inflight_total_cnt <= inflight_total_cnt_next;
    end
end

assign push_specimen  = push & push_sel[specimen_id];
assign pop_specimen   = pop & pop_sel[specimen_id];
assign valid_specimen = valid[specimen_id];

// Typical FIFO operation for a single queue -- no need to keep track of ALL the queues -- check @brief
// We keep track of the stored data & their expected order of appearence at the output by:
//  a) Keeping track of the number of elements stored in queue (inflight_specimen_cnt)
//  b) Storing data in an array (data_inflight)
//  c) And track data in the array using head/tail pointers (inflight_specimen_head, inflight_specimen_tail)
always_ff @(posedge clk, negedge arst_n) begin
    if (!arst_n) begin
        inflight_specimen_cnt <= 0;
        inflight_specimen_head <= 0;
        inflight_specimen_tail <= 0;
    end else begin
        inflight_specimen_cnt <= inflight_specimen_cnt + push_specimen - pop_specimen;
        
        // push
        if (push_specimen) begin
            if (inflight_specimen_tail == (MAX_SLOTS-1)) begin
                inflight_specimen_tail <= 0;
            end else begin
                inflight_specimen_tail <= inflight_specimen_tail + 1;
            end
            data_inflight[inflight_specimen_tail] <= push_data;
        end
        
        // pop
        if (pop_specimen) begin
            if (inflight_specimen_head == (MAX_SLOTS-1)) begin
                inflight_specimen_head <= 0;
            end else begin
                inflight_specimen_head <= inflight_specimen_head + 1;
            end
        end
    end
end

// -- Assumptions --------------------------------------------------------------------------------- //
// Maximum stored data words do not exceed the buffer's capacity
asm_inflight_total_in_limits : assume property (inflight_total_cnt inside {[0:D-1]});
asm_inflight_total_next_in_limits : assume property (inflight_total_cnt_next inside {[0:D-1]});
// specimen_id constraints: should remain stable, no X's, within legal range (0...Q-1)
asm_specimen_stable: assume property ($stable(specimen_id));
asm_specimen_in_limits: assume property (specimen_id inside {[0:Q-1]});
asm_specimen_no_x: assume property (!$isunknown(specimen_id));

asm_push_no_x: assume property (!$isunknown(push));
asm_push_data_no_x: assume property (push |-> !$isunknown(push_data)); // data CAN contain X's when NOT pushing
asm_push_sel_no_x: assume property (push |-> $onehot(push_sel));
asm_inflight_lt_max_if_push: assume property (push |-> inflight_specimen_cnt < MAX_SLOTS); // illegal to push on a full queue

asm_pop_no_x: assume property (!$isunknown(pop));
asm_pop_sel_no_x_if_pop: assume property (pop |-> !$isunknown(pop_sel));
asm_pop_sel_onehot_if_pop: assume property (pop |-> $onehot(pop_sel));
asm_anyvalid_if_pop: assume property (pop |-> |valid); // popping is only allowed when valid (i.e. not empty)
asm_pop_sel_valid_if_pop: assume property (pop |-> |(pop_sel & valid)); // popping only allowed on a non-empty queue

// avoid trivial FV scenario of never actually pushing or popping anything
asm_push_eventually: assume property (s_eventually(push_specimen));
asm_pop_eventually: assume property (s_eventually(pop_specimen));

// -- Assert -------------------------------------------------------------------------------------- //
// in case of a pop -> popped data must match last pushed data
ast_data_eq_last_data_if_pop: assert property (pop_specimen |-> data_out == data_inflight[inflight_specimen_head]);
// when non-empty, make sure that pop_data outputs last pushed data (a pop is NOT required here! The output is combinational)
ast_data_from_all_eq_last: assert property (valid_specimen |-> pop_data[specimen_id] == data_inflight[inflight_specimen_head]);
// when non-empty, there must be something in flight (and backwards!)
ast_inflight_gt_0_if_valid: assert property (valid_specimen |-> inflight_specimen_cnt > 0);
ast_valid_if_inflight_gt_0: assert property (inflight_specimen_cnt > 0 |-> valid_specimen);
// when empty, there must be nothing in flight (and backwards!)
ast_inflight_eq_0_if_not_valid: assert property (!valid_specimen |-> inflight_specimen_cnt == 0);
ast_not_valid_if_inflight_eq_0: assert property (inflight_specimen_cnt == 0 |-> !valid_specimen);
// whenever a push occurs, the queue must appear non-empty in the FOLLOWING cycle
ast_valid_if_prev_push: assert property (push_specimen |-> ##1 valid_specimen);


endmodule
