/**
 * @info    Functional Verification Testbench for Multi-queue Shared Buffer
 *
 * @author  Anastasios Psarras (a.psarras4225@gmail.com)
 *
 * @license MIT license -- check license.md
 *
 * @brief   Formal Verification Testbench for Multi-queue Shared Buffer. Detailed info @ ./rtl/shared_buff.sv.
 * 
 */

module tb_fv
(
);

// ------------------------------------------------------------------------------------------------ //
localparam int   DW             = 8;
localparam int   D              = 4;
localparam int   Q              = 4;
localparam logic DBG_CHECK      = 1'b0;
localparam int   PRIVATE_SLOTS  = 0;
// ------------------------------------------------------------------------------------------------ //
logic                   clk;
logic                   arst_n;
logic                   ready;
logic[DW-1:0]           push_data;
logic[Q-1:0]            push_sel;
logic                   push;
logic[Q-1:0]            valid;
logic[Q-1:0][DW-1:0]    pop_data;
logic[Q-1:0]            pop_sel;
logic[DW-1:0]           data_out;
logic                   pop;
// ------------------------------------------------------------------------------------------------ //

shared_buff
#(
    .DW             (DW),
    .D              (D),
    .Q              (Q),
    .DBG_CHECK      (DBG_CHECK),
    .DBG_PRIV       (PRIVATE_SLOTS)
)
i_shared_buff
(
    .clk            (clk        ),
    .arst_n         (arst_n     ),
    .ready_o        (ready      ),
    .push_data_i    (push_data  ),
    .push_sel_i     (push_sel   ),
    .push_i         (push       ),
    .valid_o        (valid      ),
    .pop_data_o     (pop_data   ),
    .pop_sel_i      (pop_sel    ),
    .data_o         (data_out   ),
    .pop_i          (pop        )
);


tb_fv_shared_buffer
#(
    .DW             (DW),
    .D              (D),
    .Q              (Q),
    .PRIVATE_SLOTS  (PRIVATE_SLOTS)
)
i_shared_fv
(
    .clk            (clk        ),
    .arst_n         (arst_n     ),
    .ready          (ready      ),
    .push_data      (push_data  ),
    .push_sel       (push_sel   ),
    .push           (push       ),
    .valid          (valid      ),
    .pop_data       (pop_data   ),
    .pop_sel        (pop_sel    ),
    .data_out       (data_out   ),
    .pop            (pop        )
);

endmodule
