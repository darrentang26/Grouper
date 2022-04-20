	.section	__TEXT,__text,regular,pure_instructions
	.build_version macos, 12, 0
	.globl	_main                           ## -- Begin function main
	.p2align	4, 0x90
_main:                                  ## @main
	.cfi_startproc
## %bb.0:                               ## %entry
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$24, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movl	$16, %edi
	callq	_malloc
	movq	%rax, %r14
	movl	$4, %edi
	callq	_malloc
	movl	$2, (%rax)
	movq	%rax, (%r14)
	movq	$0, 8(%r14)
	movl	$16, %edi
	callq	_malloc
	movq	%rax, %rbx
	movl	$4, %edi
	callq	_malloc
	movl	$1, (%rax)
	movq	%rax, (%rbx)
	movq	%r14, 8(%rbx)
	movq	%rbx, 16(%rsp)
	movq	(%rbx), %rax
	movq	%rax, 8(%rsp)
	movq	(%rax), %rax
	movl	(%rax), %eax
	movl	%eax, 4(%rsp)
	leaq	L___unnamed_1(%rip), %rdi
	xorl	%eax, %eax
	callq	_printf
	xorl	%eax, %eax
	addq	$24, %rsp
	popq	%rbx
	popq	%r14
	retq
	.cfi_endproc
                                        ## -- End function
	.section	__TEXT,__cstring,cstring_literals
L___unnamed_1:                          ## @0
	.asciz	"1"

.subsections_via_symbols
