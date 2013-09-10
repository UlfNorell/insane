
bnfc_output = $(patsubst %,Syntax/%,Abs.hs ErrM.hs Layout.hs Print.hs Lex.x Par.y)
gen_hs_files = $(patsubst %,Syntax/%.hs,Par Lex Abs ErrM Layout Print)

unwanted = $(patsubst %,Syntax/%.hs,Skel Test)

src_files = $(filter-out $(unwanted),$(shell find . -name '*hs')) $(shell find . -name '*hs-boot')

ghc_flags = -fwarn-incomplete-patterns -Werror

default : tc

$(bnfc_output) : Syntax.cf
	-@rm $(bnfc_output)
	bnfc -d $<
	-@rm Syntax/Skel* Syntax/Doc* Syntax/Test*

%.hs : %.y
	happy $< -i

%.hs : %.x
	alex $<

tc : Main.hs $(gen_hs_files) $(src_files)
	ghc --make -o $@ $< $(ghc_flags)

