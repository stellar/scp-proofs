proof: network.ivy node.ivy sort.ivy assertion.ivy proof.ivy
	ivy_check trace=true proof.ivy

format:
	git ls-tree -r HEAD --name-only | xargs sed -i "s/, /, /g; s/, \s\+/, /g; s/[ \t]*$$//"
