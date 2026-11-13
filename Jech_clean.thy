theory Jech_clean imports ZF begin
context 
  fixes S
  fixes W defines W_def : "W == {x ∈ S. x ∉ x}"
begin

lemma ex_1_2' : "¬ (Pow(S) ⊆ S)"
proof (rule notI)
  assume sub: "Pow(S) ⊆ S"
  have W_sub: "W ⊆ S"
  proof (rule subsetI)
    fix x
    assume "x ∈ W"
    then have "x ∈ {x ∈ S. x ∉ x}"
      unfolding W_def .
    then show "x ∈ S"
      by (rule CollectD1)
  qed
  have W_in_Pow: "W ∈ Pow(S)"
    using W_sub by (rule PowI)
  have W_in_S: "W ∈ S"
    using sub W_in_Pow by (rule subsetD)
  have not_in: "W ∉ W"
  proof (rule notI)
    assume in_W: "W ∈ W"
    then have "W ∈ {x ∈ S. x ∉ x}"
      unfolding W_def .
    then have not_W: "W ∉ W"
      by (rule CollectD2)
    show False
      using not_W in_W by (rule notE)
  qed
  have in_W: "W ∈ W"
  proof (unfold W_def, rule CollectI)
    show "W ∈ S" by (rule W_in_S)
  next
    show "W ∉ W" by (rule not_in)
  qed
  show False
    using not_in in_W by (rule notE)
qed

end
