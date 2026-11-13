theory Example1 imports Jech begin

context
  fixes S
  fixes W defines W_def : "W == {x ∈ S. x ∉ x}"
begin

lemma example_lemma : "¬ (Pow(S) ⊆ S)"
  by (rule ex_1_2')

end
