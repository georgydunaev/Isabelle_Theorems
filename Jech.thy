theory Jech imports ZF begin
context 
  fixes S
  fixes W defines W_def : "W == {x∈S. x∉x}"
begin

lemma ex_1_2' : " ¬ ( Pow(S) ⊆ S )"
  apply (rule notI)
  apply (rule case_split[where P="W∈W"])
  apply (rule notE[where P="W∈W"])
    apply (rule CollectD2[where A=S])
    apply (fold W_def)
    apply assumption
   apply assumption
  apply (rule notE[where P="W∈W"])
   apply assumption
  apply (unfold W_def)
   apply (rule CollectI)
   apply (fold W_def)
   prefer 2
  apply assumption
  (*subgoal*)
   apply (unfold subset_def)
   apply (unfold Ball_def)
    apply (rule mp[where P="W∈Pow(S)"])
     apply (rule spec[where x=W])
     apply assumption
    apply (rule PowI)
    apply (unfold W_def)
    apply (unfold subset_def)
    apply (unfold Ball_def)
    apply (rule allI)
    apply (rule impI)
    apply (rule CollectD1)
    apply assumption
  done
end 
