import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section GeneratorMatrix

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

private lemma le_genSub_self (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genSub E S := by
  exact le_sInf fun T hT => hT.1

private lemma genSub_stable (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) (a b : Fin n) {v : M}
    (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  exact Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)

private lemma genSub_le_of (E : Fin n → Fin n → Module.End ℂ M) (S T : Submodule ℂ M) (hST : S ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T := by
  exact sInf_le ⟨hST, hT⟩

private lemma single_smul_fin (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  funext j
  by_cases h : j = c
  · subst h
    simp
  · simp [h]

private lemma gen_generic (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) :
    f ∈ genSub T (Submodule.pi Set.univ fun _ => V) := by
  classical
  let G := genSub T (Submodule.pi Set.univ fun _ => V)
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ x, (Pi.single x m : Fin n → M) ∈ G}
      add_mem' := fun {m m'} hm hm' x => by rw [Pi.single_add]; exact G.add_mem (hm x) (hm' x)
      zero_mem' := fun x => by rw [Pi.single_zero]; exact G.zero_mem
      smul_mem' := fun r m hm x => by rw [single_smul_fin]; exact G.smul_mem r (hm x) }
  have hVS : V ≤ S := fun v hv x => le_genSub_self T _ (Submodule.mem_pi.2 fun j _ => by
    by_cases h : j = x
    · subst h
      simpa using hv
    · simp [h])
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm x
    have h2 : Submodule.span ℂ (Set.range fun y : Fin n => (Pi.single y m : Fin n → M)) ≤ G :=
      Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hm y)
    have h3 := G.add_mem (h2 (hT a b x m)) (genSub_stable T _ a b (hm x))
    simpa using h3
  have hle := genSub_le_of E V S hVS hSS
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle (hf c) c

private lemma tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  funext c'
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.add_apply]
  by_cases h2 : c' = a <;> by_cases h1 : c' = c <;> by_cases h3 : b = c <;>
    simp_all [Pi.single_apply, ite_apply]

private lemma tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  funext c'
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.sub_apply]
  by_cases h2 : c' = b <;> by_cases h1 : c' = c <;> by_cases h3 : a = c <;>
    simp_all [Pi.single_apply, ite_apply]

end GeneratorMatrix

theorem gen_statement (n : ℕ) : GenStatement n := by
  intro ε M _ _ E V _ _
  refine ⟨fun f hf => gen_generic E V (tensV E) (fun a b c m => ?_) f hf,
    fun f hf => gen_generic E V (tensVd E) (fun a b c m => ?_) f hf⟩
  · rw [tensV_single, sub_add_cancel_left]
    split_ifs
    · exact neg_mem (Submodule.subset_span ⟨a, rfl⟩)
    · simp
  · rw [tensVd_single, sub_sub_cancel]
    split_ifs
    · exact Submodule.subset_span ⟨b, rfl⟩
    · exact zero_mem _

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
