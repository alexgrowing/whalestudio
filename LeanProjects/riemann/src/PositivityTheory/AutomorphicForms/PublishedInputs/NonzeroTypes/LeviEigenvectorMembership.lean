import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.LeviEigenvectorMembership

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

theorem mem_left_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {g : GL (Fin n) k} (hg : g ∈ G.JSet) (h : GL (Fin n) k) : g * h ∈ G.JSet ↔ h ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hh => hmul g hg h hh⟩
  have := hmul _ (hinv g hg) _ hgh
  simpa [← mul_assoc] using this

theorem mem_right_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {h : GL (Fin n) k} (hh : h ∈ G.JSet) (g : GL (Fin n) k) : g * h ∈ G.JSet ↔ g ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hg => hmul g hg h hh⟩
  have := hmul _ hgh _ (hinv h hh)
  simpa [mul_assoc] using this

theorem levi_eigenvector_of_conditions (hcb : CompactConductorBasicProp (k := k)) (hccB : CompactConductorBoundProp G) (hΔU : ModulusOnUnitsProp G) (hΔM : ModulusMultiplicativeProp G)
    (hJone : JacquetOneProp G) (hJmul : JacquetMultiplicativeProp G) (hJinv : JacquetInverseProp G) (hlM : LambdaMultiplicativeProp G)
    (hlB : LambdaBasicProp G) (hKC : CompactOpenKernelProp G) :
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧ ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet →
      Rreg (k := k) (n := n) j G.v0 = G.lam j • G.v0 := by
  have hmul := hJmul hcb hccB
  have hinv := hJinv hcb hccB
  have hlam := hlM hcb hΔU hΔM hccB
  obtain ⟨hl1, -, hlK⟩ := hlB hccB
  have hKJ : KC k n G.lev ⊆ G.JSet := (hKC hccB G.lev).2.2.2.2 le_rfl

  have hright : ∀ (g j : ↥(KO k (Fin n))), (j : GL (Fin n) k) ∈ G.JSet →
      G.v0 (g * j) = G.lam j * G.v0 g := by
    intro g j hj
    simp only [Grp.v0, Subgroup.coe_mul, mem_right_iff G hmul hinv hj]
    split_ifs with hg
    · rw [hlam _ hg _ hj, mul_comm]
    · simp
  refine ⟨⟨fun p hp g => ?_, fun g u hu => ?_⟩, ?_, fun j hj => ?_⟩
  · have hpJ : (p : GL (Fin n) k) ∈ G.JSet := hJone.2 hp
    simp only [Grp.v0, Subgroup.coe_mul, mem_left_iff G hmul hinv hpJ]
    split_ifs with hg
    · rw [hlam _ hpJ _ hg]
    · simp
  · rw [hright g u (hKJ hu), hlK _ hu, one_mul]
  · intro h0
    have := congrFun h0 1
    simp only [Grp.v0, OneMemClass.coe_one, if_pos hJone.1, hl1, Pi.zero_apply] at this
    exact one_ne_zero this
  · funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hright g j hj]
    rfl

end UpperTheory.TNZ.Grp.LeviEigenvectorMembership

namespace UpperTheory.TNZ.Grp

theorem leviEigenvector_holds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : NonzeroLeviEigenvectorExists G :=
  fun hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC =>
    LeviEigenvectorMembership.levi_eigenvector_of_conditions G hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC

end UpperTheory.TNZ.Grp
