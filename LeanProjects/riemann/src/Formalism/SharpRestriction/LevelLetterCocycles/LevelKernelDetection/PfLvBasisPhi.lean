import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem lvBasis_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V) (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.actVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lvBasis_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := V) x) =
      φVB PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.mulVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lvBasis_mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.Dcris, sub_eq_zero]

theorem lvBasis_mem_DcrisL (ρ : Representation LL G V) (τ₀ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ₀ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ₀ c • x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.DcrisL, sub_eq_zero]

theorem lvBasis_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [lvBasis_mem_Dcris] at hx ⊢
  intro g
  rw [lvBasis_φ_act, hx g]

theorem lvBasis_φ_letter (ρ : Representation LL G V) {τ₀ τ₁ : K₀ →ₐ[Qp] LL}
    (h : τ₁.comp PD.σ = τ₀) {x : V ⊗[Qp] B} (hx : x ∈ DcrisL PD ρ τ₀) :
    φVB PD (LL := LL) (V := V) x ∈ DcrisL PD ρ τ₁ := by
  rw [lvBasis_mem_DcrisL] at hx ⊢
  refine ⟨lvBasis_φ_Dcris PD ρ hx.1, fun c => ?_⟩
  obtain ⟨c', rfl⟩ := PD.σ_bij.2 c
  rw [lvBasis_φ_mul, hx.2 c', map_smul, ← h, AlgHom.comp_apply]

theorem lvBasis_φ_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have hfun : ⇑(Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V)) = ⇑(LinearMap.lTensor V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.φVB]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hfun]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj

theorem lvBasis_φpow_inj (k : ℕ) : Function.Injective ((φVB PD (LL := LL) (V := V)) ^ k) := by
  first
  | (rw [Module.End.coe_pow]; exact (lvBasis_φ_inj PD).iterate k)
  | simpa using (lvBasis_φ_inj PD).iterate k

private theorem eigen_finset_eq_zero_of_injective_embeddings {ι : Type} [DecidableEq ι] (τ : ι → (K₀ →ₐ[Qp] LL))
    (hτ : Function.Injective τ) (s : Finset ι) : ∀ (x : ι → V ⊗[Qp] B),
    (∀ i ∈ s, ∀ c, Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i) →
    ∑ i ∈ s, x i = 0 → ∀ i ∈ s, x i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro x _ _ i hi; simp at hi
  | @insert j s hj ih =>
    intro x hx hs
    rw [Finset.sum_insert hj] at hs
    have h2 : ∑ i ∈ s, x i = -x j := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    have key : ∀ c, ∀ i ∈ s, (τ i c - τ j c) • x i = 0 := by
      intro c
      apply ih (fun i => (τ i c - τ j c) • x i)
      · intro i hi c'
        rw [map_smul, hx i (Finset.mem_insert_of_mem hi) c', smul_comm]
      · have h1 := congrArg (Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c) hs
        rw [map_add, map_sum, map_zero, hx j (Finset.mem_insert_self j s) c,
          Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_insert_of_mem hi) c)] at h1
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, ← Finset.smul_sum, h2, smul_neg, sub_neg_eq_add, add_comm]
        exact h1
    have hs0 : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have hij : τ i ≠ τ j := fun h => hj (by rw [← hτ h]; exact hi)
      obtain ⟨c, hc⟩ : ∃ c, τ i c ≠ τ j c := by
        by_contra hne
        push_neg at hne
        exact hij (AlgHom.ext hne)
      exact (smul_eq_zero.mp (key c i hi)).resolve_left (sub_ne_zero.mpr hc)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hs0, add_zero] at hs
      exact hs
    · exact hs0 i hi

theorem lvBasis_indep {ι : Type} [Fintype ι] (τ : ι → (K₀ →ₐ[Qp] LL)) (hτ : Function.Injective τ)
    (x : ι → V ⊗[Qp] B)
    (hx : ∀ i c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i)
    (hs : ∑ i, x i = 0) (i : ι) : x i = 0 := by
  classical
  exact eigen_finset_eq_zero_of_injective_embeddings τ hτ Finset.univ x (fun i _ c => hx i c) hs i (Finset.mem_univ i)

end Formalism.MainNotions.N.Ln03.Pf
