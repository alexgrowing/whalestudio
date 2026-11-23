import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExtStatement
open NumberField

namespace GlobalTheory
open Formalism.IndefR.Arith

theorem mall_eq_span_rat (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (hK : A.IsKsForm) (hρ : ∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) (hc : ∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) : A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  apply le_antisymm
  swap
  · rw [Submodule.span_le]
    rintro y ⟨hy1, hy2⟩
    exact ⟨Submodule.subset_span hy1, hy2⟩
  obtain ⟨n, b, hbK, _, hspK, hliL, hspL⟩ := hK

  set ψ : (Fin n → LL) →ₗ[LL] WL := Fintype.linearCombination LL b with hψdef
  have hψ : ∀ y, ψ y = ∑ k, y k • b k := fun y => by simp [hψdef, Fintype.linearCombination_apply]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hψ] at hy
    funext i
    exact Fintype.linearIndependent_iff.1 hliL y hy i
  set e : (Fin n → Ks) → (Fin n → LL) := fun x i => algebraMap Ks LL (x i) with he
  have hψe : ∀ x, ψ (e x) = ∑ k, x k • b k := fun x => by
    rw [hψ]; simp [he, algebraMap_smul]

  have hex : ∀ (p : J0) (k : Fin n), ∃ c : Fin n → Ks, ∑ i, c i • b i = A.ρ p (b k) := by
    intro p k
    have : A.ρ p (b k) ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact hρ p _ (hbK k)
    exact (Submodule.mem_span_range_iff_exists_fun Ks).1 this
  choose cc hcc using hex
  let Am : J0 → Matrix (Fin n) (Fin n) Ks := fun p => Matrix.of fun i k => cc p k i
  choose lamK hlamK using hc
  have hρψ : ∀ (p : J0) y, A.ρ p (ψ y) = ψ (((Am p).map (algebraMap Ks LL)).mulVec y) := by
    intro p y
    rw [hψ, hψ, map_sum]
    simp only [LinearMap.map_smul, ← hcc, Finset.smul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Am, Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact smul_comm _ _ _
  have hmemT : ∀ y, ψ y ∈ A.typeP J0 lam0 ↔ ∀ p : J0, ((Am p).map (algebraMap Ks LL)).mulVec y = algebraMap Ks LL (lamK p) • y := by
    intro y
    rw [FormsL.mem_typeP]
    refine forall_congr' fun p => ?_
    rw [hρψ, hlamK p, ← LinearMap.map_smul]
    exact hψinj.eq_iff
  let Wt : Submodule Ks (Fin n → Ks) :=
    { carrier := {x | ∀ p, (Am p).mulVec x = lamK p • x}
      zero_mem' := fun p => by simp
      add_mem' := fun {x y} hx hy p => by simp [Matrix.mulVec_add, hx p, hy p, smul_add]
      smul_mem' := fun a x hx p => by
        show (Am p).mulVec (a • x) = lamK p • (a • x)
        rw [Matrix.mulVec_smul, hx p, smul_smul, smul_smul, mul_comm] }
  let φ : (Fin n → Ks) →ₗ[𝓞 Ks] WL := (Fintype.linearCombination Ks b).restrictScalars (𝓞 Ks)
  let M : Submodule (𝓞 Ks) (Fin n → Ks) := A.MK.comap φ
  have hMmem : ∀ x, x ∈ M ↔ ∑ k, x k • b k ∈ A.MK := fun x => by simp [M, φ, Fintype.linearCombination_apply]
  have hI1 := (GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational Ks LL n J0 Am lamK 0).1
  have hI2 := GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext Ks LL n M Wt
  let ψO : (Fin n → LL) →ₗ[𝓞 LL] WL := ψ.restrictScalars (𝓞 LL)
  rintro y ⟨hy1, hy2⟩
  have hle : Submodule.span (𝓞 LL) (A.MK : Set WL) ≤ (Submodule.span (𝓞 LL) (e '' (M : Set _))).map ψO := by
    rw [Submodule.span_le]
    intro m hm
    have hmK : m ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact A.MK_le_WK hm
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).1 hmK
    refine ⟨e x, Submodule.subset_span ⟨x, (hMmem x).2 (hx ▸ hm), rfl⟩, ?_⟩
    show ψ (e x) = m
    rw [hψe, hx]
  obtain ⟨z, hz, rfl⟩ := hle hy1
  have hzW : z ∈ Submodule.span LL (e '' (Wt : Set _)) := (hI1 z).1 ((hmemT z).1 hy2)
  have hz2 : z ∈ Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) := by
    rw [← hI2]; exact ⟨hz, hzW⟩
  have hle2 : Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) ≤ (Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0}).comap ψO := by
    rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxM, hxW⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · show ψ (e x) ∈ A.MK
      rw [hψe]; exact (hMmem x).1 hxM
    · show ψ (e x) ∈ A.typeP J0 lam0
      rw [hmemT]; exact (hI1 (e x)).2 (Submodule.subset_span ⟨x, hxW, rfl⟩)
  exact hle2 hz2

end GlobalTheory
