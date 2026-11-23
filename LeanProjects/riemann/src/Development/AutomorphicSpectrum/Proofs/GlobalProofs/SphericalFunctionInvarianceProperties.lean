import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpenStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangularStatement

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.SphLaw

theorem diag_mul {F : Type} [Field F] {c : ℕ} {a b : Matrix (Fin c) (Fin c) F}
    (ha : a.BlockTriangular id) (hb : b.BlockTriangular id) (i : Fin c) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · simp

theorem diag_ne_zero {F : Type} [Field F] {c : ℕ} (b : GL (Fin c) F)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) (i : Fin c) :
    (b : Matrix (Fin c) (Fin c) F) i i ≠ 0 := by
  have h : (b : Matrix (Fin c) (Fin c) F).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_of_upperTriangular hb] at h
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)

noncomputable def wt {F : Type} [Field F] (nrm : AbsoluteValue F ℝ) {c : ℕ} (χ : Fin c → F → ℂ)
    (b : Matrix (Fin c) (Fin c) F) : ℂ :=
  ∏ i : Fin c, χ i (b i i) * ((nrm (b i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)

theorem chi_mul {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α) (i : Fin c)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : χ i (x * y) = χ i x * χ i y := by
  obtain ⟨e, he⟩ := hv x hx
  obtain ⟨e', he'⟩ := hv y hy
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    positivity
  have hxy : nrm (x * y) = (q : ℝ) ^ (-(e + e')) := by
    rw [map_mul, he, he', neg_add, zpow_add₀ hq0]
  rw [hU.2 i _ _ hxy, hU.2 i _ _ he, hU.2 i _ _ he', zpow_add₀ (hU.1 i)]

theorem wt_mul {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α)
    (a b : GL (Fin c) F) (ha : (a : Matrix (Fin c) (Fin c) F).BlockTriangular id)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) :
    wt nrm χ ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      wt nrm χ (a : Matrix (Fin c) (Fin c) F) * wt nrm χ (b : Matrix (Fin c) (Fin c) F) := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) i i =
      (a : Matrix (Fin c) (Fin c) F) i i * (b : Matrix (Fin c) (Fin c) F) i i := by
    rw [Units.val_mul]; exact diag_mul ha hb i
  rw [hd, chi_mul hq hv hU i (diag_ne_zero a ha i) (diag_ne_zero b hb i), map_mul,
    Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _)]
  push_cast
  ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → (∀ k ∈ GLint O c, φ k = 1) ∧ (∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g) ∧ (∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ g, φ (b * g) = φ b * φ g) ∧ Continuous φ ∧ ∀ φ', IsSphFn O nrm χ φ' → φ' = φ := by
  intro F _ _ _ _ O ϖ nrm q hLF c χ α hU φ hφ
  obtain ⟨hq, -, -, -, hv', -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) := fun x hx =>
    (hv' x hx).imp fun _ h => h.1
  have hIw := (GlobalTheory.T.iwasawa_decomposition_upperTriangular hLF) c
  have hKo : IsOpen (GLint O c : Set (GL (Fin c) F)) := (GlobalTheory.T.generalLinear_integral_compact_open hLF c).1
  have hval : ∀ (ψ : GL (Fin c) F → ℂ), IsSphFn O nrm χ ψ → ∀ b : GL (Fin c) F,
      (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
      ψ (b * k) = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun ψ hψ b hb k hk => hψ b hb k hk
  have hone : (1 : GL (Fin c) F) ∈ GLint O c := one_mem _
  have h1t : ((1 : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
    simpa using (Matrix.blockTriangular_one (b := (id : Fin c → Fin c)) (R := F))
  have hb1 : ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id →
      φ b = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun b hb => by
    simpa using hval φ hφ b hb 1 hone
  have hχ1 : ∀ i, χ i 1 = 1 := fun i => by
    have := hU.2 i 1 0 (by simp)
    simpa using this
  have hright : ∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g := by
    intro g k hk
    obtain ⟨b, hb, k', hk', rfl⟩ := hIw g
    rw [mul_assoc, hval φ hφ b hb _ ((GLint O c).mul_mem hk' hk), hval φ hφ b hb _ hk']
  refine ⟨?_, hright, ?_, ?_, ?_⟩
  · intro k hk
    have := hval φ hφ 1 h1t k hk
    rw [one_mul] at this
    rw [this]
    simp [wt, hχ1]
  · intro b hb g
    obtain ⟨b', hb', k, hk, rfl⟩ := hIw g
    have hbb : ((b * b' : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
      rw [Units.val_mul]; exact hb.mul hb'
    rw [← mul_assoc, hval φ hφ _ hbb k hk, hval φ hφ b' hb' k hk, hb1 b hb,
      wt_mul hq hv hU b b' hb hb']
  · refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (GLint O c : Set (GL (Fin c) F)),
      hKo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp [one_mem]
    · intro x hx
      have := hright g _ hx
      simpa using this
  · intro φ' hφ'
    funext g
    obtain ⟨b, hb, k, hk, rfl⟩ := hIw g
    rw [hval φ' hφ' b hb k hk, hval φ hφ b hb k hk]

end GlobalTheory.CompanionTheory.QL.SphLaw
