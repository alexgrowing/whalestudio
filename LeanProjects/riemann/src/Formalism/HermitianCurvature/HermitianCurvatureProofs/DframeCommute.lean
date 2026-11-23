import Formalism.HermitianCurvature.HermitianCurvatureProofs.GenCapRepIntertwine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section commute

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inWb_of_zero (hr : r = 0) (v : Fin (2 * r + k + 1) → ℂ) : inWb k r v := by
  subst hr; intro i hi; exfalso; have := i.isLt; omega

theorem prW_perp0 (hr : r = 0) (z v : Fin (2 * r + k + 1) → ℂ) (hvz : herm (Hpk k r) v z = 0) :
    D.prW k r z v = v := by
  rw [prW_eq, Wb_of_inWb (inWb_of_zero hr v), hvz, zero_div, zero_smul, sub_zero]

theorem herm_unit {g : B.Mat k r} (hg : g ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  conv_lhs => rw [show w = g *ᵥ (g⁻¹ *ᵥ w) by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]]
  exact herm_m0_mulVec_invariant g hg v _

theorem dframe_commute (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    (hdet : (Zhat k r S.z S.z' γ).det ≠ 0) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (m₀ * hB * m₀⁻¹) * γ * hB⁻¹ = γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  obtain ⟨⟨a1, ha1, h1⟩, ⟨a2, ha2, h2⟩, h3⟩ := hD
  have hz := S.z_mem
  have hz' := S.z'_mem
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have uγ := WeylGroupFacts.isUnit_of_uh hγ
  have uB := WeylGroupFacts.isUnit_of_uh hhB.1
  set ζ := (Zhat k r S.z S.z' γ).det with hζdef
  have hzν : herm (Hpk k r) S.z' ν' = 0 := herm_zν hνz
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; have := S.T'_pos; intro h; simp at h; linarith
  have hzz0' : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; have := S.T_pos; intro h; simp at h; linarith

  have hlast : ∀ b : Fin (r + 1), b = Fin.last r := fun b => Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
  have hfz : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)), fvec k r x b = x := by
    intro x b; rw [hlast b]; exact fvec_lastI x
  have hadj : ∀ a b : Fin (r + 1), (Zhat k r S.z S.z' γ).adjugate a b = 1 := by
    subst hr; intro a b
    rw [Matrix.adjugate_fin_one]; fin_cases a; fin_cases b; rfl
  have hcofR : D.cofR S γ = γ *ᵥ S.z' := by
    unfold D.cofR; subst hr; simp [hadj, hfz]
  have hcofL : D.cofL S γ = S.z := by
    unfold D.cofL; subst hr; simp [hadj, hfz]
  rw [hcofR, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h1
  rw [hcofL, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h2

  set c1 := herm (Hpk k r) (γ *ᵥ S.z') S.z / herm (Hpk k r) S.z S.z with hc1
  set c2 := herm (Hpk k r) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k r) S.z' S.z' with hc2
  have hγz' : γ *ᵥ S.z' = c1 • S.z + ((a1 : ℂ) * ζ) • (m₀ *ᵥ ν') := by rw [← h1]; abel
  have hγiz : γ⁻¹ *ᵥ S.z = c2 • S.z' + ((a2 : ℂ) * conj ζ) • ν' := by rw [← h2]; abel
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hmiz : m₀⁻¹ *ᵥ S.z = (μ : ℂ)⁻¹ • S.z' := by
    have : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
  set σ := m₀⁻¹ * γ with hσdef

  have hσz' : σ *ᵥ S.z' = (c1 * (μ : ℂ)⁻¹) • S.z' + ((a1 : ℂ) * ζ) • ν' := by
    rw [hσdef, ← Matrix.mulVec_mulVec, hγz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmiz,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec, smul_smul]
  have ha2ζ : (a2 : ℂ) * conj ζ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast ha2.ne') ?_
    simpa using hdet
  have hγν : γ *ᵥ ν' = ((a2 : ℂ) * conj ζ)⁻¹ • (S.z - c2 • (γ *ᵥ S.z')) := by
    have e : γ *ᵥ (γ⁻¹ *ᵥ S.z) = S.z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uγ, Matrix.one_mulVec]
    rw [hγiz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at e
    rw [← e]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha2ζ, one_smul]
  have hσν : σ *ᵥ ν' = (((a2 : ℂ) * conj ζ)⁻¹ * (μ : ℂ)⁻¹) • S.z' -
      (((a2 : ℂ) * conj ζ)⁻¹ * c2) • (σ *ᵥ S.z') := by
    simp only [hσdef, ← Matrix.mulVec_mulVec]
    rw [hγν, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hmiz, smul_sub, smul_smul, smul_smul]

  have hfix : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 → σ *ᵥ u = u := by
    intro u hu1 hu2
    have e1 : herm (Hpk k r) (γ *ᵥ u) S.z = 0 := by
      rw [herm_unit hγ, hγiz, B2x4.herm_add_right, B2x4.herm_smul_right, B2x4.herm_smul_right, hu1, hu2]
      simp
    have e2 : herm (Hpk k r) (γ *ᵥ u) (γ *ᵥ S.z') = 0 := by rw [herm_m0_mulVec_invariant γ hγ, hu1]
    have key := h3 (γ *ᵥ u) (fun a => ⟨by rw [hfz]; exact e1, by rw [hfz]; exact e2⟩)
    rw [prW_perp0 hr S.z _ e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec,
      prW_perp0 hr S.z' u hu1] at key
    rw [hσdef, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]

  have hBz' : hB *ᵥ S.z' = S.z' := hhB.2.2
  have hBperp : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 →
      herm (Hpk k r) (hB *ᵥ u) S.z' = 0 ∧ herm (Hpk k r) (hB *ᵥ u) ν' = 0 := by
    intro u h1u h2u
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hBz']
      rw [herm_m0_mulVec_invariant hB hhB.1, h1u]
    · conv_lhs => rw [← hBν]
      rw [herm_m0_mulVec_invariant hB hhB.1, h2u]

  have hcomm : σ * hB = hB * σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set α := herm (Hpk k r) v S.z' / herm (Hpk k r) S.z' S.z' with hα
    set β := herm (Hpk k r) v ν' with hβ
    set v0 := v - α • S.z' - β • ν' with hv0
    have hv0z : herm (Hpk k r) v0 S.z' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hνz, hα]
      field_simp; ring
    have hv0ν : herm (Hpk k r) v0 ν' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hzν, hνν, hβ]
      ring
    have hv : v = v0 + α • S.z' + β • ν' := by rw [hv0]; abel
    obtain ⟨hb1, hb2⟩ := hBperp v0 hv0z hv0ν
    rw [← Matrix.mulVec_mulVec v σ hB, ← Matrix.mulVec_mulVec v hB σ, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hBz', hBν, hfix v0 hv0z hv0ν,
      hfix (hB *ᵥ v0) hb1 hb2]
    rw [hσν, hσz']
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hBz', hBν]

  have hγσ : γ = m₀ * σ := by rw [hσdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
  rw [hγσ]
  calc m₀ * hB * m₀⁻¹ * (m₀ * σ) * hB⁻¹ = m₀ * hB * (m₀⁻¹ * m₀) * σ * hB⁻¹ := by simp only [Matrix.mul_assoc]
    _ = m₀ * (σ * hB) * hB⁻¹ := by rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.mul_one]

end commute

end Formalism.FourierDecayAlt.P.PBI
