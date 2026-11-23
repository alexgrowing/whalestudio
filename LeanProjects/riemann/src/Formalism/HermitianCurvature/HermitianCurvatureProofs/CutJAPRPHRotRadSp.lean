import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentRotationHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock

variable {k r : ℕ}

theorem star_exp_mul (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem cW_mem_UWb (θ : ℝ) : cW k r θ ∈ UWb k r := by
  refine emb_mem_UWb ?_
  show (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))ᴴ * Hb k *
    (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) = Hb k
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
    mul_comm, star_exp_mul, one_smul]

theorem cW_comm (θ : ℝ) {h : Q.Mx k r} (hh : h ∈ UWb k r) : cW k r θ * h = h * cW k r θ := by
  obtain ⟨μ, _, rfl⟩ := (UWb_iff h).1 hh
  unfold cW
  rw [← emb_mul, ← emb_mul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem cW_Glev (θ : ℝ) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) : cW k r θ * g ∈ Q.Glev k r (Fin.last r) := by
  obtain ⟨hc, hfix⟩ := cW_mem_UWb (k := k) (r := r) θ
  refine ⟨UH_mul hc hg.1, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).1, (hfix a).1]
  · rw [← Matrix.mulVec_mulVec, (hg.2 a ha).2, (hfix a).2]

theorem herm_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (cW k r θ *ᵥ v) z = Complex.exp ((θ : ℂ) * Complex.I) * herm (Hpk k r) v z := by
  have h1 : cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z) = z := by
    rw [Matrix.mulVec_smul, cW_mulVec _ hz, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  have h2 : star (Complex.exp (-((θ : ℂ) * Complex.I))) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  calc herm (Hpk k r) (cW k r θ *ᵥ v) z
      = herm (Hpk k r) (cW k r θ *ᵥ v) (cW k r θ *ᵥ (Complex.exp (-((θ : ℂ) * Complex.I)) • z)) := by rw [h1]
    _ = _ := by rw [herm_UH (cW_mem_UWb θ).1, herm_smul_right, h2]

theorem GGl_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) :
    Q.GGl k r z z' (cW k r θ * g) = Q.GGl k r z z' g := by
  unfold Q.GGl Q.zetaL
  rw [fvec_last, fvec_last, ← Matrix.mulVec_mulVec, herm_cW θ hz, map_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem domR_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ Q.DomR k r z z') : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z' :=
  ⟨hx.1, cW_Glev θ hx.2.1, by
    show 0 < Q.GGl k r z z' (cW k r θ * x.2)
    rw [GGl_cW θ hz]
    exact hx.2.2⟩

theorem domR_of_cW (θ : ℝ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : (x.1, cW k r θ * x.2) ∈ Q.DomR k r z z') : x ∈ Q.DomR k r z z' := by
  have h := domR_cW (-θ) hz z' hx
  have e : cW k r (-θ) * (cW k r θ * x.2) = x.2 := by
    rw [← Matrix.mul_assoc, cW_mul, neg_add_cancel, cW_zero, one_mul]
  change (x.1, cW k r (-θ) * (cW k r θ * x.2)) ∈ Q.DomR k r z z' at h
  rwa [e] at h

theorem rotation_radial_space_holds : RotRadSp := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' θ Φ hΦ
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 (x.1, cW k r θ * x.2) (fun h => hx (domR_of_cW θ hz z' h)), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs (x₀.1, cW k r θ * x₀.2) (domR_cW θ hz z' hx₀)
    have hL : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) :=
      contDiff_fst.prodMk (((LinearMap.mulLeft ℝ (cW k r θ)).toContinuousLinearMap.contDiff).comp contDiff_snd)
    exact ⟨(fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)) ⁻¹' U,
      F ∘ (fun x : (Fin r → ℂ) × Q.Mx k r => (x.1, cW k r θ * x.2)), hU.preimage hL.continuous, hxU,
      hF.comp hL.contDiffOn (fun x hx => hx), fun x hx hg => hΦF (x.1, cW k r θ * x.2) hx (cW_Glev θ hg)⟩
  · show Φ x.1 (cW k r θ * (h * x.2 * h')) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, cW_comm θ ⟨hh.1, hh.2.1⟩, Matrix.mul_assoc h]
    exact he (x.1, cW k r θ * x.2) (domR_cW θ hz z' hx) h hh h' hh'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
