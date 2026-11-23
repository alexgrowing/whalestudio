import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

variable {j j' : ℕ}

theorem sg_fb {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks a b c d)) :
    aᴴ * a - cᴴ * c = 1 ∧ aᴴ * b - cᴴ * d = 0 ∧ bᴴ * b - dᴴ * d = -1 := by
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 h
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h2
  · simpa [sub_eq_add_neg] using h4

theorem unit_of_rel {a : Matrix (Fin j) (Fin j) ℂ} {c : Matrix (Fin j') (Fin j) ℂ}
    (h : aᴴ * a - cᴴ * c = 1) : IsUnit a.det := by
  have e : aᴴ * a = 1 + cᴴ * c := by rw [← h]; abel
  have pd : (aᴴ * a).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)
  have hu : IsUnit (aᴴ * a).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  unfold sgI
  rw [fromBlocks_multiply]
  simp

theorem IsSgU.mul {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) : IsSgU (u * v) := by
  unfold IsSgU at *
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * sgI j j' * (u * v) = vᴴ * (uᴴ * sgI j j' * u) * v := by
        simp only [Matrix.mul_assoc]
    _ = sgI j j' := by rw [hu, hv]

theorem IsSgU.det_unit {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) : IsUnit u.det := by
  have : (sgI j j' * uᴴ * sgI j j') * u = 1 := by
    have e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u) := by
      simp only [Matrix.mul_assoc]
    rw [e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]
  exact Matrix.isUnit_det_of_left_inverse this

theorem unitary_iff_fb {p : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {r : Matrix (Fin j') (Fin j) ℂ} {s : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks p b r s)) :
    (fromBlocks p b r s)ᴴ * fromBlocks p b r s = 1 ↔ r = 0 := by
  obtain ⟨h1, h2, h3⟩ := sg_fb h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  constructor
  · intro e
    obtain ⟨e1, -, -, -⟩ := fromBlocks_inj.1 e
    have hz : (2 : ℂ) • (rᴴ * r) = 0 := by
      have : rᴴ * r + rᴴ * r = 0 := by
        have := sub_eq_zero.2 (e1.trans h1.symm)
        rw [← this]; abel
      rw [two_smul]; exact this
    have hz' : rᴴ * r = 0 := (smul_eq_zero.1 hz).resolve_left two_ne_zero
    exact conjTranspose_mul_self_eq_zero.1 hz'
  · rintro rfl
    simp only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢
    have hp : p * pᴴ = 1 := mul_eq_one_comm.1 h1
    have hb : b = 0 := by
      have : p * (pᴴ * b) = b := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      rw [← this, h2, Matrix.mul_zero]
    subst hb
    simp only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3
    simp [h1, h3]

theorem single_fb {a p : Matrix (Fin j) (Fin j) ℂ} {b e : Matrix (Fin j) (Fin j') ℂ}
    {c r : Matrix (Fin j') (Fin j) ℂ} {d s : Matrix (Fin j') (Fin j') ℂ}
    (hu : IsSgU (fromBlocks a b c d)) (hv : IsSgU (fromBlocks p e r s)) :
    c * a⁻¹ = (c * p + d * r) * (a * p + b * r)⁻¹ ↔ r = 0 := by
  have ha : IsUnit a.det := unit_of_rel (sg_fb hu).1
  have hp : IsUnit p.det := unit_of_rel (sg_fb hv).1
  have hw : IsUnit (a * p + b * r).det := by
    have := IsSgU.mul hu hv
    rw [fromBlocks_multiply] at this
    exact unit_of_rel (sg_fb this).1
  constructor
  · intro h
    have h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r := by
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]
    have hs : (d - c * a⁻¹ * b) * r = 0 := by
      have e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]
      rw [e1] at h'
      have : c * a⁻¹ * b * r = d * r := add_left_cancel h'
      rw [Matrix.sub_mul, this, sub_self]
    have hS : IsUnit (d - c * a⁻¹ * b).det := by
      have hd := IsSgU.det_unit hu
      letI := Matrix.invertibleOfIsUnitDet a ha
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hd
      exact isUnit_of_mul_isUnit_right hd
    have : (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r :=
      Matrix.nonsing_inv_mul_cancel_left _ _ hS
    rw [← this, hs, Matrix.mul_zero]
  · rintro rfl
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]

theorem single {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) :
    u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = (u * v).toBlocks₂₁ * (u * v).toBlocks₁₁⁻¹ ↔ vᴴ * v = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  obtain ⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩
  rw [unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]

theorem ballPt_inj {Ψ : Type} {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    {W W' : Ψ → Matrix (Fin j') (Fin j) ℂ} (h : ballPt q W = ballPt q W') : W = W' := by
  funext τ
  ext i' i
  have := congrFun h (q (τ, i, i'))
  simpa [ballPt] using this

theorem moebBall_zero {Ψ : Type} [Fintype Ψ] {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) :
    moebBall q w 0 = ballPt q fun τ => (w τ).toBlocks₂₁ * (w τ).toBlocks₁₁⁻¹ := by
  have hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  unfold moebBall
  congr 1
  funext τ
  rw [hb τ]
  simp [moebW]

theorem moebBall_zero_iff : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  intro Ψ _ j j' n q u v hu hv
  rw [moebBall_zero, moebBall_zero]
  constructor
  · intro h τ
    exact (single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)
  · intro h
    congr 1
    funext τ
    exact (single (hu τ) (hv τ)).2 (h τ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
