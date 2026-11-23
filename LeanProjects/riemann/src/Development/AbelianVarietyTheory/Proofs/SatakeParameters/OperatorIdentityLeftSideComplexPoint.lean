import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePolyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocksStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPointStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem leftSide_odd_grp {M : Type} [CommGroup M] (u e d d' e' : M) (n : ℕ) (c s w : ℤ) (hu : u = e' * d'⁻¹) (he : e * e = 1) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  subst hu
  apply Additive.ofMul.injective
  have he' : Additive.ofMul e + Additive.ofMul e = 0 := by rw [← ofMul_mul, he]; rfl
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv]
  linear_combination (norm := module) (c - w) • he'

theorem leftSide_odd (u e d d' e' : ℂ) (n : ℕ) (c s w : ℤ) (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e * e = 1) (he' : e' * e' = 1)
    (hu : u = e' * d'⁻¹) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  have he0 : e ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he0' : e' ≠ 0 := left_ne_zero_of_mul_eq_one he'
  have h := leftSide_odd_grp (Units.mk0 e' he0' * (Units.mk0 d' hd')⁻¹) (Units.mk0 e he0) (Units.mk0 d hd) (Units.mk0 d' hd')
    (Units.mk0 e' he0') n c s w rfl (Units.ext (by simpa using he))
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  subst hu
  exact h2

theorem leftSide_sgRev_sq (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem leftSide_det_zT_odd {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos h]
  have := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) ((f τ)⁻¹).transpose
  rw [show (⇑(Fin.revPerm : Equiv.Perm (Fin n))) = Fin.rev from rfl] at this
  rw [this, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem leftSide_zT_even {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : ¬ IsOddPos (pos.symm τ).2) :
    zT X D pos f τ = f τ := by
  unfold zT; rw [if_neg h]

end GlobalTheory.TwV.DelA
end

namespace GlobalTheory.TwV.DelA

theorem leftSide_at_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG d f' hf' hdf
  have hodd := GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν Q hQ Gc G hR hG
  have hsub := GlobalTheory.T.substituted_value_at_complex_point_oddBlocks X D pos Kc ι j hN Gc G hG hodd d f' hf' hdf
  have hnum := GlobalTheory.T.numerator_div_denominator_at_complex_point X D pos Kc ι j hN d f' hf' hdf
  have hex := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j
  have hnn := (GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν).2.2.2.2
  have hR' := hR ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩
  have hR2 := (ev1_eq_prod_det_pow_mul_valZ X D pos j (rkS X D hN) Gc ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩).symm.trans hR'
  clear hR'
  simp only at hR2
  rw [map_mul, hsub, hnum]
  have gen : ∀ (x y z : ℂ) (E : Kc), ι x * (E * ι y) * ι z = E * ι (x * y * z) := by
    intro x y z E; simp only [map_mul]; ring
  rw [gen]
  congr 2
  have hW : (∏ τ, (dfr X D hN d f' τ).det ^ (-(wT X D pos j τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdf τ)
  have key : ∀ A V B P' S W' q Pj Wf : ℂ, Wf ≠ 0 → A * B * P' * Wf = S * W' * Pj → Pj * V = Wf * q →
      A * V * B * P' = S * W' * q := by
    intro A V B P' S W' q Pj Wf hWf hK hP
    apply mul_right_cancel₀ hWf
    linear_combination V * hK + S * W' * hP
  refine key _ _ _ _ _ _ _ _ _ hW ?_ hR2
  unfold sgO
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨h1, h2⟩ := hex τ
  by_cases ho : IsOddPos (pos.symm τ).2
  · simp only [if_pos ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_det_zT_odd X D pos f' τ ho, leftSide_det_zT_odd X D pos (dfr X D hN d f') τ ho]
    exact leftSide_odd _ _ _ _ _ _ _ _ _ (hdf τ) (hf' τ) (leftSide_sgRev_sq _) (leftSide_sgRev_sq _) rfl
  · simp only [if_neg ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_zT_even X D pos f' τ ho, leftSide_zT_even X D pos (dfr X D hN d f') τ ho, ← zpow_natCast,
      Int.toNat_of_nonneg (hnn τ), zpow_sub₀ (hdf τ)]
    simp only [zpow_neg]
    ring

end GlobalTheory.TwV.DelA
