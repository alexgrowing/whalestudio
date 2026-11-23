import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductL2PositiveStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmplitudeConst

theorem normSq_inv_mul_sqrt (l d l' d' : ℝ) (hl : 0 < l) (hl' : 0 < l') (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    Complex.normSq ((((l / d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (l / d * d' / l') : ℝ) : ℂ)) = d / l * (d' / l') := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.normSq_ofReal]
  have hs : 0 ≤ l / d * d' / l' := by positivity
  have e : (l / d)⁻¹ * Real.sqrt (l / d * d' / l') * ((l / d)⁻¹ * Real.sqrt (l / d * d' / l')) =
      (l / d)⁻¹ * (l / d)⁻¹ * (Real.sqrt (l / d * d' / l') * Real.sqrt (l / d * d' / l')) := by ring
  rw [e, Real.mul_self_sqrt hs]
  rcases hd.eq_or_lt with h | h
  · subst h; simp
  · field_simp

theorem const_eq (P P' L L' K M H M' H' V V' : ℝ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hM' : 0 < M')
    (hH' : 0 < H') (hL : 0 < L) (hL' : 0 < L') (hV : L * V = M * H) (hV' : L' * V' = M' * H')
    (hP : 0 ≤ P) (hP' : 0 ≤ P') :
    P / L * (P' / L') = ((Real.sqrt (K * M * H / P * (K * M' * H' / P')))⁻¹ * K) ^ 2 * (V * V') := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_inv, inv_div, inv_div]
  have eV : V = M * H / L := by field_simp; linarith
  have eV' : V' = M' * H' / L' := by field_simp; linarith
  subst eV eV'
  field_simp

theorem prod_finrank_loc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ τ : D.what₂.Tau, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) = (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl

theorem prod_normSq_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  intro D X Y hF θ C hB u u' hθ hG
  have hK0 : 0 ≤ X.volK2 := ENNReal.toReal_nonneg
  have hv := hF.volPos u
  have hv' := hF.volPos u'
  have hN : 0 < X.volK2 * (X.muN u (Y.FN u)).toReal := hv.1
  have hN' : 0 < X.volK2 * (X.muN u' (Y.FN u')).toReal := hv'.1
  have hK : 0 < X.volK2 := pos_of_mul_pos_left hN ENNReal.toReal_nonneg
  have hNu : 0 < (X.muN u (Y.FN u)).toReal := pos_of_mul_pos_right hN hK0
  have hNu' : 0 < (X.muN u' (Y.FN u')).toReal := pos_of_mul_pos_right hN' hK0
  have hHu : 0 < (X.muH u Set.univ).toReal := hv.2
  have hHu' : 0 < (X.muH u' Set.univ).toReal := hv'.2
  obtain ⟨hl, hp⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u hθ hG hNu hHu
  obtain ⟨hl', hp'⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u' hθ hG hNu' hHu'
  have hτ : ∀ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) =
      (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) / (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal *
        ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) := by
    intro τ
    unfold sclOf cOf
    exact normSq_inv_mul_sqrt _ _ _ _ (hl τ) (hl' τ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_div_distrib, prod_finrank_loc, prod_finrank_loc]
  unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
  exact const_eq _ _ _ _ _ _ _ _ _ _ _ hK hNu hHu hNu' hHu' (Finset.prod_pos fun τ _ => hl τ)
    (Finset.prod_pos fun τ _ => hl' τ) hp hp' (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.AmplitudeConst
