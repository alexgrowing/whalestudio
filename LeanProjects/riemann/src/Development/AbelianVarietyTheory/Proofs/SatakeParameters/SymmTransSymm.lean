import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeAtBadPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCouplingCosetInvariantFrameCongruentOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFramesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOnStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFramesStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTop

theorem inFr_trans {E : Type} [Field E] {n m : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (g g₁ : Sp E m ≃ₗ[E] Sp E m) (z : HomE E n m) :
    inFr f₁ g₁ z = (g₁.trans g.symm).symm.toLinearMap ∘ₗ inFr f g z ∘ₗ (f₁.trans f.symm).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  simp [inFr, LinearEquiv.trans_symm]

theorem symm_trans_symm {E : Type} [Field E] {n : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (y : Sp E n) :
    f₁.symm y = (f₁.trans f.symm).symm (f.symm y) := by
  simp [LinearEquiv.trans_symm]

theorem ptAway_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 + 1 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi hi1
  subst hi1
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  have hagS : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 :=
    fun v hv => (hag v hv).1
  have hagT : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun v hv => (hag v hv).2
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have e : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' =
      XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' := by
    intro q q'
    funext z
    unfold xiPt
    rw [dif_neg (by omega), if_neg (by omega)]
  rw [e, e]

  have hF := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS
  have hF' := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT

  have hcos : cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁ = cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p := by
    ext y
    simp only [cosetOf, Set.mem_setOf_eq]
    refine forall_congr' fun P => ?_
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      ((GlobalTheory.TwU.Model.sameCoset_equiv t.sel (t.tup μ) (t.cst μ) P).refl _)
    have key := GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm)
      (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) hc (hF P).1 (hF P).2 (hok.depthQ P) hb.1 hb.2 ((frsF t.sel (t.tup μ) p P).symm y)
    rw [← symm_trans_symm] at key
    exact key
  rw [hcos]
  funext z
  rw [XiTop_eq, XiTop_eq]
  congr 1
  ·
    unfold phiT
    congr 1
    refine propext (forall_congr' fun P => ?_)
    have hA := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hA' := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    have hB := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hB' := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    rw [hA, hA']
    refine forall_congr' fun w => imp_congr_right fun hw => and_congr_right fun hzw => ?_
    rw [hB w hw (hA ▸ hw), hB' _ hzw (hA' ▸ hzw)]
  ·
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p) (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
    have hrep : repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ⟨r, hr⟩
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P _ (hrep P)
    rw [inFr_trans (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p' P) (frsF t.sel (t.tup μ) p₁' P) z,
      symm_trans_symm (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P)]
    by_cases hG : P.1 ∈ t.Pr.vGs
    · exact GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.1 hG)
    · exact GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.2 hG)

end GlobalTheory.TwV.AwayTop

end
