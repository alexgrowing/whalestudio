import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChart
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frMap_along {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z : FrPt Xo c T, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r} {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}

theorem abs_fn_frBor_good (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') (i : Ix Dw) :
    |fn σ y' i| = cabs (t i : CAt σ) * |fn σ y i| := by
  obtain ⟨k, x, s, hx, hs⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
  have hc := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x) y y').2.2.1 s t hs hb
  rw [hp.1 σ hσ k x hx _ _ hc i, hp.1 σ hσ k x hx _ _ hs i, ← mul_assoc]
  congr 1
  exact norm_mul (show ℂ from (t i : CAt σ)) (show ℂ from (s i : CAt σ))

theorem abs_fn_frBor (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {σ : c.F →+* ℂ} {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') (i : Ix Dw) :
    |fn σ y' i| = cabs (t i : CAt σ) * |fn σ y i| := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact abs_fn_frBor_good hU hp hσ hb i
  · have hg : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    obtain ⟨z, hz⟩ := exists_frMap_along (conjAlg σ) y
    obtain ⟨z', hz'⟩ := exists_frMap_along (conjAlg σ) y'
    have hb' := frBorBC _ _ (conjAlg σ) t y y' z z' hb hz hz'
    have e := abs_fn_frBor_good hU hp hg hb' i
    rw [hp.2 σ y z hz i, hp.2 σ y' z' hz' i] at e
    rw [e]
    congr 1
    exact Complex.norm_conj (show ℂ from (t i : CAt σ))

def algOver {Z : Comp Xo c} (sg : c.F →+* ℂ) (P : Om Z →+* ℂ) (hP : sgOf P = sg) : Om Z →ₐ[c.F] CAt sg :=
  { P with commutes' := fun a => RingHom.congr_fun hP a }

theorem abs_fn_generic (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {Z : Comp Xo c} {z g : FrPt Xo c (Om Z)} {t : Ix Dw → (Om Z)ˣ} (hb : FrBor t z g)
    (sg : c.F →+* ℂ) (P : Om Z →+* ℂ) (hP : sgOf P = sg) {w : FrPt Xo c (CAt sg)}
    (hw : FrMap (algOver sg P hP) z w) {y : FrPt Xo c (CAt (sgOf P))} (hy : FrMap (PAlg P) g y) (i : Ix Dw) :
    |fn _ y i| = ‖P (t i : Om Z)‖ * |fn sg w i| := by
  subst hP
  have hb' := frBorBC _ _ (PAlg P) t z g w y hb hw hy
  exact abs_fn_frBor hU hp hb' i

end

theorem nrmAlong_of_fnPin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ [Fintype (Comp Xo c)], ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → NrmAlong fn yP ∧ ∀ (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)), STLoc h Dd N uL wR jc → FnTrdeg Xo c Dd → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → NrmContOff h fn yP Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hp _ h yP hyP
  have hne : FnNe Xo c fn := (GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm E H Dw l Xo c r U hU xR fn hx hp).1
  have main : NrmAlong fn yP := by
    intro Z sg G f _ _ X _ W Q hQ hQc
    obtain ⟨C, ψ, z, t, hz, hb⟩ := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h (Om Z) (genFr h Z)
    haveI := C.sm
    have hsg : ∀ x : W, sgOf (Q x) = sg := fun x => hQ x x.2
    choose w hw using fun x : W => exists_frMap_along (algOver sg (Q x) (hsg x)) z
    have hQ' : ∀ a, Continuous (fun x : W => Q x a) := fun a => continuousOn_iff_continuous_restrict.1 (hQc a)
    have hcont := GlobalTheory.FrameNorm.fn_continuousOn_smooth E H Dw l Xo c r U hU xR fn hx hp sg C.R C.y W Set.univ
      (fun x => (algOver sg (Q x) (hsg x)).comp ψ) w (fun a => (hQ' (ψ a)).continuousOn)
      (fun x _ => frMap_trans _ _ _ ψ _ C.y z (w x) hz (hw x))
    have hfn : ∀ i, Continuous (fun x : W => |fn _ (yP Z (Q x)) i|) := by
      intro i
      have e : (fun x : W => |fn _ (yP Z (Q x)) i|) = fun x : W => ‖Q x (t i : Om Z)‖ * |fn sg (w x) i| :=
        funext fun x => abs_fn_generic hU hp hb sg (Q x) (hsg x) (hw x) (hyP Z (Q x)) i
      rw [e]
      exact (hQ' _).norm.mul (continuousOn_univ.1 (hcont i))
    rw [continuousOn_iff_continuous_restrict]
    show Continuous (fun x : W => ‖Q x (f.coeff G)‖ * ∏ i, |fn _ (yP Z (Q x)) i| ^ (-exZ Dw G i))
    refine (hQ' _).norm.mul (continuous_finset_prod _ fun i _ => ?_)
    exact (hfn i).zpow₀ _ fun x => Or.inl (abs_ne_zero.2 (hne _ _ _))
  exact ⟨main, fun Dd N uL wR jc hst htr hw =>
    nrmContOff_of h fn yP Dd N uL wR jc hst main hne htr (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 hw⟩

end GlobalTheory.FrameNorm
