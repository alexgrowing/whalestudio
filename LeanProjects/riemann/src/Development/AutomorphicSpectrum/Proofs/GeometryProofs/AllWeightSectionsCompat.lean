import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Bridge

open AlgebraicGeometry CategoryTheory Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem secZ_eq_allWt (a : WZ E) : secZ Xo c a = GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) := by
  ext f
  exact ⟨mem_allWt_of_secZ, mem_secZ_of_allWt⟩

theorem exZ_pair (a : WZ E) : Formalism.L2.Pj.exZ Dw (a, (0 : ℤ)) = GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a := by
  funext i
  cases i <;> rfl

theorem modelWt_pair {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) :
    GlobalTheory.AllWt.modelWt U (a, (0 : ℤ)) = laZ U a := by
  funext k τ j
  simp [GlobalTheory.AllWt.modelWt, laZ]

theorem cuspZ_eq_allWt {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : WZ E) :
    cuspZ Xo c U a = GlobalTheory.AllWt.cuspW Xo c U (a, (0 : ℤ)) := by
  unfold cuspZ GlobalTheory.AllWt.cuspW
  simp only [exZ_pair, modelWt_pair, secZ_eq_allWt]

theorem ptF_congr {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y'.x = y.x) :
    GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
  apply pullback.hom_ext
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, h]
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    GlobalTheory.AllWt.ptF z = spMap φ.toRingHom ≫ GlobalTheory.AllWt.ptF y := by
  apply pullback.hom_ext
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, Category.assoc, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext fun x => (φ.commutes x).symm)

theorem comp_eq_of_mem {Z Z' : Comp Xo c} {p : Xo.XF c} (hp : p ∈ (Z : Set (Xo.XF c)))
    (hp' : p ∈ (Z' : Set (Xo.XF c))) : Z' = Z := by
  have hs0 := Xo.smooth
  have hs1 : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hs : Smooth (strK (Xo := Xo) (c := c)) := inferInstance
  obtain ⟨-, hN, -⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F (Xo.XF c) strK hs
  have hN' : GlobalTheory.IsNormalScheme (Xo.XF c) := by first | exact hN | exact GlobalTheory.IsNormalScheme.of_pred hN
  have ho : IsOpen (Z : Set (Xo.XF c)) := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents Z.2
  have hg := (Z'.2.1 : IsIrreducible (Z' : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z'.2)
  have h1 : (Z'.2.1 : IsIrreducible (Z' : Set (Xo.XF c))).genericPoint ∈ (Z : Set (Xo.XF c)) :=
    (hg.mem_open_set_iff ho).2 ⟨p, hp', hp⟩
  have hle : (Z' : Set (Xo.XF c)) ⊆ Z := (hg.mem_closed_set_iff (isClosed_of_mem_irreducibleComponents _ Z.2)).1 h1
  exact Subtype.ext (hle.antisymm (Z'.2.2 Z.2.1 hle))

theorem evR_chart {h : GenFrEx Xo c} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c 0) (C : GlobalTheory.Reg.FChart h) {v : c.F}
    (hv : evC h C.Z f = algebraMap c.F (Om C.Z) v) {L : Type} [Field L] [Algebra c.F L] {ψ : C.R →ₐ[c.F] L}
    {z w : FrPt Xo c L} {t : Ix Dw → Lˣ} (hz : FrMap ψ C.y z) (hb : FrBor t z w) :
    evR Xo c f w = algebraMap c.F L v := by
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
  have h1 : evR Xo c f C.yg = algebraMap c.F (Om C.Z) v := by
    rw [GlobalTheory.FlagTan.evR_frBor hf C.bor]
    have : evR Xo c f (genFr h C.Z) = algebraMap c.F (Om C.Z) v := hv
    rw [this]
    simp
  have h2 : χ (f q y₀) = algebraMap c.F C.R v := by
    rw [GlobalTheory.FlagTan.evR_eq hf.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
    exact Subtype.ext h1
  rw [GlobalTheory.FlagTan.evR_frBor hf hb, GlobalTheory.FlagTan.evR_eq hf.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz),
    AlgHom.comp_apply, h2]
  simp

theorem liesOn_chart {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) {L : Type} [Field L] [Algebra c.F L]
    {ψ : C.R →ₐ[c.F] L} {z w : FrPt Xo c L} {t : Ix Dw → Lˣ} (hz : FrMap ψ C.y z) (hb : FrBor t z w) :
    GlobalTheory.AllWt.LiesOn C.Z w := by
  have key : ∀ s' : Sp C.R, GlobalTheory.AllWt.ptF C.y s' ∈ (C.Z : Set (Xo.XF c)) := by
    intro s'
    let η : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
    have e1 : GlobalTheory.AllWt.ptF C.yg = spMap C.R.val.toRingHom ≫ GlobalTheory.AllWt.ptF C.y := ptF_frMap C.gen
    have e2 : GlobalTheory.AllWt.ptF C.y (spMap C.R.val.toRingHom η) = Formalism.L2.Pj.genPt C.Z := by
      rw [← Scheme.Hom.comp_apply, ← e1, ptF_congr C.bor.1]
      exact GlobalTheory.AllWt.ptF_genFr h C.Z η
    have hsp : (spMap C.R.val.toRingHom η) ⤳ s' := by
      refine (PrimeSpectrum.le_iff_specializes (spMap C.R.val.toRingHom η : PrimeSpectrum C.R) (s' : PrimeSpectrum C.R)).1 ?_
      intro a ha
      have : (a : Om C.Z) = 0 := ha
      have : a = 0 := Subtype.ext this
      rw [this]
      exact Ideal.zero_mem _
    have hmem : Formalism.L2.Pj.genPt C.Z ∈ (C.Z : Set (Xo.XF c)) :=
      ((C.Z.2.1 : IsIrreducible (C.Z : Set (Xo.XF c))).isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ C.Z.2)).mem
    have h3 := hsp.map (GlobalTheory.AllWt.ptF C.y).continuous
    rw [e2] at h3
    exact h3.mem_closed (isClosed_of_mem_irreducibleComponents _ C.Z.2) hmem
  intro s
  rw [ptF_congr hb.1, ptF_frMap hz, Scheme.Hom.comp_apply]
  exact key _

theorem indicator_at_field {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hC : CompLaws U h e) {L : Type} [Field L] [Algebra c.F L] (w : FrPt Xo c L) :
    ∃ Z₀ : Comp Xo c, GlobalTheory.AllWt.LiesOn Z₀ w ∧ evR Xo c (e Z₀) w = 1 ∧ ∀ Z, Z ≠ Z₀ → evR Xo c (e Z) w = 0 := by
  have hz : ∀ Z, e Z ∈ GlobalTheory.AllWt.secZ Xo c 0 := fun Z => by
    have := hC.e_sec Z
    rwa [← GlobalTheory.AllWt.secZ_nat, show (fun i => (ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 i : ℤ)) = 0 by
      funext i; cases i <;> rfl] at this
  obtain ⟨-, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h L w
  refine ⟨C.Z, liesOn_chart C h1 h2, ?_, fun Z hZ => ?_⟩
  · have := evR_chart (v := 1) (hz C.Z) C (by rw [(hC.e_val C.Z).1, map_one]) h1 h2
    rwa [map_one] at this
  · have := evR_chart (v := 0) (hz Z) C (by rw [(hC.e_val Z).2 C.Z (Ne.symm hZ), map_zero]) h1 h2
    rwa [map_zero] at this

theorem indicator_mem_suppOn {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hC : CompLaws U h e) (Z : Comp Xo c) : e Z ∈ GlobalTheory.AllWt.suppOn Z := by
  intro S _ _ y hy
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hnat := (hC.e_sec Z).1
  by_cases hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  swap
  · unfold evR evalAt
    rw [dif_neg hT]
  obtain ⟨q, χ, y₀, hy₀⟩ := hT
  have hid := (sections_generic_indicators E H Dw l Xo c r U h e hC).2.2.2.1 Z
  have hu : IsIdempotentElem (χ (e Z q y₀)) := by
    have : e Z q y₀ * e Z q y₀ = e Z q y₀ := congrFun (congrFun hid q) y₀
    show χ _ * χ _ = χ _
    rw [← map_mul, this]
  rw [GlobalTheory.FlagTan.evR_eq hnat hy₀]
  have hnil : IsNilpotent (χ (e Z q y₀)) := by
    rw [nilpotent_iff_mem_prime]
    intro P hP
    let φ : S →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F S P.ResidueField
    obtain ⟨w, hw⟩ := hL.bc _ _ φ y
    obtain ⟨Z₀, h1, -, h3⟩ := indicator_at_field hC w
    have hne : Z ≠ Z₀ := by
      rintro rfl
      let s₀ : Sp P.ResidueField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum P.ResidueField)
      have := h1 s₀
      rw [ptF_frMap hw, Scheme.Hom.comp_apply] at this
      exact hy _ this
    have h4 := h3 Z hne
    rw [GlobalTheory.FlagTan.evR_eq hnat (frMap_trans _ _ _ _ _ _ _ _ hy₀ hw), AlgHom.comp_apply] at h4
    exact Ideal.algebraMap_residueField_eq_zero.1 h4
  obtain ⟨n, hn⟩ := hnil
  have := hu.pow_succ_eq n
  rw [pow_succ, hn, zero_mul] at this
  exact this.symm

theorem cuspOn_eq_allWt {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hC : CompLaws U h e) (a : WZ E) (Z : Comp Xo c) :
    cuspOn U h a Z = GlobalTheory.AllWt.cuspOn U Z (a, (0 : ℤ)) := by
  have hT := hC.genT
  have hz : e Z ∈ secZ Xo c (0 : WZ E) := by
    have h1 := hC.e_sec Z
    rw [← GlobalTheory.CompanionTheory.Ar.Rec.secZ_nat] at h1
    have h2 : (fun x => ((((0 : (E →+* ℂ) × ℕ → ℕ)) x : ℕ) : ℤ)) = (0 : WZ E) := by
      funext x
      simp
    rwa [h2] at h1
  ext f
  constructor
  · intro hf
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    rw [cuspZ_eq_allWt] at h1
    refine Submodule.mem_inf.2 ⟨h1, ?_⟩
    have hfs : f ∈ secZ Xo c a := (Submodule.mem_inf.1 (cuspZ_eq_allWt U a ▸ h1)).1
    have hzero : evC h Z (0 : Rul Xo c) = 0 := by
      rw [← evL_apply, map_zero]
    have hoff : ∀ Z', Z' ≠ Z → evC h Z' f = 0 := fun Z' hne =>
      Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 h2 Z') hne
    have hef : f = f * e Z := by
      refine sub_eq_zero.1 (secZ_eq_zero_of_generic h (a := a) (Submodule.sub_mem _ hfs ?_) fun Y => ?_)
      · have := secZ_mul hfs hz
        rwa [add_zero] at this
      · rw [← evL_apply, map_sub, evL_apply, evL_apply, evC_mul_of_test hT, sub_eq_zero]
        by_cases hY : Y = Z
        · subst hY
          rw [(hC.e_val Y).1, mul_one]
        · rw [hoff Y hY, zero_mul]
    rw [hef]
    exact GlobalTheory.AllWt.mul_mem_suppOn f (indicator_mem_suppOn hC Z)
  · intro hf
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨(cuspZ_eq_allWt U a).symm ▸ h1, ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun Z' => Submodule.mem_iInf _ |>.2 fun hne => ?_
    exact GlobalTheory.AllWt.evC_eq_zero h hne h2

theorem rdU_indicator {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hC : CompLaws U h e) (Z : Comp Xo c) {σ : c.F →+* ℂ} (k : (U σ).Comp)
    {x : Frame ((U σ).X k).Ψ r} (hx : x ∈ ((U σ).X k).dom) :
    (GlobalTheory.AllWt.LiesOn Z ((U σ).un k ⟨x, hx⟩) → rdU (U σ) (e Z) k x = 1) ∧
      (¬ GlobalTheory.AllWt.LiesOn Z ((U σ).un k ⟨x, hx⟩) → rdU (U σ) (e Z) k x = 0) := by
  have hval : rdU (U σ) (e Z) k x = toC (evR Xo c (e Z) ((U σ).un k ⟨x, hx⟩)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hx, dif_pos]
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨Z₀, h1, h2, h3⟩ := indicator_at_field hC ((U σ).un k ⟨x, hx⟩)
  let s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (CAt σ))
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have : Z₀ = Z := comp_eq_of_mem (hl s₀) (h1 s₀)
    subst this
    rw [hval, h2]
    rfl
  · have : Z ≠ Z₀ := fun hh => hl (hh ▸ h1)
    rw [hval, h3 Z this]
    rfl

theorem rdU_indicator_const {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hC : CompLaws U h e) (Z : Comp Xo c) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (k : (U σ).Comp) {x y : Frame ((U σ).X k).Ψ r} (hx : x ∈ ((U σ).X k).dom) (hy : y ∈ ((U σ).X k).dom) :
    rdU (U σ) (e Z) k x = rdU (U σ) (e Z) k y := by
  have hsec := (hC.unf σ hσ).2.2.2.2.1 0 0 ⟨fun _ _ _ _ => le_rfl, Even.zero⟩ (e Z) (hC.e_sec Z) k
  have hconn : IsPreconnected ((U σ).X k).dom :=
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r ((U σ).X k)).isPreconnected
  have hmaps : Set.MapsTo (rdU (U σ) (e Z) k) ((U σ).X k).dom ({0, 1} : Set ℂ) := fun z hz => by
    by_cases hl : GlobalTheory.AllWt.LiesOn Z ((U σ).un k ⟨z, hz⟩)
    · exact Or.inr ((rdU_indicator hC Z k hz).1 hl)
    · exact Or.inl ((rdU_indicator hC Z k hz).2 hl)
  exact hconn.constant_of_mapsTo (Set.toFinite ({0, 1} : Set ℂ)).isDiscrete hsec.1.continuousOn hmaps hx hy

theorem framesOn_iff_over {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hC : CompLaws U h e) (Z : Comp Xo c) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (k : (U σ).Comp) {y : Frame ((U σ).X k).Ψ r} (hy : y ∈ ((U σ).X k).dom) :
    (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z ↔ Over (U σ) (e Z) k := by
  constructor
  · rintro ⟨h', hl⟩ x hx
    rw [rdU_indicator_const hC Z hσ k hx hy]
    exact (rdU_indicator hC Z k hy).1 hl
  · intro ho
    refine ⟨hy, ?_⟩
    by_contra hl
    have := (rdU_indicator hC Z k hy).2 hl
    rw [ho y hy] at this
    exact one_ne_zero this

end Bridge

theorem bridge_allWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (Z : Comp Xo c), secZ Xo c a = GlobalTheory.AllWt.secZ Xo c (exZ Dw a) ∧ cuspZ Xo c U a = GlobalTheory.AllWt.cuspW Xo c U (a, 0) ∧ cuspOn U h a Z = GlobalTheory.AllWt.cuspOn U Z (a, 0) ∧ (∀ f : GlobalTheory.AllWt.cuspOn U Z (a, 0), f ∈ GlobalTheory.AllWt.latOn U Z (a, 0) ↔ (f : Rul Xo c) ∈ latOn U h a Z) ∧ ∀ σ, GoodEmb c σ → ∀ k, ∀ y ∈ ((U σ).X k).dom, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z ↔ Over (U σ) (e Z) k := by
  intro E _ _ _ H Dw l Xo c r U h e hC a Z
  have hcusp := cuspOn_eq_allWt hC a Z
  refine ⟨secZ_eq_allWt a, cuspZ_eq_allWt U a, hcusp, fun f => ?_, fun σ hσ k y hy => framesOn_iff_over hC Z hσ k hy⟩
  have key := mem_latIn (K := c.F) (R := Rul Xo c) (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet
    (f : Rul Xo c)
  constructor
  · intro hf
    exact key.2 ⟨hcusp.ge f.2, GlobalTheory.AllWt.mem_supLat.1 hf⟩
  · intro hf
    exact GlobalTheory.AllWt.mem_supLat.2 (key.1 hf).2

end GlobalTheory.CompanionTheory.Ar.Rec
