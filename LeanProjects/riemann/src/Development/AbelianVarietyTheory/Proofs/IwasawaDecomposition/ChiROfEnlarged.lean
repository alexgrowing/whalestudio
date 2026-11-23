import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsFormBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.chiR_of_enlarged : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      Formalism.IndefR.FWT.ChiR core' R'.toRealDat := by
  intro B B' f f' T T' w w' hP
  obtain ⟨P'⟩ := B'
  dsimp only at hP
  subst hP
  intro Z hX Wt z Z' hX' Wt' core' alg' halg hH hL Xg tr R' hR hmu ι hι
  obtain ⟨⟨⟨H', l', c', Dw', Xo'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := core'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hH
  dsimp only at h1 h2 h3 h12
  subst h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h12
  have hmu' := eq_of_heq hmu
  letI := z.alg
  have halg' : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) =
      @algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y := by
    intro y
    apply (w'.st Z').toD7.what₂.embLL.injective
    rw [hι]
    exact (z.alg_eq y).trans (halg y).symm
  have hE2 : (w'.st Z').toD7.what₂.embLL.comp (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg') =
      (w.st Z).toD7.what₂.embLL.comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
    ext y
    exact (halg y).trans (z.alg_eq y).symm
  have hE : (w'.st Z').toD7.embE = ι.comp (w.st Z).toD7.embE := by
    ext x
    apply (w'.st Z').toD7.what₂.embLL.injective
    have e1 := congrArg (fun g => g x) (w'.st Z').toD7.embE_φ₀
    have e2 := congrArg (fun g => g x) (w.st Z).toD7.embE_φ₀
    show _ = (w'.st Z').toD7.what₂.embLL (ι ((w.st Z).toD7.embE x))
    rw [hι]
    exact e1.trans e2.symm
  intro i σ' hg
  have hcomp : σ'.comp (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg') =
      (σ'.comp ι).comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
    ext y
    exact congrArg σ' (halg' y).symm
  have hlabE : labE σ' = labE (σ'.comp ι) := by
    funext τ
    unfold labE labLL
    rw [hE]
    rfl
  have hz := z.geo.fw.chiR i (σ'.comp ι) (hcomp ▸ hg)
  obtain ⟨a1, a2, a3, a4, a5⟩ := hz
  rw [hcomp]
  refine ⟨a1, a2, fun ρ => ?_, fun x hx => ?_, fun hσ => ?_⟩
  · have : lab σ' ρ = lab (σ'.comp ι) ρ := by
      unfold lab
      rw [hlabE]
      try rfl
    rw [this]
    exact a3 ρ
  · obtain ⟨y, hy1, hy2⟩ := a4 x hx
    refine ⟨y, ?_, hy2.trans (congrArg σ' (halg' y))⟩
    have hm : ((R'.toRealDat.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ((z.R.toRealDat.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) := by
      rw [hmu']
      rfl
    refine hm.trans (hy1.trans ?_)
    rw [← halg', hι]
  · have hσ' : (σ'.comp ι).comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) =
        (w.st Z).toD7.what₂.embLL.comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
      first
        | exact hσ.trans hE2
        | exact (hcomp.symm.trans hσ).trans hE2
    refine (a5 hσ').trans ?_
    rw [hmu']
