import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.UpNonzero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Doubling (io hgt flat zetaA ZetaConvA IsMaj dblSp Khat HasIwasawa degPS)
open GlobalTheory.FinZeta (projV embV Kv Gv IsLocKer VacFin bddAut)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction (ofFr ipTh ptAt actSrc actTgt IsJoint UnitHighest kfin alS alT NodeGap)
open GlobalTheory.AdelicScalar (l2)
open scoped InnerProductSpace GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.Ipf.Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

def offK (V : HSp D) (Sb : Finset (FPl D)) : Set (GA D V) := {g | ∀ v ∉ Sb, projV V v g ∈ Kv V v}

def infJ (V : HSp D) (J : Subgroup (GA D V)) : Set (GA D V) := {g | ∃ k ∈ J, g * k⁻¹ ∈ GinfC V}

def grH (V : HSp D) (a : GL (Fin V.rank) (AE D)) (g : GA D V) : ℝ := (hgt V a (io V (g, 1)) : ℝ)

def onG (V : HSp D) (Φ : GA D (dblSp V) → ℂ) : GA D V → ℂ := fun g => Φ (io V (g, 1))

def IsBdSec (V : HSp D) (a : GL (Fin V.rank) (AE D)) (s₀ : ℝ) (Φ : GA D (dblSp V) → ℂ) : Prop :=
  Continuous (onG V Φ) ∧ ∃ C : ℝ, ∀ g, ‖onG V Φ g‖ ≤ C * grH V a g ^ (s₀ + (V.rank : ℝ) / 2)

def coefSrc {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓧 : Set (WO S T))
    (f : WO S T → ℂ) : GA D S → ℂ := fun g => l2 μ 𝓧 (om (g, 1) f) f

def coefAut (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (F₁ F₂ : GA D V → ℂ) : GA D V → ℂ :=
  fun g => l2 ν 𝓕 (rTr V g F₁) F₂

def IsKerOff (V : HSp D) (N : ℕ) (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (Sb : Finset (FPl D)) (c : GA D V → ℂ) : Prop :=
  ∀ v ∉ Sb, ∃ φ : Gv V v → ℂ, IsLocKer V N z v φ ∧
    ∀ g, projV V v g = 1 → ∀ x : Gv V v, c (g * embV V v x) = φ x * c g

structure IsLevelS (V : HSp D) (Sb : Finset (FPl D)) (J : Subgroup (GA D V)) : Prop where
  fin : J ≤ GfC V
  compact : IsCompact (J : Set (GA D V))
  isOpen : IsOpen (infJ V J)
  split : ∀ g ∈ GfC V, g ∈ J ↔ (∃ k ∈ J, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v

def IsLevelKer (V : HSp D) (Sb : Finset (FPl D)) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (c : GA D V → ℂ) : Prop :=
  (∀ k ∈ J, ∀ g, c (g * k) = χ k * c g) ∧ ∀ g ∈ offK V Sb, g ∉ infJ V J → c g = 0

section Real

variable {V : HSp D} {PS : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V PS)

def atPl (τ : D.what₂.Tau) (x : Formalism.REAL.UJ (M.ε τ)) : GA D V := atTau θ V τ (ofFr M τ (Formalism.MainNotions.S.umat x))

def realPt (x : ∀ τ, Formalism.REAL.UJ (M.ε τ)) : GA D V := ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => atPl θ M τ (x τ)).prod

def zReal (a : GL (Fin V.rank) (AE D)) (τ : D.what₂.Tau) (m : Measure (Formalism.REAL.UJ (M.ε τ))) (c : Formalism.REAL.UJ (M.ε τ) → ℂ)
    (v w : M.H τ) (s₀ s : ℂ) : ℂ :=
  ∫ x, c x * (grH V a (atPl θ M τ x) : ℂ) ^ (s - s₀) * star (Formalism.MainNotions.S.coefOn (M.σ τ) v w x) ∂m

end Real

structure IsStep (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {PS PT : D.what₂.Tau → SPar} (M : DSModel S PS) (M' : DSModel T PT)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Sb : Finset (FPl D)) (f₀ fF : WO S T → ℂ) : Prop where
  weil : IsWeilDatumO ψ S T χS χT om
  inf : IsInfFam θ
  parS : PS = parB (Ptw D) k
  parT : PT = parB (Ptw D) (k + 1)
  expo : ∀ τ, HasInfExp D χS τ (alS D k τ) ∧ HasInfExp D χT τ (alT D k τ)
  rank : T.rank = S.rank + D.R.t
  noQ : LS.Q = ∅
  places : ∀ v, v ∈ Sb ↔ ∃ PP ∈ LS.Pg, PP.under (𝓞 D.host.F) = v
  frameS : ∃ N : ℕ, Lev.IsBaseFrame S βS ΛS N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  frameT : ∃ N : ℕ, Lev.IsBaseFrame T βT ΛT N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  vec : IsStepVecOf ψ θ S T (cart M) (cart M') ΛS ΛT βS βT LS χj ∅ (fun _ => 1) f₀ fF
  unr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → GlobalTheory.LFun.UnrAt χS w ∧ GlobalTheory.LFun.UnrAt χT w
  tame : ∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP χS (χj PP) (-1) ∧ Formalism.IndefR.Fin.TameAt e PP χT (χj PP) (-1)

def fockVec (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {PS PT : D.what₂.Tau → SPar} (M : DSModel S PS)
    (M' : DSModel T PT) (fF : WO S T → ℂ) (P : D.what₂.Tau → MvPolynomial (Fin T.rank × Fin S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (cart M) (cart M') (onb M) (onb M') fF
    (∏ τ, MvPolynomial.rename (fun y : Fin T.rank × Fin S.rank => ((τ, y) : FVar D T.rank S.rank)) (P τ))

def fockAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {PS PT : D.what₂.Tau → SPar} (M : DSModel S PS)
    (M' : DSModel T PT) (fF : WO S T → ℂ) (τ : D.what₂.Tau) : MvPolynomial (Fin T.rank × Fin S.rank) ℂ → (WO S T → ℂ) :=
  ptAt ψ θ S T τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) fF

def IsJointAll (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {PS PT : D.what₂.Tau → SPar}
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (M : DSModel S PS) (M' : DSModel T PT) (fF : WO S T → ℂ)
    (P : D.what₂.Tau → MvPolynomial (Fin T.rank × Fin S.rank) ℂ) : Prop :=
  ∀ τ, IsJoint M' τ (actTgt θ om τ) (fockAt ψ θ M M' fF τ) M (actSrc θ om τ) (P τ)

def IsTopVec {V : HSp D} {PS : D.what₂.Tau → SPar} (M : DSModel V PS) (v : M.Vec) : Prop :=
  ∀ τ, ∃ x : kfin M τ, UnitHighest M τ x ∧ (x : M.H τ) = (v τ : M.H τ)

def EulerOff (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
  ∀ (N : ℕ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ N →
  ∀ Sb : Finset (FPl D), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → GlobalTheory.LFun.UnrAt χ w) →
  ∀ Φ : GA D (dblSp V) → ℂ, IsBdSec V a (((N : ℝ) - V.rank) / 2) Φ → IsKerOff V N (GlobalTheory.LFun.val χ)⁻¹ Sb (onG V Φ) →
  ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
  ∀ (F₁ F₂ : bddAut V) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFunV V Sb (star F₁.1) B →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sb : Set (FPl D))) B V.rank (((V.rank : ℝ) - 1) / 2) →
  ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re →
    ZetaConvA V a m Φ (((N : ℂ) - V.rank) / 2) s (coefAut V ν 𝓕 F₁ F₂) ∧
    zetaA V a m Φ (((N : ℂ) - V.rank) / 2) s (coefAut V ν 𝓕 F₁ F₂) =
      GlobalTheory.LFun.LSD D Sb B χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (Sb : Set (FPl D)) V.rank N s *
        zetaA V a (m.restrict (offK V Sb)) Φ (((N : ℂ) - V.rank) / 2) s (coefAut V ν 𝓕 F₁ F₂)

def LevelFactor (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) (Sb : Finset (FPl D)) (J : Subgroup (GA D V)),
    IsLevelS V Sb J → ∀ m : Measure (GA D V), m.IsHaarMeasure →
  ∀ mτ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ)), (∀ τ, (mτ τ).IsHaarMeasure) →
    ∃ zf : ℂ → ℂ, Differentiable ℂ zf ∧ (∃ κ : ℝ, 0 < κ ∧ zf 0 = κ) ∧
      ∀ χ : GA D V → ℂ, (∀ k ∈ J, ‖χ k‖ = 1) → ∀ Φ : GA D (dblSp V) → ℂ, Continuous (onG V Φ) → IsLevelKer V Sb J χ (onG V Φ) →
      ∀ c : GA D V → ℂ, Continuous c → (∀ k ∈ J, ∀ g, c (g * k) = χ k * c g) → ∀ s₀ s : ℂ,
        Integrable (fun x => flat V a Φ s₀ s (io V (realPt θ M x, 1)) * starRingEnd ℂ (c (realPt θ M x))) (Measure.pi mτ) →
        ZetaConvA V a (m.restrict (offK V Sb)) Φ s₀ s c ∧
        zetaA V a (m.restrict (offK V Sb)) Φ s₀ s c =
          zf (s - s₀) * ∫ x, flat V a Φ s₀ s (io V (realPt θ M x, 1)) * starRingEnd ℂ (c (realPt θ M x)) ∂(Measure.pi mτ)

def RealConv (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) (τ : D.what₂.Tau)
    (m : Measure (Formalism.REAL.UJ (M.ε τ))), m.IsHaarMeasure → ∀ (s₀ : ℝ) (c : Formalism.REAL.UJ (M.ε τ) → ℂ), Continuous c →
    (∃ C : ℝ, ∀ x, ‖c x‖ ≤ C * grH V a (atPl θ M τ x) ^ (s₀ + (V.rank : ℝ) / 2)) → ∀ v w : M.H τ,
      (∀ s : ℂ, -(1 / 2 : ℝ) < s.re → Integrable (fun x => c x * (grH V a (atPl θ M τ x) : ℂ) ^ (s - s₀) *
        star (Formalism.MainNotions.S.coefOn (M.σ τ) v w x)) m) ∧
      DifferentiableOn ℂ (zReal θ M a τ m c v w s₀) {s | -(1 / 2 : ℝ) < s.re}

def StepCoef (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
    (IsThetaFunO ψ S T fF ∧ fF ≠ 0 ∧ 0 < nrm2 μ 𝓧 fF) ∧ IsLevelS S Sb (Lev.levG S βS LS) ∧
    (∀ κ ∈ Lev.levG S βS LS, ‖Lev.levChi S βS LS κ‖ = 1) ∧
    ∀ P, Continuous (coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P)) ∧
      IsKerOff S T.rank (GlobalTheory.LFun.val χT)⁻¹ Sb (coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P)) ∧
      IsLevelKer S Sb (Lev.levG S βS LS) (Lev.levChi S βS LS) (coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P)) ∧
      ∀ x, coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P) (realPt θ M x) = (nrm2 μ 𝓧 fF : ℂ) *
        ∏ τ, coefSrc om μ 𝓧 (fockAt ψ θ M M' fF τ (P τ)) (atPl θ M τ (x τ)) / (nrm2 μ 𝓧 fF : ℂ)

def RealPos (D : D7) : Prop :=
  NodeGap D →
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
    (∃ P, IsJointAll ψ θ om M M' fF P) ∧ (∃ v, IsTopVec M v) ∧
    ∀ P, IsJointAll ψ θ om M M' fF P → ∀ v, IsTopVec M v → ∀ (τ) (m : Measure (Formalism.REAL.UJ (M.ε τ))), m.IsHaarMeasure →
      Integrable (fun x => coefSrc om μ 𝓧 (fockAt ψ θ M M' fF τ (P τ)) (atPl θ M τ x) *
        star (Formalism.MainNotions.S.coefOn (M.σ τ) (v τ : M.H τ) (v τ) x)) m ∧
      ∃ z : ℝ, 0 < z ∧ ∫ x, coefSrc om μ 𝓧 (fockAt ψ θ M M' fF τ (P τ)) (atPl θ M τ x) *
        star (Formalism.MainNotions.S.coefOn (M.σ τ) (v τ : M.H τ) (v τ) x) ∂m = z

def StepZetaS (D : D7) : Prop :=
  NodeGap D →
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
  ∀ P, IsJointAll ψ θ om M M' fF P → ∀ v, IsTopVec M v →
  ∀ a : GL (Fin S.rank) (AE D), IsMaj S a → HasIwasawa D.sp.cm.sig (dblSp S).gram (Khat S a) →
  ∀ Φ : GA D (dblSp S) → ℂ, onG S Φ = coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P) →
  ∀ m : Measure (GA D S), m.IsHaarMeasure →
    ∃ z : ℂ → ℂ, DifferentiableOn ℂ z {s | -(1 / 2 : ℝ) < s.re} ∧ (∃ r : ℝ, 0 < r ∧ z ((D.R.t : ℂ) / 2) = r) ∧
      ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
      ∀ u ∈ Mult θ M (Lev.levG S βS LS) (Lev.levChi S βS LS), ∀ u' ∈ Mult θ M (Lev.levG S βS LS) (Lev.levChi S βS LS),
      ∀ c : ℂ, IsMultIP M ν 𝓕 u' u c → ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
        ZetaConvA S a (m.restrict (offK S Sb)) Φ ((D.R.t : ℂ) / 2) s (coefAut S ν 𝓕 (u v) (u' v)) ∧
        zetaA S a (m.restrict (offK S Sb)) Φ ((D.R.t : ℂ) / 2) s (coefAut S ν 𝓕 (u v) (u' v)) = z s * starRingEnd ℂ c

def StepZeta (D : D7) : Prop :=
  NodeGap D →
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
  ∀ P, IsJointAll ψ θ om M M' fF P → ∀ v, IsTopVec M v →
  ∀ a : GL (Fin S.rank) (AE D), IsMaj S a → HasIwasawa D.sp.cm.sig (dblSp S).gram (Khat S a) →
  ∀ Φ : GA D (dblSp S) → ℂ, onG S Φ = coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P) →
  ∀ m : Measure (GA D S), m.IsHaarMeasure →
    ∃ z : ℂ → ℂ, DifferentiableOn ℂ z {s | -(1 / 2 : ℝ) < s.re} ∧ (∃ r : ℝ, 0 < r ∧ z ((D.R.t : ℂ) / 2) = r) ∧
      ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
      ∀ u ∈ Mult θ M (Lev.levG S βS LS) (Lev.levChi S βS LS), ∀ u' ∈ Mult θ M (Lev.levG S βS LS) (Lev.levChi S βS LS),
      ∀ c : ℂ, IsMultIP M ν 𝓕 u' u c → ∀ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFunV S Sb (star (u v)) B →
      ∀ s : ℂ, (S.rank : ℝ) / 2 < s.re →
        ZetaConvA S a m Φ ((D.R.t : ℂ) / 2) s (coefAut S ν 𝓕 (u v) (u' v)) ∧
        zetaA S a m Φ ((D.R.t : ℂ) / 2) s (coefAut S ν 𝓕 (u v) (u' v)) =
          GlobalTheory.LFun.LSD D Sb B χT (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (Sb : Set (FPl D)) S.rank T.rank s * z s *
            starRingEnd ℂ c

def IwasawaAll (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)

def HgtMul (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    Continuous (grH V a) ∧ (∀ g, 0 < grH V a g) ∧
    (∀ (v : FPl D) (g : GA D V) (x : Gv V v), projV V v g = 1 → grH V a (g * embV V v x) = grH V a g * grH V a (embV V v x)) ∧
    (∀ g ∈ GinfC V, ∀ k ∈ GfC V, grH V a (g * k) = grH V a g * grH V a k) ∧
    (∀ g, ∀ k ∈ GlobalTheory.Doubling.Kmax V a, grH V a (g * k) = grH V a g) ∧
    ∀ θ : InfFam D, IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) x,
      grH V a (realPt θ M x) = ∏ τ, grH V a (atPl θ M τ (x τ))

def HgtKer (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ v : FPl D, IsLocKer V 2 1 v fun x => (grH V a (embV V v x) : ℂ)

open GlobalTheory.LFun Formalism.UG in

def SumGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (z : ℂˣ) (X : ℂ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → ‖X‖ * (qV E w : ℝ) ^ (r - 1) < 1 →
    (∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      ∀ k₁ ∈ KGL w r, ∀ k₂ ∈ KGL w r, φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * X ^ (∑ i, |d i|).toNat) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ),
      IsSatVecGL w ρ x B →
      (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) →
      ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) →
        HasSum (fun y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => φ y.out * ℓ (ρ y.out x))
          (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
            eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
            (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x)

open GlobalTheory.LFun Formalism.UG in

def SumU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r : ℕ),
    IsUnramInv ϖ σ q → ∀ (X : ℂ) (φ : GU σ r → ℂ), ‖X‖ * (q : ℝ) ^ (2 * (r - 1)) < 1 →
    (∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
      φ (k₁ * t * k₂) = X ^ (∑ i, max (d i) 0).toNat) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ),
      IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) →
        HasSum (fun y : GU σ r ⧸ KU σ r => φ y.out * ℓ (ρ y.out x))
          (eulerFac (GlobalTheory.LGrp.bcParam r α) ((q : ℂ) ^ (r - 1) * X) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X)) * ℓ x)

def LocSum (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
  ∀ (N : ℕ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ N →
  ∀ v : FPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) →
  ∀ φ : Gv V v → ℂ, IsLocKer V N (GlobalTheory.LFun.val χ)⁻¹ v φ →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X) (x : X) (B : GlobalTheory.LFun.Fam D.host.E),
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
      GlobalTheory.LFun.IsParamVec D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) h ρ x (B w) ∧
        ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((V.rank : ℝ) - 1) / 2)) →
    ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re →
      HasSum (fun y : Gv V v ⧸ Kv V v =>
          φ y.out * (grH V a (embV V v y.out) : ℂ) ^ (s - ((N : ℂ) - V.rank) / 2) * ℓ (ρ y.out x))
        (GlobalTheory.LFun.LvTw B (GlobalTheory.LFun.val χ) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E V.rank N v s * ℓ x)

def AbsSum (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ e : ℝ, (V.rank : ℝ) < e → ∃ A : FPl D → ℝ, Summable (fun v => A v - 1) ∧
      ∀ v, HasSum (fun y : Gv V v ⧸ Kv V v => grH V a (embV V v y.out) ^ e) (A v)

def ArchHgt (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (w : InfinitePlace D.host.F) (m : Measure (GlobalTheory.Doubling.Gw V w)), m.IsHaarMeasure → ∀ e : ℝ, (V.rank : ℝ) - 1 < e →
      Integrable (fun x => grH V a (GlobalTheory.AdelicU.embArch D.sp.cm.sig V.gram w x) ^ e) m

def HgtInt (D : D7) : Prop :=
  ∀ (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ e : ℝ, (V.rank : ℝ) < e → Integrable (fun g => grH V a g ^ e) m

def IntCosets : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulLeftInvariant] (U : Subgroup G), IsOpen (U : Set G) → Countable (G ⧸ U) → ∀ f : G → ℂ,
    (Integrable f m → (∀ y : G, IntegrableOn (fun u => f (y * u)) U m) ∧
      HasSum (fun y : G ⧸ U => ∫ u in (U : Set G), f (y.out * u) ∂m) (∫ g, f g ∂m)) ∧
    ((∀ y : G, IntegrableOn (fun u => f (y * u)) U m) →
      Summable (fun y : G ⧸ U => ∫ u in (U : Set G), ‖f (y.out * u)‖ ∂m) → Integrable f m)

def RealChart (D : D7) : Prop :=
  ∀ (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS),
    (∀ τ, ∃ e : Formalism.REAL.UJ (M.ε τ) ≃ₜ* GlobalTheory.Doubling.Gw V (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.plTau D τ),
      ∀ x, atPl θ M τ x = GlobalTheory.AdelicU.embArch D.sp.cm.sig V.gram (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.plTau D τ) (e x)) ∧
    ∃ e : (∀ τ, Formalism.REAL.UJ (M.ε τ)) ≃ₜ* GinfC V, ∀ x, (e x : GA D V) = realPt θ M x

def MeasSplit (D : D7) : Prop :=
  ∀ (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) (Sb : Finset (FPl D))
    (J : Subgroup (GA D V)), IsLevelS V Sb J → ∀ m : Measure (GA D V), m.IsHaarMeasure →
  ∀ mτ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ)), (∀ τ, (mτ τ).IsHaarMeasure) →
    ∃ κ : NNReal, 0 < κ ∧ ∃ mJ : Measure J, mJ.IsHaarMeasure ∧ IsProbabilityMeasure mJ ∧
      m.restrict (infJ V J) = κ • ((Measure.pi mτ).prod mJ).map fun p => realPt θ M p.1 * (p.2 : GA D V)

def SrcKerOn (D : D7) (C : FPl D → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ v, C v →
    (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w ∧ GlobalTheory.LFun.UnrAt χT w) →
    ∃ φ : Gv S v → ℂ, IsLocKer S T.rank (GlobalTheory.LFun.val χT)⁻¹ v φ ∧
      ∀ (x : Gv S v) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ →
        l2 μ 𝓧 (om (embV S v x, 1) f₁) f₂ = φ x * l2 μ 𝓧 f₁ f₂

def SrcKerSplit (D : D7) : Prop := SrcKerOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

def SrcKerInert (D : D7) : Prop := SrcKerOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

def FinComm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ →
  ∀ (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT),
    (∀ (v : FPl D) (g : GA D S), projV S v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (g, 1) f)) ∧
    ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f) →
      (∀ P, IsThetaFunO ψ S T (fockVec ψ θ M M' f P)) ∧
      (∀ v P, VacFin ψ S T v f → VacFin ψ S T v (fockVec ψ θ M M' f P)) ∧
      ∀ g ∈ GfC S, (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) (om (g, 1) f)) ∧
        ∀ P, om (g, 1) (fockVec ψ θ M M' f P) = fockVec ψ θ M M' (om (g, 1) f) P

def StepVac (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
    IsThetaFunO ψ S T fF ∧ fF ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) fF) ∧ ∀ v ∉ Sb, VacFin ψ S T v fF

def StepLevel (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
    IsLevelS S Sb (Lev.levG S βS LS) ∧ (∀ κ ∈ Lev.levG S βS LS, ‖Lev.levChi S βS LS κ‖ = 1) ∧
      SphOff (Lev.levG S βS LS : Set (GA D S)) (Lev.levChi S βS LS) Sb

def StepLaw (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
    ∀ κ ∈ Lev.levG S βS LS, om (κ, 1) fF = Lev.levChi S βS LS κ • fF

def StepSupp (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
    ∀ g ∈ GfC S, g ∈ offK S Sb → g ∉ Lev.levG S βS LS → l2 μ 𝓧 (om (g, 1) fF) fF = 0

def RealKer (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ →
  ∀ (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT),
    ∀ τ (x : Formalism.REAL.UJ (M.ε τ)) P Q, ∃ K : ℂ, ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
      ∀ f₁ f₂, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f₁ →
        IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f₂ →
        l2 μ 𝓧 (om (atPl θ M τ x, 1) (fockAt ψ θ M M' f₁ τ P)) (fockAt ψ θ M M' f₂ τ Q) = K * l2 μ 𝓧 f₁ f₂

def RealPure (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ →
  ∀ (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT),
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
    ∀ f f₁ f₂, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → f ≠ 0 →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f ∧ IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f₁ ∧
        IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f₂) → ∀ P x,
      l2 μ 𝓧 (om (realPt θ M x, 1) (fockVec ψ θ M M' f₁ P)) (fockVec ψ θ M M' f₂ P) = l2 μ 𝓧 f₁ f₂ *
        ∏ τ, coefSrc om μ 𝓧 (fockAt ψ θ M M' f τ (P τ)) (atPl θ M τ (x τ)) / (nrm2 μ 𝓧 f : ℂ)

def RealDecay (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ →
  ∀ (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT),
  ∀ a : GL (Fin S.rank) (AE D), IsMaj S a → HasIwasawa D.sp.cm.sig (dblSp S).gram (Khat S a) →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 →
    ∀ τ f P, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (cart M τ) (cart M' τ)) f →
      Continuous (fun x => coefSrc om μ 𝓧 (fockAt ψ θ M M' f τ P) (atPl θ M τ x)) ∧
      ∃ C : ℝ, ∀ x, ‖coefSrc om μ 𝓧 (fockAt ψ θ M M' f τ P) (atPl θ M τ x)‖ ≤ C * grH S a (atPl θ M τ x) ^ ((T.rank : ℝ) / 2)

def StepBound (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (PS PT : D.what₂.Tau → SPar) (M : DSModel S PS) (M' : DSModel T PT)
    ΛS ΛT βS βT LS χj Sb f₀ fF, IsStep k ψ θ χS χT om M M' ΛS ΛT βS βT LS χj Sb f₀ fF →
  ∀ a : GL (Fin S.rank) (AE D), IsMaj S a → HasIwasawa D.sp.cm.sig (dblSp S).gram (Khat S a) →
  ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ P,
    ∃ C : ℝ, ∀ g, ‖coefSrc om μ 𝓧 (fockVec ψ θ M M' fF P) g‖ ≤ C * grH S a g ^ ((T.rank : ℝ) / 2)

def MultCoef (D : D7) : Prop :=
  ∀ (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ u ∈ Mult θ M J χ, ∀ u' ∈ Mult θ M J χ, ∀ v : M.Vec,
      u v ∈ bddAut V ∧ Continuous (coefAut V ν 𝓕 (u v) (u' v)) ∧
      (∀ k ∈ J, ∀ g, coefAut V ν 𝓕 (u v) (u' v) (g * k) = χ k * coefAut V ν 𝓕 (u v) (u' v) g) ∧
      ∀ c : ℂ, IsMultIP M ν 𝓕 u' u c → ∀ x,
        coefAut V ν 𝓕 (u v) (u' v) (realPt θ M x) = c * ∏ τ, Formalism.MainNotions.S.coefOn (M.σ τ) (v τ : M.H τ) (v τ) (x τ)

def ParBound (D : D7) : Prop :=
  ∀ (V : HSp D) (Sb : Finset (FPl D)) (F : bddAut V) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFunV V Sb F.1 B →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sb : Set (FPl D))) B V.rank (((V.rank : ℝ) - 1) / 2)

def ParFun (D : D7) : Prop :=
  ∀ (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (PS : D.what₂.Tau → SPar) (M : DSModel V PS) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (FPl D)), SphOff J χ Sb → ∀ (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
    GlobalTheory.LFun.IsSysParamD D Sb V.rank c B → ∀ u ∈ partDual θ M J χ Sb c, ∀ v : M.Vec, u v ≠ 0 →
      GlobalTheory.LFun.IsParamFunV V Sb (star (u v)) B

def RecStep : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ k : Fin D.R.m,
    ((k : ℕ) + 1 < D.R.m →
      IsStep k R.ψ R.θ (Lift.chrStep (R.toLevCh.mu A.μ0) R.eta ((k : ℕ) + 1)).1 (Lift.chrStep (R.toLevCh.mu A.μ0) R.eta ((k : ℕ) + 1)).2
        (R.ωY A.μ0 k) (R.MY k) (R.MY ((k : ℕ) + 1)) (R.ΛY k) (R.ΛY ((k : ℕ) + 1)) (R.βY k) (R.βY ((k : ℕ) + 1))
        (R.datYt A.μ0 k R.triv) (R.chi ((k : ℕ) + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R A.μ0) (R.vac k) (R.vY A.μ0 k)) ∧
    ((k : ℕ) + 1 = D.R.m →
      IsStep k R.ψ R.θ (Lift.chrStep (R.toLevCh.mu A.μ0) R.eta D.R.m).1 (Lift.chrStep (R.toLevCh.mu A.μ0) R.eta D.R.m).2
        (R.ωX A.μ0) (R.MY (D.R.m - 1)) R.MX (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX
        (R.datYt A.μ0 (D.R.m - 1) R.triv) (R.chi D.R.m) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R A.μ0) R.vacX (R.vX A.μ0))

end GlobalTheory.CompanionTheory.Ipf.Loc

end
