import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)

def latIota : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def chiDet (g : G) : ℂ :=
  ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)

variable {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F)

abbrev sigB : T.Q.c.F →+* ℂ := c'.F.val.toRingHom.comp (incF T.Q.c c' hle)

abbrev Cmp : Type := (T.U ((i : ℕ) + 1) (sigB T hle)).Comp

variable (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)

def toDict (g : GA D (Wc D i)) : GA D (T.V ((i : ℕ) + 1) (sigB T hle)) := cast (congrArg (GA D) hV.symm) g

def adFn (a : (D.host.E →+* ℂ) × ℕ → ℕ) (cc : Cmp T i hle → ℂ) (P : FDSec (T.U ((i : ℕ) + 1) (sigB T hle)).X)
    (g : GA D (Wc D i)) : ℂ :=
  cc (T.dict ((i : ℕ) + 1) (sigB T hle) (toDict T i hle hV g)).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
    T.mu ((i : ℕ) + 1) (sigB T hle) (toDict T i hle hV g) *
      P (T.dict ((i : ℕ) + 1) (sigB T hle) (toDict T i hle hV g)).1
        (T.dict ((i : ℕ) + 1) (sigB T hle) (toDict T i hle hV g)).2

def adC (a : (D.host.E →+* ℂ) × ℕ → ℕ) (cc : Cmp T i hle → ℂ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adFn T i hle hV a cc (rdU (T.U ((i : ℕ) + 1) (sigB T hle)) f)

def adC' (a : (D.host.E →+* ℂ) × ℕ → ℕ) (cc : Cmp T i hle → ℂ) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) c') :
    GA D (Wc D i) → ℂ :=
  adFn T i hle hV a cc (rdU (unfBC hle (T.U ((i : ℕ) + 1)) c'.F.val.toRingHom) f)

variable (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n₀ : ℕ) (v₀ : (R.MW i (sg0 D A)).Vec)
  (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))

def LevelLaw (cc : Cmp T i hle → ℂ) : Prop :=
  ∀ (g : G) (k : GA D (Wc D i)), Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n₀, ∀ x : GA D (Wc D i),
      adC T i hle hV a cc (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g f) x =
        chiDet T R i g * adC T i hle hV a cc f (x * k)

def RationalLaw (cc : Cmp T i hle → ℂ) (ph : ℂ) : Prop :=
  ∀ x₀ : A.fam.amb.FL i A.μ0, ∃ (m : ℕ) (as : Fin m → D.what₂.LL) (fs : Fin m → T.R ((i : ℕ) + 1)),
    (∀ s, fs s ∈ T.cuspA ((i : ℕ) + 1) a n₀) ∧ ∀ g : GA D (Wc D i),
      ph * R.thF i A.μ0 (jVx R i A.μ0 x₀) v₀ g = ∑ s, D.what₂.embLL (as s) * adC T i hle hV a cc (fs s) g

variable (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
  (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
  (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
  {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
  (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F)

def ClassSumLaw (cc : Cmp T i hle → ℂ) (ph : ℂ) (z : G) : Prop :=
  ∀ (x₀ : A.fam.amb.FL i A.μ0) (x : Cl → VsV D i c'.F), Place R i A.μ0 h c0' (jVx R i A.μ0 x₀) x →
    (∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) c' (unfBC hle (T.U ((i : ℕ) + 1))) a n₀,
      IsThClsD (T.Q.Xo ((i : ℕ) + 1)) c' dδ w La Nc gam vol ep io x f) ∧
    ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) c' a n₀, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) c' dδ w La Nc gam vol ep io x f →
      ∀ g : GA D (Wc D i), ph * R.thF i A.μ0 (jVx R i A.μ0 x₀) v₀ g =
        adC' T i hle hV a cc (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' lev z f) g

def LiftPins (jL : D.what₂.LL →+* c'.F) : Prop :=
  ThPinsR R i jL c'.F.val.toRingHom v₀ c0' (latIota T i) T.Q.l.M (Mfr T.Q.l) (fun g => (lev g).1) ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev ∧ ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' lev ∧
    ∃ hw : VsV D i c'.F, IoLFRec c' (embV D jL) (lamV D i) a io hw

def CoverPins : Prop :=
  CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun _ : Unit => dδ) ∧ HalfIs R A.μ0 T.Q.l.Mb dδ.I ∧ dδ.cδ = 1

def ClassPins : Prop :=
  ∃ (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (B : Ideal (𝓞 D.host.E) → c'.F) (epF : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F)
    (φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F),
    BadPin bad (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) ∧
    RepsR R i A.μ0 h bad J' Lh gam vol ∧
    RepsOK (l := dδ.l₂) bad La Nc gam ∧ LatPin Lh La ∧
    PlaceEx R i A.μ0 h c0' ∧
    BIs R i c'.F.val.toRingHom A.μ0 bad B ∧ EpIs (Dw := T.Q.Dw ((i : ℕ) + 1)) c' bad B epF ∧
    (∀ k, ep k = epF (Lh k)) ∧
    PhiIs R i c'.F.val.toRingHom A.μ0 (latIota T i) (Mfr dδ.l₂ • ⊤) φ ∧
    WPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun _ : Unit => Cl) (fun _ => dδ) (fun _ => φ) (fun _ => w)

def OneMapAt : Prop :=
  ∃ (cc : Cmp T i hle → ℂ) (ph : ℂ) (z : G), (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ z ∈ Subgroup.center G ∧
    LevelLaw T R i hle hV a n₀ lev cc ∧
    ClassSumLaw T R i hle hV a n₀ v₀ lev c0' io dδ h La Nc gam vol ep w cc ph z ∧
    RationalLaw T R i hle hV a n₀ v₀ cc ph

def OneMapRef (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) →
    ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)
      (jL : D.what₂.LL →+* c'.F)
      (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
        ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
      (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
      (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
      (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
      (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i))
      (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
      (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F),
      LiftPins T R i (wtA (κ i)) (v₀ i (sg0 D A)) lev c0' io jL → CoverPins T R i dδ →
      ClassPins T R i c0' dδ h La Nc gam vol ep w →
      OneMapAt T R i hle hV (wtA (κ i)) (κ i).n (v₀ i (sg0 D A)) lev c0' io dδ h La Nc gam vol ep w

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters
