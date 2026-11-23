import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def IsRootOfUnity (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

def normQ (Q : Finset (Pl D.host.E)) : ℕ := ∏ PP ∈ Q, Nat.card (kP PP)

def IsCentralInv (V : HSp D) (Q : Finset (Pl D.host.E)) (z : GA D V) : Prop :=
  z ∈ GfC V ∧ ∃ es : Pl D.host.E → AE D, (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) ∧
    mt V z = Matrix.diagonal fun _ =>
      1 + ∑ PP ∈ Q, (es PP * (incA D ((Nat.card (kP PP) : D.host.E)⁻¹) - 1) +
        cA D (es PP) * (incA D (Nat.card (kP PP) : D.host.E) - 1))

section Series

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

open Classical in

def flatFun (t : T0) (e : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ∧
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
      omegaQ (R.Q t) (Wc D i).rank (R.xiR t) 1 (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
  else 0

def IsFlatVec (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ eg eQ : AE D, IsIdemSum eg R.Pg ∧ IsIdemSum eQ (R.Q t) ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg + eQ)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (flatFun R i t (cA D eg + eQ)) f

def ptOf (f : WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f

abbrev Low : Type := ∀ ρ, lowT (R.MW i (sg0 D A)) ρ

def ser (v : Low R i) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W) : GA D (Wc D i) → ℂ :=
  fun x => thetaKO (R.ωP i t) h x (ptOf R i f (R.ioP i (PiTensorProduct.tprod ℂ v) w))

def IsClassReps (t : T0) {Cl : Type} (h : Cl → GA D (Vc D i)) : Prop :=
  (∀ k, h k ∈ GfC (Vc D i)) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (levJ R i t) fun k => fin _ (h k)

def clSum (v : Low R i) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
    (y : (R.HV i t).H) : GA D (Wc D i) → ℂ :=
  fun x => ∑ k, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (levJ R i t) (fin _ (h k))) : ℕ) : ℂ)⁻¹ *
    ser R i v t f (h k) ((R.HV i t).e y (fin _ (h k))) x

def ConjTup (g : ℂ ≃+* ℂ) (t t' : T0) : Prop :=
  R.Q t' = R.Q t ∧ ∀ x : (AE D)ˣ, ((R.xi t' x : Circle) : ℂ) = g ((R.xi t x : Circle) : ℂ)

end Series

section Pinned

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)

def Pinned : Prop :=
  GlobalTheory.Hk3.Core R F ∧ TieIn T R κ v₀ ∧ OMPins T R κ v₀ O i ∧ PhaseTie T R κ v₀ O ph i ∧ QGuard R

def FixesBase (g : ℂ ≃+* ℂ) : Prop :=
  (∀ x ∈ T.Q.c.F, g x = x) ∧ (∀ (τ : D.host.E →+* ℂ) (a : D.host.E), g (τ a) = τ a) ∧
    (∀ PP : Pl D.host.E, (R.C.mu0 i * R.C.eta⁻¹).UnrAt PP →
      g ((R.C.mu0 i * R.C.eta⁻¹).valTw (1 / 2) PP) = (R.C.mu0 i * R.C.eta⁻¹).valTw (1 / 2) PP) ∧
    (∀ PP ∈ R.Pg, ∀ a, g ((R.chi ((i : ℕ) + 1) PP a : ℂˣ) : ℂ) = ((R.chi ((i : ℕ) + 1) PP a : ℂˣ) : ℂ)) ∧
    GlobalTheory.CompRat.FixesCurve T.Q.H g (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')

def IsLowestKTypeVector (v : Low R i) : Prop := ∀ ρ, (v ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ

def rd (f : T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) : GA D (Wc D i) → ℂ :=
  fun x => (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
    (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.toCore.R ((i : ℕ) + 1)) x

def ConjFun (g : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n),
    (∀ x, ph i * Φ x = ∑ k, a k * rd T R κ O i (f k) x) → ∀ x, ph i * Φ' x = ζ * ∑ k, g (a k) * rd T R κ O i (f k) x

def ConjVec (g : ℂ ≃+* ℂ) (w w' : (R.cV i).W) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ) (P : Fin n → VsV D i (O i).c'.F),
    (∀ k m, g (inC (O i).c' (MvPolynomial.coeff m (P k : Pol (O i).c'.F D.what₂.Tau (Vc D i).rank))) =
      inC (O i).c' (MvPolynomial.coeff m (P k : Pol (O i).c'.F D.what₂.Tau (Vc D i).rank))) ∧
    w = ∑ k, a k • (O i).c0' (P k) ∧ w' = ∑ k, g (a k) • (O i).c0' (P k)

def ConjForm (g : ℂ ≃+* ℂ) (t t' : T0) (y : (R.HV i t).H) (y' : (R.HV i t').H) : Prop :=
  ∀ h : Bridge.Gf (Vc D i), ConjVec T R O i g ((R.HV i t).e y h) ((R.HV i t').e y' h)

def SeriesConj (g : ℂ ≃+* ℂ) (ζ : ℂ) (t t' : T0) : Prop :=
  ∀ v, IsLowestKTypeVector T R v₀ i v → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∀ h ∈ GfC (Vc D i), ∀ w w',
    ConjVec T R O i g w w' → ConjFun T R κ O ph i g ζ (ser R i v t f h w) (ser R i v t' f' h w')

def ClassConj (g : ℂ ≃+* ℂ) (ζ : ℂ) (t t' : T0) : Prop :=
  ∀ v, IsLowestKTypeVector T R v₀ i v → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' →
    ∀ (Cl Cl' : Type) [Fintype Cl] [Fintype Cl'] (h : Cl → GA D (Vc D i)) (h' : Cl' → GA D (Vc D i)),
      IsClassReps R i t h → IsClassReps R i t' h' → ∀ y y', ConjForm T R O i g t t' y y' →
        ConjFun T R κ O ph i g ζ (clSum R i v t f h y) (clSum R i v t' f' h' y')

def LiftConj (g : ℂ ≃+* ℂ) (ζ : ℂ) (t t' : T0) : Prop :=
  ∀ y y', ConjForm T R O i g t t' y y' →
    ConjFun T R κ O ph i g ζ (R.thF i t y (v₀ i (sg0 D A))) (R.thF i t' y' (v₀ i (sg0 D A)))

def ConjClauses : Prop :=
  ∀ g : ℂ ≃+* ℂ, FixesBase T R i g → ∀ t : T0,
    (∃ ζ : ℂ, IsRootOfUnity ζ ∧ ∀ t', ConjTup R g t t' →
      SeriesConj T R κ v₀ O ph i g ζ t t' ∧ ClassConj T R κ v₀ O ph i g ζ t t') ∧
    (∃ ζ' : ℂ, IsRootOfUnity ζ' ∧ ∀ t', ConjTup R g t t' → LiftConj T R κ v₀ O ph i g ζ' t t') ∧
    ∀ t', ConjTup R g t t' → ∀ y, ∃ y', ConjForm T R O i g t t' y y'

def coefLat (B : Subring ℂ) (h : Bridge.Gf (Vc D i)) : Submodule B (R.cV i).W :=
  Submodule.span B ((O i).c0' '' (nabAtr (embV D (O i).jL) (lamV D i) (Bridge.hLat (Vc D i) h) : Set (VsV D i (O i).c'.F)))

def Mt (B : Subring ℂ) (t : T0) : Set (R.HV i t).H := {y | ∀ h, (R.HV i t).e y h ∈ coefLat T R O i B h}

def serSpan (B : Subring ℂ) (v : Low R i) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) : Submodule B (GA D (Wc D i) → ℂ) :=
  Submodule.span B {Φ | ∃ h ∈ GfC (Vc D i), ∃ w ∈ coefLat T R O i B (fin _ h), Φ = ser R i v t f h w}

def GoodRing (t : T0) (u : ℂ) (B : Subring ℂ) : Prop :=
  (∀ a : 𝓞 (O i).c'.F, inC (O i).c' (a : (O i).c'.F) ∈ B) ∧ ((normQ (R.Q t) : ℕ) : ℂ)⁻¹ ∈ B ∧ u ∈ B ∧ u⁻¹ ∈ B

def TwoData : Prop :=
  ∀ t : T0, ∃ (z : GA D (Vc D i)) (u : ℂ), IsCentralInv (Vc D i) (R.Q t) z ∧ UnitOff (normQ (R.Q t)) u ∧
    (∃ f, IsFlatVec R i t f) ∧ ∀ f, IsFlatVec R i t f →
      f = u • R.ωP i t (z, 1) (R.vP i t) ∧ ∀ v, IsLowestKTypeVector T R v₀ i v →
        (∀ h ∈ GfC (Vc D i), ∀ w, ser R i v t f h w = u • ser R i v t (R.vP i t) (h * z) w) ∧
        ∀ B : Subring ℂ, GoodRing T R O i t u B →
          serSpan T R O i B v t f = serSpan T R O i B v t (R.vP i t) ∧
          ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), IsClassReps R i t h →
            clSum R i v t f h '' Mt T R O i B t = (fun y => R.thF i t y (v₀ i (sg0 D A))) '' Mt T R O i B t

def At : Prop := Pinned T R F κ v₀ O ph i → ConjClauses T R κ v₀ O ph i ∧ TwoData T R v₀ O i

end Pinned

def TwistConj (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), At T R F κ v₀ O ph i

section Checks

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

end
