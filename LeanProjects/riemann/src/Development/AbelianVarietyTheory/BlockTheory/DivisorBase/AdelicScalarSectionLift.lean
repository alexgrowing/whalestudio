import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LogFactorialIndices.StatementSize

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hook (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·)) List.sortedGE_insertionSort)

variable (D) in

def hookSum (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log
    ((hook ((Wc D i).sig (tauE D ρ)).1 (aPl D i ((Wc D i).sig (tauE D ρ)).1 ρ) : ℝ) *
      (hook ((Wc D i).sig (tauE D ρ)).2 (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 ρ) : ℝ))

variable (D) in

def logSize (b : ℝ) : ℝ := Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ))

variable (D) in

def IsSize (i : Fin D.R.m) (b : ℝ) : Prop :=
  (∀ ρ : D.what₂.Tau, 0 < (((D.hc ρ).e i : ℚ) : ℝ) ∧ (((D.hc ρ).e i : ℚ) : ℝ) ≤ 2 * b ∧
    (∀ l, 0 ≤ (((D.hc ρ).v l : ℚ) : ℝ) ∧ (((D.hc ρ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l, |(((D.hc ρ).b l : ℚ) : ℝ) - (((D.hc ρ).e i : ℚ) : ℝ)| ≤ b) ∧
  ∀ l, ((D.R.k : ℝ) * b) ^ 8 ≤ (D.host.g l : ℝ)

def zeroOff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} (X : Comp → Data E r) :
    Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {P Q} hP hQ k x hx => by
    show P k x + Q k x = 0
    rw [hP k x hx, hQ k x hx, add_zero]
  smul_mem' := fun a P hP k x hx => by
    show a * P k x = 0
    rw [hP k x hx, mul_zero]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def level (F : Face D A) : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levL F b (sg0 D A)

open Classical in

def finS : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def PrimeToHost : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def IsHecke (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D (Wc D i))) : Prop :=
  Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (finS R) P d Rp

def cuspPart (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (finS R) c

def IsAdelicScalar (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (l : ℝ) : Prop :=
  ∀ U ∈ cuspPart R i c, ∃ y : (R.HV i A.μ0).H,
    (∀ f, ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U (R.thF i A.μ0 f) = ⟪y, f⟫_ℂ) ∧ R.thF i A.μ0 y = (l : ℂ) • U

def coordV (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0

def srcAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) (p : P.H),
    LinearMap.ker ((actL (Vc D i) (R.βV i) (R.datVt i A.μ0) p.1 - ((P.chi p : ℂˣ) : ℂ) • LinearMap.id) ∘ₗ coordV R i ℓ)

def IsSrcProj (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H) : Prop :=
  ∀ ℓ y, coordV R i ℓ (e y) =
    gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (coordV R i ℓ y)

def ipSrc (P : LevelP R.Pg D.R.r ℂ) (x y : (R.HV i A.μ0).H) : ℂ := ((Nat.card P.H : ℕ) : ℂ)⁻¹ * ⟪y, x⟫_ℂ

def chiDet (g : G) : ℂˣ := ∏ PP : R.Pg, R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP))

end Adelic

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Sec : Type := FDSec (C.U ((i : ℕ) + 1) O.s0).X

def cuspC : Submodule ℂ (Sec O) :=
  holSub (C.U ((i : ℕ) + 1) O.s0).X (laU (C.U ((i : ℕ) + 1) O.s0) (wtA κ) κ.n) ⊓ zeroOff _

def unitVal (P : Sec O) (g : GA D (Wc D i)) : ℂ :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * P (O.dict g).1 (O.dict g).2

def ipSec (P : LevelP R.Pg D.R.r ℂ) (S S' : Sec O) : ℂ :=
  ((Nat.card P.H : ℕ) : ℂ)⁻¹ * (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
    ∫ g in R.fdW i, unitVal O κ S g * star (unitVal O κ S' g) ∂(R.νW i)

variable (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def dict : Sec O →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) • adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc)

def goodAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (Sec O) :=
  cuspC O κ ⊓ LinearMap.ker ((R.eWf i (sg0 D A) - LinearMap.id) ∘ₗ dict O κ cc) ⊓
    ⨅ p : P.H, LinearMap.ker
      ((actL (Wc D i) (R.βW i) (R.datWp i R.triv) p.1 - ((P.chi p : ℂˣ) : ℂ) • LinearMap.id) ∘ₗ dict O κ cc)

def partAt (P : LevelP R.Pg D.R.r ℂ) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (Sec O) :=
  goodAt O κ cc P ⊓ ⨅ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D (Wc D i))) (_ : IsHecke R i Q d Rp),
    LinearMap.ker ((heckeLin (Wc D i) Rp - c Q d • LinearMap.id) ∘ₗ dict O κ cc)

def IsRepSystem (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
    ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

def IsSecLift (h : O.Cl' () → GA D (Vc D i)) (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) : Prop :=
  ∀ (x₀ : A.fam.amb.FL i A.μ0) (x : O.Cl' () → VsV D i O.c'.F), Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank,
      IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f ∧
      th (jVx R i A.μ0 x₀) = rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f

def ActsByScalar (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H)
    (P : LevelP R.Pg D.R.r ℂ) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (l : ℝ) : Prop :=
  ∀ S ∈ partAt O κ cc P c, ∃ y ∈ srcAt R i P,
    (∀ f ∈ srcAt R i P, ipSec O κ P (th (e f)) S = ipSrc R i P f y) ∧ th (e y) = (l : ℂ) • S

structure DictClauses (F : Face D A) (v₀ : (R.MW i (sg0 D A)).Vec) : Prop where
  inj : ∀ S ∈ cuspC O κ, dict O κ cc S = 0 → S = 0
  integrable : ∀ S ∈ cuspC O κ, ∀ S' ∈ cuspC O κ,
    IntegrableOn (fun g => unitVal O κ S g * star (unitVal O κ S' g)) (R.fdW i) (R.νW i)
  cuspidal : ∃ δ : cuspC O κ →ₗ[ℂ] R.Wall i (sg0 D A),
    (∀ S, (δ S : MMap (R.MW i (sg0 D A))) v₀ = dict O κ cc S) ∧
    (∀ S S', ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) (δ S') (δ S) = ipSec O κ R.triv S S') ∧
    ∀ b, (∀ S : cuspC O κ, (S : Sec O) ∈ goodAt O κ cc (level R F b) →
        (δ S : MMap (R.MW i (sg0 D A))) ∈ R.Wat i (sg0 D A) (level R F b)) ∧
      ∀ c, ∀ S : cuspC O κ, (S : Sec O) ∈ partAt O κ cc (level R F b) c → (δ S : MMap (R.MW i (sg0 D A))) ∈ cuspPart R i c
  proj : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n,
    dict O κ cc (∑ g : G, (RealDat.eC (A := A) (sg0 D A) g * (((chiDet R i g)⁻¹ : ℂˣ) : ℂ)) •
        rdU (C.U ((i : ℕ) + 1) O.s0) (actLev C.Q.c O.lev2 g f)) =
      R.eWf i (sg0 D A) (dict O κ cc (rdU (C.U ((i : ℕ) + 1) O.s0) f))

structure LiftClauses (F : Face D A) (v₀ : (R.MW i (sg0 D A)).Vec) (b : ℝ) (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O)
    (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H) : Prop where
  mem : ∀ y, th y ∈ cuspC O κ
  carry : ∃ (u : ℂ) (z : G), ‖u‖ = 1 ∧ z ∈ Subgroup.center G ∧ ∀ y,
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) (dict O κ cc (th y)) = u • R.thF i A.μ0 y v₀
  scalar : ∀ (s : Option Bool) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), partAt O κ cc (level R F s) c ≠ ⊥ →
    ∃ l : ℝ, 0 < l ∧ IsAdelicScalar R i c l ∧ ActsByScalar O κ cc th e (level R F s) c l ∧
      hookSum D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * logSize D b ≤ Real.log l

end Geometric

def SectionLiftScalar (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → PrimeToHost R →
  ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    DictClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) ∧
    ∀ h, IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∃! th, IsSecLift (O i) (κ i) h th) ∧ (∃! e, IsSrcProj R i e) ∧
      ∀ b, IsSize D i b → ∀ th e, IsSecLift (O i) (κ i) h th → IsSrcProj R i e →
        LiftClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) b th e

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

end
