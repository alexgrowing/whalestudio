import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeJ

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

def ball (la : HeightOneSpectrum (𝓞 Ks)) : Set Φ.WK := {f | ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1}

def resW (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Φ.WK →ₗ[Ks] Φ.WK :=
  (hL.restrictScalars Ks).restrict hW

def LiesOver (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') : Prop :=
  ∀ x : Ks, algebraMap Ks K' x ∈ O ↔ FinitePlace.mk la x ≤ 1

def latK (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[Ks] Φ.WK) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[Ks] f) '' ball Φ la)

def latKIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[Ks] Φ.WK) :=
  latK Φ la O ⊓ (((V.restrictScalars Ks).comap Φ.WK.subtype).baseChange K').restrictScalars O

def latL (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[LL] WL) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[LL] (f : WL)) '' ball Φ la)

def latLIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[LL] WL) :=
  latL Φ la O ⊓ (V.baseChange K').restrictScalars O

structure Keeps (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Prop where

  sup : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1

  rho : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL

  eOp : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL

  typeP : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam

  good : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC

  overK : ∀ (K' : Type) [Field K'] [Algebra Ks K'] (O : ValuationSubring K'), LiesOver la O →
    (∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latKIn Φ la O (Φ.typeP J lam), (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latKIn Φ la O (Φ.Wgood J lam eC),
        (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.Wgood J lam eC)

  overL : ∀ (K' : Type) [Field K'] [Algebra LL K'] [Algebra Ks K'] [IsScalarTower Ks LL K'] (O : ValuationSubring K'),
    LiesOver la O →
    (∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latLIn Φ la O (Φ.typeP J lam), hL.baseChange K' x ∈ latLIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latLIn Φ la O (Φ.Wgood J lam eC), hL.baseChange K' x ∈ latLIn Φ la O (Φ.Wgood J lam eC)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def hkC {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : ℂ :=
  ((((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ k)⁻¹ * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

theorem two_mul_half : 2 * (D.R.nV / 2) = D.R.nV := Nat.two_mul_div_two_of_even (kapDom D).2

def IsHkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ k ≤ D.R.r ∧
    IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def OffChar {Ks : Type} [Field Ks] [NumberField Ks] (P : Formalism.L2.DIV.Pl D.host.E) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal → (p : 𝓞 Ks) ∉ la.asIdeal

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def ConstPinned (i : Fin D.R.m) : Prop :=
  ∃ (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph

theorem constPinned_of (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hp : OMPins T R κ v₀ O i)
    (hr : OneMapRow0 T R κ v₀ O i) (hc : CTie T R κ v₀ O i) : ConstPinned T R κ v₀ i :=
  ⟨O i, (hc hr).choose, hp.1, hp.2, (hc hr).choose_spec⟩

structure ReadAt0 (i : Fin D.R.m) : Prop where
  ex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV
  inj : Function.Injective ((R.FW i).j (sg0 D A))
  rho : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ
  const : ConstPinned T R κ v₀ i

theorem readAt0_of (hj : JEvExists T R κ v₀) (fw : FWTie T R κ v₀) (hu : R.LUnif) (i : Fin D.R.m)
    (hc : ConstPinned T R κ v₀ i) : ReadAt0 T R κ v₀ i where
  ex hV := hj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV
  inj := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h
    have h1 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
    exact h1.ne_zero 0 hx
  rho := (hu i (sg0 D A)).2.2
  const := hc

def HkSupAt (i : Fin D.R.m) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    ∀ (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)),
      HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (hkC R i P k) hL →
      ∀ (hW : ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OffChar P la →
        Keeps (R.FW i) la hL hW

def HkSup : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), R.Char F →
    ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
      (_fw : FWTie T R κ v₀) (i : Fin D.R.m), ReadAt0 T R κ v₀ i → HkSupAt T R i

end GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls
