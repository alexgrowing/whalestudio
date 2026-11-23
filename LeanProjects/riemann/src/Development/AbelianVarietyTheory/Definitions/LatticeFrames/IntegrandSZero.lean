import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev WRep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

section Objects

variable {A B : HSp D} (om : WRep A B) (m : Measure (GA D A))

def up (Φ : WO A B → ℂ) (u : GA D A → ℂ) : GA D B → ℂ :=
  fun h => ∫ q, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h Φ * u g) q ∂autMeasure A m

def UpConv (mH : Measure (GA D B)) (Φ : WO A B → ℂ) (u : GA D A → ℂ) : Prop :=
  (∀ h, Integrable (AutomorphicL2Unitary.descend (GQ A) fun g => thetaKO om g h Φ * u g) (autMeasure A m)) ∧
    MemL2Quotient (GQ B) mH (up om m Φ u)

def wcoef (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (Φ₁ Φ₂ : WO A B → ℂ) : GA D A → ℂ :=
  fun g => ip A B ν 𝓕 (om (g, 1) Φ₁) Φ₂

def rcoef (u₁ u₂ : GA D A → ℂ) : GA D A → ℂ := fun g => petersson A m (rTr A g u₁) u₂

variable (A) in

def hgtL (L : Lat A) (a : GL (Fin A.rank) (AE D)) (g : GA D A) : ℝ≥0 :=
  hgtAd D.sp.cm.sig (dblSp A).gram L a (io A (g, 1))

def integrand (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ)
    (u₁ u₂ : GA D A → ℂ) (s : ℂ) : GA D A → ℂ :=
  fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A L a g) (s - sZero A B) * rcoef m u₁ u₂ g

variable (A) in

def openOff (L : Lat A) (Sf : Finset (FinPl D)) : Set (GA D A) :=
  {g | ∀ v ∉ Sf, proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram L v}

variable (A) in

def SphFun (L : Lat A) (Sf : Finset (FinPl D)) (u : GA D A → ℂ) : Prop :=
  ∀ v ∉ Sf, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ g, u (g * emb D.sp.cm.sig A.gram v k) = u g

end Objects

structure Pair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)) : Prop where

  setting : HidaSetting θ A B sA sB t cA

  maj : IsMaj A a

  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1

  weil : IsWeilDatumO ψ A B χA χB om

  covol : IsCovolOne (ratL B A) ν 𝓕

structure Unram (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (LA : Lat A) (LB : Lat B)
    (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ) : Prop where

  sdA : IsSelfDualC A LA

  sdB : IsSelfDualC B LB

  two : ∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

  unr : LFun.UnrOff χB (Sf : Set (FinPl D))

  sph₁ : IsSphOff ψ A B LA LB Sf Φ₁

  sph₂ : IsSphOff ψ A B LA LB Sf Φ₂

def SiegelWeilAll (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank →
    (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omh (Khat A a) φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

def GlobalFormAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalForm (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAt A L

def IsSphSecAt (A : HSp D) (L : Lat A) (v : FinPl D) (μ : (AE D)ˣ →* Circle) (s : ℂ) (φ : Gv (dblSp A) v → ℂ) : Prop :=
  φ ∈ degPSFin D.sp.cm.sig (dblSp A).gram L v (charAt μ v) s ∧
    (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, φ (g * k) = φ g) ∧ φ 1 = 1

def ioAt (A : HSp D) (v : FinPl D) (y : Gv A v) : Gv (dblSp A) v := ioH _ D.sp.cm.sig (gram_hdbl A) (y, 1)

def SphFactor (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ s : ℂ, ∃ φ, IsSphSecAt A LA v χB⁻¹ s φ ∧
    ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → ∀ y : Gv A v,
      wcoef om ν 𝓕 Φ₁ Φ₂ (x * emb D.sp.cm.sig A.gram v y) *
          npow (hgtL A LA a (x * emb D.sp.cm.sig A.gram v y)) (s - sZero A B) =
        wcoef om ν 𝓕 Φ₁ Φ₂ x * npow (hgtL A LA a x) (s - sZero A B) * φ (ioAt A v y)

def IsSphCoef (A : HSp D) (L : Lat A) (v : FinPl D) (par : LFun.Fam D.host.E) (c : Gv A v → ℂ) : Prop :=
  (∃ C : ℝ, ∀ y, ‖c y‖ ≤ C) ∧
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (Gv A v) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ),
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
      LFun.IsParamVec D.sp.cm.sig A.gram L h ρ x (par w)) ∧
    (∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ∀ y, ℓ (ρ (k * y) x) = ℓ (ρ y x)) ∧ ∀ y, c y = ℓ (ρ y x)

def LocalZetaOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D χ → ResEta D χ b →
  ∀ v, C v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → LFun.UnrAt χ w) →
  ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 →
  ∀ s : ℂ, (A.rank : ℝ) < s.re → ∀ φ, IsSphSecAt A L v χ⁻¹ s φ → ∀ par c, IsSphCoef A L v par c →
    Integrable (fun y => φ (ioAt A v y) * c y) μ ∧
      ∫ y, φ (ioAt A v y) * c y ∂μ =
        LFun.LvTw par (LFun.val χ) v (s + 1 / 2) / LFun.dv D.host.E A.rank b v s * c 1

def ParamBoundOn (D : D7) (C : FinPl D → Prop) : Prop :=
  ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v, C v → ∀ par c, IsSphCoef A L v par c → c 1 ≠ 0 →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → (par w).card = A.rank ∧
      ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((A.rank : ℝ) / 2)

def EulerRight (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ →
    Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
  ∀ s : ℂ, (A.rank : ℝ) + 1 < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m →
    ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
      LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m

def HeckeForm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

theorem integrand_sZero {A B : HSp D} (om : WRep A B) (m : Measure (GA D A)) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (L : Lat A) (a : GL (Fin A.rank) (AE D)) (Φ₁ Φ₂ : WO A B → ℂ) (u₁ u₂ : GA D A → ℂ) (g : GA D A) :
    integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ (sZero A B) g = wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
  simp [integrand, GlobalTheory.Doubling.npow]

theorem one_mem_openOff (A : HSp D) (L : Lat A) (Sf : Finset (FinPl D)) : (1 : GA D A) ∈ openOff A L Sf :=
  fun v _ => by rw [map_one]; exact one_mem _

end GlobalTheory.Core.Rk.IP

end
