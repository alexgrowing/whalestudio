import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.LimOddOfLimWU3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.UnramifiedFromSplittingCriterion (RealStep RamOff Step0 Step1)

namespace UpperTheory.Gal.Int.Core

def OneUs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), ImQ E d →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (normV w).Prime → UsPl d w

def IsoOne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r r' : G F Ω →* GL (Fin a) (Qbar l)),
    Continuous r → Continuous r' → IsSSRep r → IsSSRep r' →
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (normV w).Prime → ∃ S, FrobEig ι r w S ∧ FrobEig ι r' w S) → RepIso r r'

def PhiPol : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A w) (x y : WD h) (σ : Weil h),
    (∀ n, GlobalTheory.CongPhi.phiSum x σ n = GlobalTheory.CongPhi.phiSum y σ n) → x.charPol σ = y.charPol σ

def AutT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T ∧ AutOffT T U

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def AttOne (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω] (r : G L Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (normV w).Prime →
    ∃ B, sat (w.under (𝓞 F)) B ∧ FrobEig ι r w (algSat a (normV w) B)

end

def OneTower : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω]
    (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M]
    [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (r : G K Ω →* GL (Fin a) (Qbar l)),
    AttOne sat ι K r → AttOne sat ι M (r.comp (res K Ω M))

def OneConj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop)
    (r : G K Ω →* GL (Fin a) (Qbar l)) (g : G F Ω) (c : G K Ω →* G K Ω), (∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹) →
    Function.Surjective c → AttOne sat ι K r → AttOne sat ι K (r.comp c)

def PatchOne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop),
    (∀ v B B', sat v B → sat v B' → B = B') → ∀ S : Set (QCM F Ω), S.Infinite →
    ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttOne sat ι ↥Q.1.K (r Q)) →
    ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧
      ∀ᶠ Q : ↥S in Filter.cofinite, RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K))

def SphDown (c : GlobalTheory.RoadU.Sph) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (Q : QCM E Ω) (P : CuspSub ↥Q.K a), IsLift π P →
    ∀ (ρ : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), (CG.mk π).HasSat w B →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (res E Ω ↥Q.K).range) →
    (∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B →
      GlobalTheory.RoadU.SphAt c P ι (ρ.comp (res E Ω ↥Q.K)) w' B) →
    GlobalTheory.RoadU.SphAt c π ι ρ w B

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

def Serves {a : ℕ} (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (Q : QCM E Ω) : Prop :=
  (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (res E Ω ↥Q.K).range) ∧
    (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧
    ∀ P : CuspSub ↥Q.K a, IsLift π P → ∃ p : HeightOneSpectrum (𝓞 ↥Q.K) → Prop, RowP Ω p P ι ∧
      (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, (normV w).Prime → p w) ∧ ∀ w, w.under (𝓞 E) = w₀ → p w

end

def StepDown : Prop :=
  QuadLift → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (∀ w₀, {Q : QCM E Ω | Serves π ι w₀ Q}.Infinite) → RowP Ω (fun _ => True) π ι

def CsdLift : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
    ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (P : CuspSub M a), IsLift π P → InScope .all l π (quadChar E ^ a) → InScope .all l P (quadChar M ^ a)

def RamUnr : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Set (HeightOneSpectrum (𝓞 F))) (Q : QCM F Ω), RamOff T Q →
    ∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal ∧ w.under (𝓞 F) ∉ T

def Step2 {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y))) (Q : QCM Y Ω) : Prop :=
  Step1 T Q ∧ UpperTheory.Gal.TP.InertOK ↥Q.K ∧
    ∃ d : ℕ, ImQ ↥Q.K d ∧ ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 Y) ∈ T → UsPl d w

def Quad2Ex : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ T : Set (HeightOneSpectrum (𝓞 Y)), T.Finite → ∃ Q : QCM Y Ω, Step2 T Q

def JoinU : Prop := LimU → CoreUd

def JoinAll : Prop := UpperTheory.Gal.TP.TwoUpOK → CoreUd → AllUd

def JoinGL : Prop := DescOffT → AllUd → CoreGLu

def JoinUp : Prop := GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual → QuadLift → CoreGLu → RowCsd

def JoinEnd : Prop := RowCsd → GlobalTheory.RoadW.RowStarCore

end UpperTheory.Gal.Int.Core

end
