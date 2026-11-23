import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

def resTo {K Ω : Type} (L : Type) [Field K] [Field L] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {M : Type} [Monoid M] (r : G K Ω →* M) : G L Ω →* M :=
  r.comp (AlgEquiv.restrictScalarsHom K)

def Restricts {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (x : WD h) (x' : WD h') : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h' (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = x' ∧ b.N = a.N ∧
    ∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → b.ρ σ' = a.ρ σ

def Irr {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Prop :=
  1 ≤ a ∧ ∀ W : Submodule k (Fin a → k), (∀ g, ∀ v ∈ W, (r g).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

def IneTriv {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) : Prop :=
  ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ x.lpDim

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

def RegPol (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ χ : HChar (maximalRealSubfield E), GlobalTheory.ContraPair.PolarizedPair π χ

def RepOf (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ (χ : HChar (maximalRealSubfield E)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
    GlobalTheory.ContraPair.PolarizedPair π χ ∧ GalHyps.Props π χ ι r wt HT

def IsAut (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop := ∃ π : CuspSub E a, RepOf π ι r

end GlobalTheory.AboveL

end
