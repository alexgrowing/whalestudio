import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.RowDefOfOdd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def pl (φ : E →+* ℂ) : InfinitePlace (maximalRealSubfield E) := (InfinitePlace.mk φ).comap (algebraMap (maximalRealSubfield E) E)

open Classical in

def typ (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (a b : InfinitePlace (maximalRealSubfield E) → ℤ) (φ : E →+* ℂ) : ℤ :=
  if φ = (emb (pl φ)).1 then a (pl φ) else b (pl φ)

def InfExp (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (μ : HChar E) (m : InfinitePlace (maximalRealSubfield E) → ℤ) : Prop :=
  ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ w, ((emb w).1 (k : E) / ‖(emb w).1 (k : E)‖) ^ m w

def Reads (μ : HChar E) (χ : Chr (maximalRealSubfield E) E) : Prop :=
  ∀ z : (AE (maximalRealSubfield E) E)ˣ, (χ z : ℂ) =
    ((μ.1 (Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).toRingHom.toMonoidHom z) : ℂˣ) : ℂ)

def ChrEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (w₀ : HeightOneSpectrum (𝓞 E)) (m : InfinitePlace (maximalRealSubfield E) → ℤ), (∀ w, Odd (m w)) →
    ∃ (χ : Chr (maximalRealSubfield E) E) (ψ : ℕ → ℤ → HChar E), UnrAt χ w₀ ∧
      (∀ k : ℕ, IsHecke (maximalRealSubfield E) E (χ ^ k) ∧ HasExp emb (χ ^ k) (fun w => k * m w) ∧
        ∀ j : ℕ, j % 2 = k % 2 → ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range (χ ^ k) j) ∧
      (∀ k s w, ((ψ k s).UnrAt w ↔ UnrAt (χ ^ k) w) ∧
        (((ψ k s).val w : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (-(s : ℂ) / 2)) ∧
      (∀ (k : ℕ) (s : ℤ), Even (k + s) → IsAlgPos (ψ k s) (typ emb (fun w => (s + k * m w) / 2) fun w => (s - k * m w) / 2)) ∧
      ∀ k k' s s', ψ k s = ψ k' s' → k = k'

def MuEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (w₀ : HeightOneSpectrum (𝓞 E)) (m : InfinitePlace (maximalRealSubfield E) → ℤ), (∀ w, Odd (m w)) →
    ∃ μ : HChar E, μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
      InfExp emb μ m ∧ μ.UnrAt w₀

def ReadEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    ∃ χ : Chr (maximalRealSubfield E) E, Reads μ χ ∧ IsHecke (maximalRealSubfield E) E χ

def ReadLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (χ : Chr (maximalRealSubfield E) E), Reads μ χ → ∀ w, locChar χ w = μ.loc w

def ReadRes : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (χ : Chr (maximalRealSubfield E) E), Reads μ χ →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χ 1

def ReadExp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (μ : HChar E)
    (χ : Chr (maximalRealSubfield E) E) (m : InfinitePlace (maximalRealSubfield E) → ℤ), Reads μ χ → InfExp emb μ m → HasExp emb χ m

def AbsFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (z : ℂ),
    (∀ w, (Model.absC E z).UnrAt w ∧ (((Model.absC E z).val w : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (-z)) ∧
    ∀ k : Eˣ, (((Model.absC E z).inf k : ℂˣ) : ℂ) = ∏ w, ((‖(emb w).1 (k : E)‖ : ℝ) : ℂ) ^ (2 * z)

def TypProd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (a b : InfinitePlace (maximalRealSubfield E) → ℤ) (x : E),
    ∏ φ : E →+* ℂ, φ x ^ typ emb a b φ = ∏ w, (emb w).1 x ^ a w * (starRingEnd ℂ ((emb w).1 x)) ^ b w

def TypVal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (a b : InfinitePlace (maximalRealSubfield E) → ℤ) (w : InfinitePlace (maximalRealSubfield E)),
    typ emb a b (emb w).1 = a w ∧ typ emb a b (ComplexEmbedding.conjugate (emb w).1) = b w

def ExpInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (m m' : InfinitePlace (maximalRealSubfield E) → ℤ) (s s' : ℤ),
    (∀ k : Eˣ, ∏ w, ((emb w).1 (k : E) / ‖(emb w).1 (k : E)‖) ^ m w * ((‖(emb w).1 (k : E)‖ : ℝ) : ℂ) ^ s =
      ∏ w, ((emb w).1 (k : E) / ‖(emb w).1 (k : E)‖) ^ m' w * ((‖(emb w).1 (k : E)‖ : ℝ) : ℂ) ^ s') → m = m'

end UpperTheory.Gal.TP.Chr

end
