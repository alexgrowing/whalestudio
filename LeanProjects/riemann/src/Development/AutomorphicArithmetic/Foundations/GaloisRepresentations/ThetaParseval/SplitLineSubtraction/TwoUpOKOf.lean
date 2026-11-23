import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.AllCoreOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)

namespace UpperTheory.Gal.TP.Sub

structure Dict {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) {t : ℕ}
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ)
    (κ : HChar E) (m : (E →+* ℂ) → ℤ) (ψ : Fin t → HChar E) (p : Fin t → (E →+* ℂ) → ℤ) : Prop where
  alg : ∀ i, IsAlgPos (ψ i) (p i)
  m₁ : ∀ w, 2 * m (emb w).1 = mW w - mX w + t
  m₂ : ∀ w, 2 * m (ComplexEmbedding.conjugate (emb w).1) = mX w - mW w + t
  p₁ : ∀ i w, 2 * p i (emb w).1 = mX w + 2 * (i : ℕ) - (n + 2 * t - 2)
  p₂ : ∀ i w, 2 * p i (ComplexEmbedding.conjugate (emb w).1) = -mX w + 2 * (i : ℕ) - (n + 2 * t - 2)
  loc : ∀ w : HeightOneSpectrum (𝓞 E), κ.UnrAt w → (∀ i, (ψ i).UnrAt w) → GlobalTheory.LFun.UnrAt χX w ∧ GlobalTheory.LFun.UnrAt χW w ∧
    ((κ.val w : ℂˣ) : ℂ) = (GlobalTheory.LFun.val χW w : ℂ) * (GlobalTheory.LFun.val χX w : ℂ)⁻¹ *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2)) ∧
    ∀ i, (((ψ i).val w : ℂˣ) : ℂ) = (GlobalTheory.LFun.val χX w : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (i : ℕ))

def ChrPairs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n t : ℕ), Even n → Odd t → ∀ (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) (b : ℤ) (w₀ : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ) (χX χW : Fin 2 → Chr (maximalRealSubfield E) E)
      (mX mW : Fin 2 → InfinitePlace (maximalRealSubfield E) → ℤ) (ψ : Fin 2 → Fin t → HChar E) (p : Fin 2 → Fin t → (E →+* ℂ) → ℤ),
      IsAlgPos κ m ∧ (∀ j, GlobalTheory.LFun.IsHecke (maximalRealSubfield E) E (χX j) ∧ GlobalTheory.LFun.IsHecke (maximalRealSubfield E) E (χW j) ∧
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range (χX j) n ∧
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range (χW j) (n + t) ∧
        HasExp emb (χX j) (mX j) ∧ HasExp emb (χW j) (mW j) ∧ (∀ w, mW j w ≤ b) ∧
        Dict n emb (χX j) (χW j) (mX j) (mW j) κ m (ψ j) (p j)) ∧
      (∀ i i', ψ 0 i ≠ ψ 1 i') ∧ κ.UnrAt w₀ ∧ ∀ i, (ψ 0 i).UnrAt w₀

def EmbSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w),
    (∀ τ : E →+* ℂ, ∃ w, τ = (emb w).1 ∨ τ = ComplexEmbedding.conjugate (emb w).1) ∧
    (∀ w w', (emb w).1 = (emb w').1 → w = w') ∧ ∀ w w', (emb w).1 ≠ ComplexEmbedding.conjugate (emb w').1

def WtId : Prop :=
  ∀ (n t : ℕ) (lam : DomWeight n) (lam' : DomWeight (n + t)) (mX mW : ℤ), UpperTheory.TP.IsLiftWt lam mX mW lam' →
    (∀ (m : ℤ) (p : Fin t → ℤ), 2 * m = mW - mX + t → (∀ i, 2 * p i = mX + 2 * (i : ℕ) - (n + 2 * t - 2)) →
      wtJumps lam' = (wtJumps lam).map (· + m) + Finset.univ.val.map fun i => -p i) ∧
    ∀ (m : ℤ) (p : Fin t → ℤ), 2 * m = mX - mW + t → (∀ i, 2 * p i = -mX + 2 * (i : ℕ) - (n + 2 * t - 2)) →
      wtJumps lam'.dual = (wtJumps lam.dual).map (· + m) + Finset.univ.val.map fun i => -p i

def SatId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n t : ℕ) (B : Multiset ℂˣ) (x y : ℂˣ) (k : ℂ) (c : Fin t → ℂ),
    k = (y : ℂ) * (x : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2)) →
    (∀ i, c i = (x : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (i : ℕ))) →
    algSat (n + t) (Ideal.absNorm w.asIdeal) (B.map (· * (x * y⁻¹)) + GlobalTheory.LFun.seg w x t) =
      (algSat n (Ideal.absNorm w.asIdeal) B).map (· * k⁻¹) + Finset.univ.val.map c

def UpOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n t : ℕ), 1 ≤ n → n < t → ∀ (Bs : Base (maximalRealSubfield E) E) (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ)
    (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight n,
    (∀ τ, GlobalTheory.UnitaryBC.HasWeightAt U τ (lam τ)) → ∀ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E (n + t) → ℂ),
    UpperTheory.TP.IsLift Bs χX χW mX mW (fun w => lam (Bs.emb w).1) U U' →
    ∀ (κ : HChar E) (m : (E →+* ℂ) → ℤ) (ψ : Fin t → HChar E) (p : Fin t → (E →+* ℂ) → ℤ),
      Dict n Bs.emb χX χW mX mW κ m ψ p → ∃ lam', IsUp U lam κ m U' lam' ψ p

def BaseNG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → InertOK E →
    ∃ (Bs : Base (maximalRealSubfield E) E) (δ : E) (𝔞 : Submodule (𝓞 E) E), UpperTheory.TP.GoodNG (UpperTheory.TP.cj E) Bs ∧
      (∀ n, (Skew.stdSpc (maximalRealSubfield E) E n).IsHerm (UpperTheory.TP.cj E) Bs n 0) ∧
      ∀ d, (Skew.skewSpc (maximalRealSubfield E) δ 𝔞 d).IsSkew (UpperTheory.TP.cj E) Bs d 0

end UpperTheory.Gal.TP.Sub

end
