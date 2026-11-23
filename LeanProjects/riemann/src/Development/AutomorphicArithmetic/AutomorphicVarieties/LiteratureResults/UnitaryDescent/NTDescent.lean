import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace UpperTheory.V.Lit.Desc

def Phi (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if j = i.rev then (-1) ^ (i : ℕ) else 0

def snd {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Phi K n * (g⁻¹)ᵀ * (Phi K n)⁻¹

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsZeta (n : ℕ) (z : E) : Prop :=
  (Odd n → z = 1) ∧ (Even n → z ≠ 0 ∧ z + IsCMField.complexConj E z = 0)

def IsIota {n : ℕ} (z : E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Prop :=
  IsSplitAt w ∨ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
    g.val⁻¹ * (snd g.val).map s = algebraMap E (w.adicCompletion E) z • Phi _ n ∧
    (snd g.val)⁻¹ * g.val.map s = (algebraMap E (w.adicCompletion E) z)⁻¹ • Phi _ n

def FixedIota {n : ℕ} (σ : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ x ∈ locU n w, g * cLoc w x * g⁻¹ ∈ GlobalTheory.LFun.KGL w n →
    (∀ i j, snd (g * cLoc w x * g⁻¹).val i j ∈ w.adicCompletionIntegers E) → RU E n x φ = φ

end UpperTheory.V.Lit.Desc

namespace UpperTheory.V.Lit

open Desc

def NTDescent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ z : E, IsZeta n z →
    ∀ wt : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → HeightOneSpectrum (𝓞 E),
      (∀ v, (wt v).under (𝓞 (maximalRealSubfield E)) = v) →
    ∀ g : ∀ v, GL (Fin n) ((wt v).adicCompletion E), (∀ v, IsIota z (wt v) (g v)) →
    ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ v, v ∉ S → FixedIota σ (wt v) (g v)) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

end UpperTheory.V.Lit
