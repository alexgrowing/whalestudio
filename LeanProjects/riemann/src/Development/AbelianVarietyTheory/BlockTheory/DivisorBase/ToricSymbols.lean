import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def lamF (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def IsTwistedSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (ψ : PicO c →* ℂˣ) (T : ℂ) : Prop :=
  Finite (PicO c) ∧ ∃ S : PicO c → ℂ → ℂ, (∀ q, IsLatSum φ (2 * s) κ (lattice c q.out) (S q)) ∧
    T = ∑ᶠ q : PicO c, ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0

def conjChar {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) (ψ : PicO c →* ℂˣ) : PicO c →* ℂˣ :=
  (Units.map g.toRingHom.toMonoidHom).comp ψ

def classOf (K : Type) [Field K] [NumberField K] [Algebra K E] (c : Ideal (OF E)) (t : (Af K)ˣ) : PicO c :=
  QuotientGroup.mk (Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t)

def IsSymbol {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (art : Ideles K →* Gab K Ω) (t : (Af K)ˣ)
    (σ : Formalism.ConjugateSelfDual.G K Ω) : Prop :=
  (art (finIdele K t))⁻¹ = toAb K Ω σ

def ToricRatioConjugates : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = ι) →
    1 ≤ s → (∀ i, 1 ≤ κ i) → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 ∅ χ →
    ∃ (T₀ : ℂ) (T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ),
      IsToricSum φ s κ 𝔣 χ T₀ ∧ T₀ ≠ 0 ∧ (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) ∧
      (∀ ψ, IsAlgebraic ℚ (T ψ / T₀)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ),
          (∀ i x, g (φ i x) = φ i x) → (∀ y, g (lamF χ s y) = lamF χ s y) →
          (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
          ∀ ψ : PicO (condQ 𝔣 Q) →* ℂˣ,
            g (T ψ / T₀) =
              ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) ∧
            IsOfFinOrder (conjChar g ψ (classOf K (condQ 𝔣 Q) t))

@[simp] theorem coe_conjChar {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) (ψ : PicO c →* ℂˣ) (q : PicO c) :
    ((conjChar g ψ q : ℂˣ) : ℂ) = g (ψ q) := rfl

theorem IsTwistedSum.unique {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} {ψ : PicO c →* ℂˣ}
    {T T' : ℂ} (h : IsTwistedSum φ s κ c χ ψ T) (h' : IsTwistedSum φ s κ c χ ψ T') : T = T' := by
  obtain ⟨_, S, hS, rfl⟩ := h
  obtain ⟨_, S', hS', rfl⟩ := h'
  have : S = S' := funext fun q => (hS q).unique (hS' q)
  rw [this]

theorem isTwistedSum_iff_isToricSum {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ ξ : HChar E}
    {ψ : PicO c →* ℂˣ} (h : ∀ y, finPart ξ y = ψ (QuotientGroup.mk y)) (T : ℂ) :
    IsTwistedSum φ s κ c χ ψ T ↔ IsToricSum φ s κ c (χ * ξ) T := by
  have key : ∀ q : PicO c, ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ =
      ((finPart (χ * ξ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ := fun q => by
    rw [finPart_mul, h, QuotientGroup.out_eq', lamF, Units.val_mul]
    simp only [mul_inv]
    ring
  simp only [IsTwistedSum, IsToricSum, key]

example {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} (T : ℂ) :
    IsTwistedSum φ s κ c χ 1 T ↔ IsToricSum φ s κ c χ T := by
  simp [IsTwistedSum, IsToricSum, lamF]

example (K : Type) [Field K] [NumberField K] [Algebra K E] (c : Ideal (OF E)) (a : Kˣ) :
    classOf K c (Units.map (algebraMap K (Af K)).toMonoidHom a) = 1 := by
  rw [classOf, QuotientGroup.eq_one_iff]
  refine Subgroup.mem_sup_left ⟨Units.map (algebraMap K E).toMonoidHom a, Units.ext ?_⟩
  exact (GlobalTheory.AdeleBaseChange.adMap_algebraMap (a : K)).symm

example {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {art : Ideles K →* Gab K Ω} (h : IsGlobalArtin art)
    (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    ∃ σ : Formalism.ConjugateSelfDual.G K Ω, Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ ∧ IsSymbol art (unifAt v) σ := by
  obtain ⟨σ, hσ, e⟩ := (h.frob v A hA _).1 ⟨_, Formalism.L2.Host.unif_spec v, rfl⟩
  refine ⟨σ, hσ, ?_⟩
  rw [map_inv, inv_eq_iff_eq_inv] at e
  exact e.symm

end GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
