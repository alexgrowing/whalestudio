import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitM

def SplitRigidity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n c c' : ℕ) (N : Fin c → ℕ) (N' : Fin c' → ℕ)
    (h : ∑ i, N i = n) (h' : ∑ j, N' j = n)
    (V : ∀ i, Submodule ℂ (Sm E (N i))) (V' : ∀ j, Submodule ℂ (Sm E (N' j)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (σ' : ∀ j (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N' j)) (w.adicCompletion E))),
    (∀ i, 0 < N i) → (∀ j, 0 < N' j) →
    (∀ i, IsDiscrete (V i)) → (∀ j, IsDiscrete (V' j)) → (∀ i, IsCsdGL (V i)) → (∀ j, IsCsdGL (V' j)) →
    (∀ i w, IsLocCompGL (V i) w (σ i w)) → (∀ j w, IsLocCompGL (V' j) w (σ' j w)) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      Nonempty (Representation.Equiv (locProd h w (σ · w)) (locProd h' w (σ' · w)))) →
    ∃ s : Fin c ≃ Fin c', ∀ i, (⟨N i, V i⟩ : Σ a, Submodule ℂ (Sm E a)) = ⟨N' (s i), V' (s i)⟩

def AllPlaceRigidity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n c c' : ℕ) (N : Fin c → ℕ) (N' : Fin c' → ℕ)
    (h : ∑ i, N i = n) (h' : ∑ j, N' j = n)
    (V : ∀ i, Submodule ℂ (Sm E (N i))) (V' : ∀ j, Submodule ℂ (Sm E (N' j)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (σ' : ∀ j (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N' j)) (w.adicCompletion E))),
    (∀ i, 0 < N i) → (∀ j, 0 < N' j) →
    (∀ i, IsDiscrete (V i)) → (∀ j, IsDiscrete (V' j)) → (∀ i, IsCsdGL (V i)) → (∀ j, IsCsdGL (V' j)) →
    (∀ i w, IsLocCompGL (V i) w (σ i w)) → (∀ j w, IsLocCompGL (V' j) w (σ' j w)) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, Nonempty (Representation.Equiv (locProd h w (σ · w)) (locProd h' w (σ' · w)))) →
    ∃ s : Fin c ≃ Fin c', ∀ i, (⟨N i, V i⟩ : Σ a, Submodule ℂ (Sm E a)) = ⟨N' (s i), V' (s i)⟩

def IsRegAlg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) {a : ℕ} (V : Submodule ℂ (Sm E a))
    (τ : E →+* ℂ) : Prop :=
  ∃ m : Multiset ℂ, HasInfCharGL V τ m ∧ m.Nodup ∧ ∀ x ∈ m, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2

def SplitRigidityRegAlg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n c c' : ℕ) (N : Fin c → ℕ) (N' : Fin c' → ℕ)
    (h : ∑ i, N i = n) (h' : ∑ j, N' j = n)
    (V : ∀ i, Submodule ℂ (Sm E (N i))) (V' : ∀ j, Submodule ℂ (Sm E (N' j)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (σ' : ∀ j (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N' j)) (w.adicCompletion E))),
    (∀ i, 0 < N i) → (∀ j, 0 < N' j) →
    (∀ i, IsDiscrete (V i)) → (∀ j, IsDiscrete (V' j)) → (∀ i, IsCsdGL (V i)) → (∀ j, IsCsdGL (V' j)) →
    (∀ i w, IsLocCompGL (V i) w (σ i w)) → (∀ j w, IsLocCompGL (V' j) w (σ' j w)) →
    (∀ i (τ : E →+* ℂ), IsRegAlg n (V i) τ) → (∀ j (τ : E →+* ℂ), IsRegAlg n (V' j) τ) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      Nonempty (Representation.Equiv (locProd h w (σ · w)) (locProd h' w (σ' · w)))) →
    ∃ s : Fin c ≃ Fin c', ∀ i, (⟨N i, V i⟩ : Σ a, Submodule ℂ (Sm E a)) = ⟨N' (s i), V' (s i)⟩

def SplitRigidityCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (m' : κ → ℕ) (π : ∀ i, CG E (m i)) (π' : ∀ j, CG E (m' j)) (s : ι → ℝ) (s' : κ → ℝ),
    (∀ i, 1 ≤ m i) → (∀ j, 1 ≤ m' j) → (∀ i, (π i).IsUnitary) → (∀ j, (π' j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ (B : ι → Multiset ℂˣ) (B' : κ → Multiset ℂˣ), (∀ i, (π i).HasSat w (B i)) ∧ (∀ j, (π' j).HasSat w (B' j)) ∧
        ∑ i, (B i).map (fun α : ℂˣ => (α : ℂ) * (Ideal.absNorm w.asIdeal : ℂ) ^ (-(s i : ℂ))) =
          ∑ j, (B' j).map (fun α : ℂˣ => (α : ℂ) * (Ideal.absNorm w.asIdeal : ℂ) ^ (-(s' j : ℂ)))) →
    ∃ e : ι ≃ κ, ∀ i, (⟨m i, π i⟩ : Σ a, CG E a) = ⟨m' (e i), π' (e i)⟩ ∧ s i = s' (e i)

end GlobalTheory.SplitM
