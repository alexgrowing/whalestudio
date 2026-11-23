import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun

namespace UpperTheory.V.Cj.S

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

abbrev locOf {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  ρ.comp (locGL E a w)

variable [IsTotallyComplex E]

def HasCap (φ : Sm E a) (m : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ t, Multiset.card (m t) = a ∧ ∀ u, cap t u φ = ((m t).map (u + ·)).prod • φ

theorem hasCap_oneFn : HasCap (oneFn E a) fun _ => Finset.univ.val.map fun k : Fin a => ((a : ℂ) - 1) / 2 - (k : ℕ) :=
  fun t => ⟨by simp, fun u => by rw [cap_oneFn, Multiset.map_map]; rfl⟩

def CuspSupport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (τ : SmIrr (GL (Fin a) (Af E))) (m : (E →+* ℂ) → Multiset ℂ) (j : τ.V →ₗ[ℂ] Sm E a), j ≠ 0 →
      (∀ g v, j (τ.ρ g v) = finRep E a g (j v)) → (∀ v, IsAutForm (j v)) → (∀ v, HasCap (j v) m) →
      (∃ π : CuspSub E a, UpperTheory.V.Af.IsFinComp π τ ∧ ∀ t, π.HasInfChar t (m t)) ∨
        ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (π : ∀ i, CG E (n i)) (μ : ι → (E →+* ℂ) → Multiset ℂ),
          2 ≤ Fintype.card ι ∧ (∀ i, 1 ≤ n i) ∧ (∀ i, n i < a) ∧ ∑ i, n i = a ∧
          (∀ i t, (π i).HasInfChar t (μ i t)) ∧ (∀ t, ∑ i, μ i t = m t) ∧
          ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : ι → Multiset ℂˣ,
            (∀ i, (π i).HasSat w (B i)) ∧ HasSatGL w (locOf τ.ρ w) (∑ i, B i)

end UpperTheory.V.Cj.S
