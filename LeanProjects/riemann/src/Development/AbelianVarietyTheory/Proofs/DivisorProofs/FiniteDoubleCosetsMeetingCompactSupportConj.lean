import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem doubleCoset_finite_of_compactSupport : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  intro G _ _ _ T K y f hK hf hfin
  have hCc : IsCompact ((fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((K : Set G) ×ˢ tsupport f)) :=
    (hK.prod hf.isCompact).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  refine (hfin _ hCc).subset ?_
  rintro q ⟨k, hk, hne⟩
  refine ⟨(k, (Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)), ⟨hk, subset_tsupport f hne⟩, ?_⟩
  group

end GlobalTheory
