import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeqEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

open CategoryTheory in
private theorem seq_ex (S : ℕ → Type) (hf : ∀ n, Finite (S n)) (hn : ∀ n, Nonempty (S n)) (t : ∀ n, S (n + 1) → S n) :
    ∃ u : ∀ n, S n, ∀ n, t n (u (n + 1)) = u n :=
  _root_.UpperTheory.Reformulated.B.Qj7.seq_ex S hf hn t

theorem UpperTheory.V.Ws.Bl.compat :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), (∀ n, Finite (T ⧸ lev A T n)) → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z) →
          ∃ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) ∧ (∀ n g, redn A T n (z (n + 1) g) = z n g) ∧ (∀ n, redn A T n (y (n + 1)) = y n) ∧ Prim (z 1) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hT hZ hP
  let S : ℕ → Type := fun n =>
    {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) // IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}
  let t : ∀ n, S (n + 1) → S n := fun n p =>
    ⟨(fun g => redn A T n (p.1.1 g), redn A T n p.1.2),
      (redMem A T Γ ρ c N H P n _ _ p.2.1).1,
      (redMem A T Γ ρ c N H P n _ _ p.2.1).2.1 (p.2.2 n.succ_pos)⟩
  have hf : ∀ n, Finite (S n) := fun n => by
    have := hT n
    have h : ((Zn ρ c N H P n) ×ˢ (Set.univ : Set (T ⧸ lev A T n))).Finite := (hZ n).prod Set.finite_univ
    exact (h.subset (fun p (hp : IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)) => ⟨⟨p.2, hp.1⟩, trivial⟩)).to_subtype
  have hn : ∀ n, Nonempty (S n) := fun n => by
    obtain ⟨z, ⟨y, hz⟩, hp⟩ := hP (n + 1) n.succ_pos
    exact ⟨t n ⟨(z, y), hz, fun _ => hp⟩⟩
  obtain ⟨u, hu⟩ := seq_ex S hf hn t
  exact ⟨fun n => (u n).1.1, fun n => (u n).1.2, fun n => (u n).2.1,
    fun n g => congrArg (fun p : S n => p.1.1 g) (hu n),
    fun n => congrArg (fun p : S n => p.1.2) (hu n), (u 1).2.2 Nat.one_pos⟩
