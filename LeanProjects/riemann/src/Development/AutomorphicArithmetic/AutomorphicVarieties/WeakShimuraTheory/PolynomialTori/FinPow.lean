import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

open IsLocalRing

private theorem exists_fg_sup_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

theorem UpperTheory.V.Ws.Po.finPow {O A : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing A] [IsLocalRing A] [Algebra O A] [IsNoetherianRing A]
    (hloc : (maximalIdeal O).map (algebraMap O A) ≤ maximalIdeal A)
    (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ maximalIdeal A) (n : ℕ)
    (hn : maximalIdeal A ^ n ≤ (maximalIdeal O).map (algebraMap O A)) : Module.Finite O A := by
  haveI : IsHausdorff (maximalIdeal A) A := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal A).ne_top
  haveI : IsHausdorff (maximalIdeal O) A := IsHausdorff.of_map hloc
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) A).2 ?_
  obtain ⟨N, hN, hx⟩ := exists_fg_sup_pow (maximalIdeal A) hres n
  have : N.map (maximalIdeal O • (⊤ : Submodule O A)).mkQ = ⊤ := by
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := hx x
    have h2 : x - y ∈ maximalIdeal O • (⊤ : Submodule O A) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    have := Submodule.add_mem_sup h2 hy
    rwa [sub_add_cancel] at this
  exact ⟨this ▸ hN.map _⟩
