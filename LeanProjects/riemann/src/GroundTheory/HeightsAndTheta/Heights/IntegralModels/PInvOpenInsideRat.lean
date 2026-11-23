import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInsideRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

theorem isLocallyNoetherian_of_locallyOfFiniteType_specZ {X : Scheme.{0}} (f : X ⟶ SpecZ)
    [LocallyOfFiniteType f] : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  have hZ : IsNoetherianRing Γ(SpecZ, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := SpecZ) ⟨⊤, isAffineOpen_top _⟩
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hφ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ U e
  let _ := (f.appLE ⊤ U.1 e).hom.toAlgebra
  have : Algebra.FiniteType Γ(SpecZ, ⊤) Γ(X, U) := hφ
  exact Algebra.FiniteType.isNoetherianRing Γ(SpecZ, ⊤) Γ(X, U)

theorem mem_range_baseChangeMap_rat_of_asIdeal_eq_bot {X : Scheme.{0}} (f : X ⟶ SpecZ) (x : X)
    (hx : (f.base x).asIdeal = ⊥) : x ∈ Set.range (baseChangeMap f ℚ) := by
  let y : Spec (CommRingCat.of ℚ) := ⟨⊥, Ideal.isPrime_bot⟩
  have h : f.base x = (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))).base y := by
    apply PrimeSpectrum.ext
    rw [hx]
    change ⊥ = Ideal.comap (Int.castRingHom ℚ) ⊥
    exact (Ideal.comap_bot_of_injective _ (Int.cast_injective (α := ℚ))).symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  exact ⟨z, hz⟩

theorem InvOpenInsideRat.proof : InvOpenInsideRat.Statement := by
  intro X f _ _ W hW
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isLocallyNoetherian_of_locallyOfFiniteType_specZ f
  have : IsNoetherian X := {}

  have hgen : ∀ x : X, x ∉ W → (f.base x).asIdeal ≠ ⊥ := by
    intro x hx h
    have h1 := hW (mem_range_baseChangeMap_rat_of_asIdeal_eq_bot f x h)
    rw [Scheme.Opens.range_ι] at h1
    exact hx h1
  obtain ⟨S, hSi, hS⟩ := NoetherianSpace.exists_finset_irreducible
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)
  have hSZ : ∀ k ∈ S, (k : Set X) ⊆ (W : Set X)ᶜ := by
    intro k hk
    have h1 : k ≤ S.sup id := Finset.le_sup (f := id) hk
    rw [← hS] at h1
    exact h1
  have claim : ∀ k ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ (k : Set X), (n : ℤ) ∈ (f.base x).asIdeal := by
    intro k hk
    have hirr : IsIrreducible (k : Set X) := hSi ⟨k, hk⟩
    have hg : IsGenericPoint hirr.genericPoint (k : Set X) :=
      hirr.isGenericPoint_genericPoint k.isClosed
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hgen _ (hSZ k hk hg.mem))
    refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun x hx => ?_⟩
    have hle : (f.base hirr.genericPoint).asIdeal ≤ (f.base x).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hx).map f.base.hom.continuous)
    exact Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) (hle hn)
  choose! n hn using claim
  refine ⟨∏ k ∈ S, n k, Finset.prod_pos fun k hk => (hn k hk).1, ?_⟩
  intro x hx
  by_contra hxW
  have hxS : x ∈ ((S.sup id : Closeds X) : Set X) := by rw [← hS]; exact hxW
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hxS
  obtain ⟨k, hk, hxk⟩ := hxS
  apply (mem_invOpen f _ x).mp hx
  have hdvd : ((n k : ℕ) : ℤ) ∣ ((∏ k ∈ S, n k : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem n hk)
  exact Ideal.mem_of_dvd _ hdvd ((hn k hk).2 x hxk)

end

end GroundTheory.Heights₂.Heights.Model
