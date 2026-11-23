import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
import GroundTheory.ProfiniteCohomology.PoincareDuality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit DirectSum groupCohomology

open scoped Pointwise NumberField.LiesOver

noncomputable section

section Infinite

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

include v in

theorem subsingleton_groupCohomology_one_infiniteDecomposition :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 1) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ c : groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 1, c = 0 by rw [h a, h b]
  intro c
  refine H1_induction_on c fun x => (H1π_eq_zero_iff _).2 ?_
  have hc := isMulCocycle₁_of_mem_cocycles₁ _ x.2
  let e := infiniteDecompositionMulEquiv v w
  let f : Gal(w.Completion/v.Completion) → (w.Completion)ˣ := fun τ => Additive.toMul (x (e.symm τ))
  have hf : IsMulCocycle₁ f := fun τ₁ τ₂ => by
    have h1 := hc (e.symm τ₁) (e.symm τ₂)
    simp only [f, map_mul]
    refine h1.trans ?_
    congr 1
    apply Units.ext
    exact congrArg (fun τ : Gal(w.Completion/v.Completion) =>
      τ ((Additive.toMul (α := (w.Completion)ˣ) (x (e.symm τ₂)) : (w.Completion)ˣ) : w.Completion))
      (e.apply_symm_apply τ₁)
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine (coboundariesOfIsMulCoboundary₁ (G := MulAction.stabilizer Gal(L/K) w)
    (M := (w.Completion)ˣ) (f := fun σ => Additive.toMul (x σ)) ⟨β, fun σ => ?_⟩).2
  have h := hβ (e σ)
  simp only [f, MulEquiv.symm_apply_apply] at h
  refine Eq.trans ?_ h
  congr 1

include v in

theorem isCyclic_infiniteDecomposition : IsCyclic (MulAction.stabilizer Gal(L/K) w) := by
  have h := natCard_infiniteDecompositionGroup v w
  rcases Nat.lt_or_ge (Module.finrank v.Completion w.Completion) 2 with h2 | h2
  · have h1 : Nat.card (MulAction.stabilizer Gal(L/K) w) ≤ 1 := by omega
    have : Subsingleton (MulAction.stabilizer Gal(L/K) w) :=
      (Finite.card_le_one_iff_subsingleton).1 h1
    exact isCyclic_of_subsingleton
  · have hle : Module.finrank v.Completion w.Completion ≤ 2 := by
      have hc := NumberField.InfinitePlace.card_stabilizer (k := K) (w := w)
      rw [← h, hc]
      split_ifs <;> omega
    have h2' : Nat.card (MulAction.stabilizer Gal(L/K) w) = 2 := by omega
    exact isCyclic_of_prime_card (p := 2) h2'

include v in
set_option maxHeartbeats 1000000 in

theorem subsingleton_cohomology_three_infiniteDecomposition :
    Subsingleton (cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
      (w.Completion)ˣ) 3) := by
  classical
  haveI := isCyclic_infiniteDecomposition v w
  letI : CommGroup (MulAction.stabilizer Gal(L/K) w) := IsCyclic.commGroup
  haveI : Fintype (MulAction.stabilizer Gal(L/K) w) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w)
  haveI := subsingleton_groupCohomology_one_infiniteDecomposition v w
  let A := Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) (w.Completion)ˣ
  let e : cohomology A 3 ≅ groupCohomology A 1 :=
    cohomologyIsoGroupCohomology A 3 ≪≫ Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 3 ⟨1, rfl⟩ ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 ⟨0, rfl⟩).symm
  exact e.toLinearEquiv.injective.subsingleton

end Infinite

section Global

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem subsingleton_cohomology_three_galUnitsZ_adicCompletion {K : FiniteSubfield}
    (v : HeightOneSpectrum (𝓞 K.1)) :
    Subsingleton (cohomology (galUnitsZ (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))) 3) := by
  have h1 := subsingleton_cohomology_three_galUnits_open (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1)) ⊤
  have h2 : Subsingleton (cohomology (galUnits.{0} (v.adicCompletion K.1)
      (AlgebraicClosure (v.adicCompletion K.1))) 3) :=
    (bijective_cohomologyRes_top _ 3).1.subsingleton
  exact (cohomologyULiftIntAddEquiv (galUnits.{0} (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))) 3).symm.injective.subsingleton

variable {K : FiniteSubfield}

theorem subsingleton_localGaloisCohomology_three (ι : LocalEmbeddings K) (v : Place K.1) :
    Subsingleton (localGaloisCohomology K 3 v) := by
  rcases v with v | v
  · have key : ∀ t : localGaloisCohomology K 3 (.inl v), t = 0 := fun t => by
      obtain ⟨p, z, rfl⟩ := (ι.localLimit 3).exists_infl (.inl v) t
      haveI : (ι.places.inf v p).1.LiesOver v := (ι.places.inf v p).2
      have hs := subsingleton_cohomology_three_infiniteDecomposition (K := K.1) (L := p.1.1) v
        (ι.places.inf v p).1
      have hz : z = 0 := hs.elim _ _
      rw [hz, map_zero]
      rfl
    exact ⟨fun a b => (key a).trans (key b).symm⟩
  · exact subsingleton_cohomology_three_galUnitsZ_adicCompletion v

theorem subsingleton_cohomology_three_limitRep : Subsingleton (cohomology (limitRep K) 3) := by
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  have h : ∀ ζ : ⨁ v : Place K.1, localGaloisCohomology K 3 v, ζ = 0 := fun ζ => by
    ext v
    haveI := subsingleton_localGaloisCohomology_three ι v
    exact Subsingleton.elim _ _
  haveI : Subsingleton (⨁ v : Place K.1, localGaloisCohomology K 3 v) :=
    ⟨fun a b => (h a).trans (h b).symm⟩
  exact (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 3)).injective.subsingleton

end Global

end

end GroundTheory.ProfCoh
