import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.LevelModulesDefs

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_split

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem isTotallyComplex_of_sq_eq_neg_one {E : Type*} [Field E] (x : E) (hx : x ^ 2 = -1) :
    NumberField.IsTotallyComplex E := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  have hr := InfinitePlace.not_isComplex_iff_isReal.1 hw
  have h := congrArg (InfinitePlace.embedding_of_isReal hr) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hr x)]

set_option maxHeartbeats 800000 in
theorem exists_split (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M] :
    ∃ (L : FiniteSubfield) (hKL : Fact (K ≤ L)),
      haveI := hKL
      ∃ hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S,
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal ∧ (∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) ∧
        (ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) ∧ ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1 := by
  classical
  have hℓ := (Fact.out : ℓ.Prime)

  let W : Set (galUnramifiedOutside K.1 ℚ̄ S) := (M.ρ.ker : Set (galUnramifiedOutside K.1 ℚ̄ S))
  have hWo : IsOpen W := isOpen_ker_ρ M
  have hW1 : (1 : galUnramifiedOutside K.1 ℚ̄ S) ∈ W := M.ρ.ker.one_mem
  obtain ⟨E, hEf, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S) W).1
    (hWo.mem_nhds hW1)
  let bE := Module.finBasis K.1 E

  let n : ℕ := if ℓ = 2 then 4 else ℓ
  have hn0 : n ≠ 0 := by
    by_cases h2 : ℓ = 2
    · simp [n, h2]
    · simp only [n, h2, if_false]; exact hℓ.ne_zero
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := by
    intro v hv hmem
    apply hv
    apply hSℓ v
    by_cases h2 : ℓ = 2
    · subst h2
      have h4 : ((4 : ℕ) : 𝓞 K.1) = ((2 : ℕ) : 𝓞 K.1) * ((2 : ℕ) : 𝓞 K.1) := by push_cast; ring
      simp only [n, if_true] at hmem
      rw [h4] at hmem
      rcases v.isPrime.mem_or_mem hmem with h | h <;> exact h
    · simpa [n, h2] using hmem
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have hξS : ξ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S hn0 hnS hξ.pow_eq_one
  let T : Finset ℚ̄ := insert ξ (Finset.univ.image fun i => ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
  have hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · exact h ▸ hξS
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (bE i : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNn, hN, hTN⟩ := exists_galois_level_finset S T hT
  have hL : ∀ x : N.1, algebraMap N.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S := fun x => hN x x.2
  have hξN : ξ ∈ N.1 := hTN ξ (Finset.mem_insert_self _ _)
  refine ⟨N, hKN, hL, gsOpenSubgroup_normal hL, ?_, ?_, ?_⟩
  ·
    by_cases h2 : ℓ = 2
    · subst h2
      refine ⟨-1, ?_⟩
      exact IsPrimitiveRoot.neg_one 0 (by norm_num)
    · have hξℓ : IsPrimitiveRoot ξ ℓ := by simpa [n, h2] using hξ
      refine ⟨⟨ξ, hξN⟩, IsPrimitiveRoot.of_map_of_injective (f := algebraMap N.1 ℚ̄) ?_
        (algebraMap N.1 ℚ̄).injective⟩
      exact hξℓ
  · by_cases h2 : ℓ = 2
    · right
      have hξ4 : IsPrimitiveRoot ξ 4 := by simpa [n, h2] using hξ
      refine isTotallyComplex_of_sq_eq_neg_one (⟨ξ, hξN⟩ : N.1) ?_
      apply (algebraMap N.1 ℚ̄).injective
      rw [map_pow, map_neg, map_one]
      change ξ ^ 2 = -1
      have h1 : (ξ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hξ4.pow_eq_one
      have h2' : ξ ^ 2 ≠ 1 := hξ4.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
      have h3 : (ξ ^ 2 - 1) * (ξ ^ 2 + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) h2'
      · exact eq_neg_of_add_eq_zero_left h
    · exact Or.inl h2
  ·
    intro g hg
    have hgE : g ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hb : ∀ i, g (bE i : maxUnramifiedOutside K.1 ℚ̄ S) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        intro i
        have hmem : ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1 :=
          hTN _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
        have key := (mem_gsOpenSubgroup_iff S hL g).1 hg (⟨_, hmem⟩ : N.1)
        have he : gsEmbedding (S := S) hL (⟨_, hmem⟩ : N.1) = (bE i : maxUnramifiedOutside K.1 ℚ̄ S) :=
          Subtype.ext (coe_embeddingOfRestrictScalarsEq _ _)
        rw [he] at key
        exact key
      have hsum : x = ∑ i, (bE.repr ⟨x, hx⟩ i) • (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
        have := congrArg (fun e : E => (e : maxUnramifiedOutside K.1 ℚ̄ S)) (bE.sum_repr ⟨x, hx⟩)
        simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
        exact this.symm
      rw [hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ∀ (r : K.1) (y : maxUnramifiedOutside K.1 ℚ̄ S), g (r • y) = r • g y from
        fun r y => g.toLinearEquiv.map_smul r y, hb i]
    have hgW := hEU hgE
    exact MonoidHom.mem_ker.1 hgW

end PositivityTheory.Lit1.GEN.W_split
