import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_endx

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem mem_gsOpenSubgroup_placesOver_iff {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (K' L : FiniteSubfield) [Fact (K ≤ K')] [Fact (K ≤ L)] [Fact (K' ≤ L)]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S))
    (τ : galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) :
    τ ∈ gsOpenSubgroup (placesOver S) hL'' ↔
      ((((gsBaseChange S hK').symm τ : (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
        galUnramifiedOutside K.1 ℚ̄ S) ∈ gsOpenSubgroup S hL) := by
  rw [mem_gsOpenSubgroup_iff, mem_gsOpenSubgroup_iff]
  refine forall_congr' fun x => ?_
  rw [Subtype.ext_iff, Subtype.ext_iff, coe_gsBaseChange_symm_apply]
  exact Iff.rfl

theorem ending_lemmaX (hX : GlobalEulerCharCoprime) (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) (hc : ℓ ≠ 2 ∨ NumberField.IsTotallyComplex L.1) :
    ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1 := by
  intro K' _ hK' hle _ hcop ιr'
  have hKL : K' ≤ L := by
    intro x hx
    refine mem_of_forall_gsOpenSubgroup_fixes S hL ⟨x, hK' ⟨x, hx⟩⟩ fun σ hσ => ?_
    have h1 := (mem_gsOpenSubgroup_iff S hK' σ).1 (hle hσ) ⟨x, hx⟩
    exact h1
  have : Fact (K' ≤ L) := ⟨hKL⟩
  have hL'' : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K'.1 ℚ̄ (placesOver S) :=
    fun x => mem_of_restrictScalars_eq' (restrictScalars_maxUnramifiedOutside_eq S hK') (hL x)
  have hcomap : (gsOpenSubgroup (placesOver S) hL'' : Subgroup (galUnramifiedOutside K'.1 ℚ̄ (placesOver S))) =
      ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf
        (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).comap
        (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom := by
    ext τ
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' τ
  haveI hfin : Finite (resTo S K' hK' M) := (inferInstanceAs (Finite M))
  refine hX K' (placesOver S) (placesOver_finite hS) ℓ (natCast_not_mem_of_not_mem_placesOver hSℓ) L hL''
    ?_ ?_ hζ hc ιr' (resTo S K' hK' M) ?_ ?_
  · rw [hcomap]
    exact (hN.subgroupOf _).comap _
  · rw [hcomap, Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)]
    exact hcop
  · intro m
    exact hℓ m
  · intro g hg
    exact htriv _ ((mem_gsOpenSubgroup_placesOver_iff S K' L hK' hL hL'' g).1 hg)

end PositivityTheory.Lit1.GEN.W_endx
