import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkEndx

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_endn

open PositivityTheory.Lit1.GEN.W_killed_a PositivityTheory.Lit1.GEN.W_endx

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ending_narrow (H : RatioOne 2 (fun K => NumberField.IsTotallyComplex K.1)) (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (h2 : ∀ m : M, 2 • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (htc : NumberField.IsTotallyComplex L.1) :
    ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index 2 →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1  := by
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
  have hidx : Module.finrank K'.1 L.1 =
      ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf
        (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index := by
    rw [← index_gsOpenSubgroup (placesOver S) hL'', hcomap,
      Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)]
  have hodd : Odd (Module.finrank K'.1 L.1) := by
    rw [hidx]
    exact Nat.coprime_two_right.1 hcop
  have htc' : NumberField.IsTotallyComplex K'.1 := TotallyComplexOfOdd.isTotallyComplex_of_odd K' L hodd htc
  haveI hfin : Finite (resTo S K' hK' M) := (inferInstanceAs (Finite M))
  exact H K' (placesOver S) (placesOver_finite hS) (fun w hw => mem_placesOver_of_natCast_mem hS2 hw) htc' ιr'
    (resTo S K' hK' M) ⟨1, fun m => by rw [pow_one]; exact h2 m⟩

end PositivityTheory.Lit1.GEN.W_endn
