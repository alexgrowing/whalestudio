import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.AlgMemCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.CutHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LinPartApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SmHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NzCoeffMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FinHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.main_cotSpan {O A ι : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (x : A →ₐ[O] O) (F : ι → A) : cotSpan x F = (Submodule.span O (Set.range F)).map (satSq x).mkQ := by
  unfold cotSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

private theorem UpperTheory.V.Alg.M.main_span {O A ι : Type} [CommRing O] [CommRing A] [Algebra O A]
    {F F' : ι → A} (h : Submodule.span O (Set.range F') = Submodule.span O (Set.range F)) :
    Ideal.span (Set.range F') = Ideal.span (Set.range F) := by
  have key : ∀ {G G' : ι → A}, Submodule.span O (Set.range G') ≤ Submodule.span O (Set.range G) →
      Ideal.span (Set.range G') ≤ Ideal.span (Set.range G) := by
    intro G G' hle
    rw [Ideal.span_le]
    intro y hy
    have h1 : y ∈ Submodule.span O (Set.range G) := hle (Submodule.subset_span hy)
    have h2 : Submodule.span O (Set.range G) ≤ (Ideal.span (Set.range G)).restrictScalars O :=
      Submodule.span_le.mpr Ideal.subset_span
    exact h2 h1
  exact le_antisymm (key h.le) (key h.ge)

theorem UpperTheory.V.Alg.M.main_holds :
    LemmaM := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ x hW r s r' s' m Q a h1 h2 h3 h4 h5
  haveI := hW.co
  obtain ⟨hr, hsm, hF, hG, hZ⟩ := h1
  obtain ⟨hfin, hrk⟩ := rk_holds O A 𝒜 x hW _ hsm
  have hrk' : Module.finrank O (cotLat x 𝒜 (-1)) = r := by rw [hrk]; simp [mDims]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨F', y, c, hspan, hy, hlast, hlen⟩ :=
    sm_holds O A 𝒜 x (hW.fixed _ (by norm_num)) r Q.F Q.hF hfin hrk' hF ϖ hϖ
  have hF'mem : ∀ i, F' i ∈ 𝒜 (-1) := fun i => by
    have : F' i ∈ Submodule.span O (Set.range Q.F) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Q.hF j)) this
  let Q' : Eqns 𝒜 x r s r' s' m := { Q with F := F', hF := hF'mem }
  have hI : Q'.ideal = Q.ideal := by
    simp only [Eqns.ideal, Ideal.span_union]
    rw [show Ideal.span (Set.range Q'.F) = Ideal.span (Set.range Q.F) from main_span hspan]
  have hF' : SpansCot x 𝒜 (-1) Q'.F := by
    intro p hp
    obtain ⟨d, hd, hp'⟩ := hF p hp
    refine ⟨d, hd, ?_⟩
    rw [main_cotSpan] at hp' ⊢
    exact hspan ▸ hp'
  have h1' : M1 Q' := ⟨hr, hsm, hF', hG, hZ⟩
  obtain ⟨τ, _, wt, φ, hφ, hφZ, hcard⟩ := cut_holds O A 𝒜 x hW r s r' s' m Q' h1'
  obtain ⟨a', ha'0, ha'I, ha'x, ha'φ⟩ := nz_holds O A 𝒜 x hW r s r' s' m Q' τ wt φ hφ
    (by rw [hcard]; simpa [mDims] using hr) (by rw [hcard]; simp [mDims]) hF' a h5.1
  rw [hI] at ha'I
  have hval : ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ → ξ a' = ξ a := fun ξ hξ => by
    have := hξ _ ha'I
    rwa [map_sub, sub_eq_zero] at this
  have h5' : M5 𝒜 K x Q.ideal a' :=
    ⟨ha'0, ha'x.trans h5.2.1, fun ξ hξ ht => by rw [hval ξ hξ]; exact h5.2.2 ξ hξ ht⟩
  refine ⟨?_, by rw [hlen]; exact ENat.coe_ne_top _, fun T hT => ?_⟩
  · exact fin_holds O K A 𝒜 x hW _ (hom_holds O A 𝒜 x hW r s r' s' m Q).1 h2 h4
  · have := core_holds O K v hv A 𝒜 x hW r s r' s' m Q' τ wt φ hφ hφZ hr hcard ϖ hϖ y c hy hlast hF' hG
      (hI ▸ h2) (hI ▸ h3) (hI ▸ h4) a' (hI ▸ h5') ha'φ T (hI ▸ hT)
    rw [hlen, ENat.toNat_coe]
    rwa [Finset.sum_congr rfl fun ξ hξ => congrArg v (hval ξ (hT.1 ξ hξ).1)] at this
