import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (b : 𝓞 Ω) : A.valuation (b : Ω) ≤ 1 := by
  have h : IsIntegral A (b : Ω) := b.isIntegral_coe.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_cen {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∃ Q : Ideal (𝓞 Ω), Q.IsPrime ∧ ∀ b : 𝓞 Ω, b ∈ Q ↔ A.valuation (b : Ω) < 1 := by
  let f : 𝓞 Ω →+* A := (algebraMap (𝓞 Ω) Ω).codRestrict A fun b => (A.valuation_le_one_iff _).1 (int_le A b)
  exact ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun b => A.valuation_lt_one_iff (f b)⟩

open GroundTheory.Global in
private theorem restrict_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) [NumberField L] [IsGalois E L] (hL : IsUnramifiedEverywhere E L)
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) (hg : ∀ x, A.valuation x ≤ 1 → A.valuation (g x - x) < 1) :
    AlgEquiv.restrictNormalHom L g = 1 := by
  obtain ⟨Q, hQ, hmem⟩ := exists_cen A
  have hc : ∀ x : 𝓞 L, AlgEquiv.restrictNormalHom L g • x - x ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_comap, map_sub, hmem]
    have := hg _ (int_le A (algebraMap (𝓞 L) (𝓞 Ω) x))
    have e : ((algebraMap (𝓞 L) (𝓞 Ω) (AlgEquiv.restrictNormalHom L g • x) : 𝓞 Ω) : Ω) =
        g (algebraMap (𝓞 L) (𝓞 Ω) x : 𝓞 Ω) := AlgEquiv.restrictNormal_commutes g L x
    rwa [← e] at this
  by_cases hP : Q.under (𝓞 L) = ⊥
  · have h0 : ∀ x : 𝓞 L, AlgEquiv.restrictNormalHom L g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x := fun x =>
      congrArg (algebraMap (𝓞 L) L) (sub_eq_zero.1 ((Submodule.mem_bot _).1 (hP.le (hc x))))
    ext1 y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
    rw [map_div₀, h0, h0, AlgEquiv.one_apply]
  · let w : HeightOneSpectrum (𝓞 L) := ⟨_, inferInstance, hP⟩
    have hwv : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 E) w).asIdeal := ⟨rfl⟩
    have hram := (isUnramifiedIn_iff_ramificationIdx E L _).1
      (hL.1 _) w hwv
    have hI : w.asIdeal.inertia (L ≃ₐ[E] L) = ⊥ := by
      rw [← Subgroup.card_eq_one, natCard_inertia (HeightOneSpectrum.under (𝓞 E) w) w, hram]
    exact Subgroup.mem_bot.1 (hI ▸ hc)

open GroundTheory.Global in
private theorem restrict_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) [NumberField L] [IsGalois E L] (hL : IsUnramifiedEverywhere E L)
    (g : Ω ≃ₐ[E] Ω) (j : Ω →+* ℂ) (hj : ∀ x, j (g x) = starRingEnd ℂ (j x)) :
    AlgEquiv.restrictNormalHom L g = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let j₀ : L →+* ℂ := j.comp (algebraMap _ Ω)
  have hE : ComplexEmbedding.IsReal (j₀.comp (algebraMap E _)) := by
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hj (algebraMap E Ω y)).symm.trans (congrArg j (g.commutes y))
  have hu := hL.2 _ (InfinitePlace.mk j₀) rfl
  rw [InfinitePlace.isUnramified_iff, InfinitePlace.comap_mk, ← InfinitePlace.not_isReal_iff_isComplex,
    InfinitePlace.isReal_mk_iff, InfinitePlace.isReal_mk_iff] at hu
  have hr := ComplexEmbedding.isReal_iff.1 (hu.resolve_right fun h => h hE)
  apply j.injective
  rw [hj]
  exact DFunLike.congr_fun hr ⟨x, hx⟩

theorem UpperTheory.V.Kum.artIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ (A : ValuationSubring Ω), ∀ g ∈ Ine (F := K) A, artCl K Ω g = 1) ∧ ∀ c : G K Ω, IsConjOm c.toRingEquiv → artCl K Ω c = 1 := by
  intro K Ω _ _ _ _ _
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : NumberField (GroundTheory.Global.hilbertClassField K Ω) := NumberField.of_module_finite K _
  have hL := GroundTheory.Global.isUnramifiedEverywhere_hilbertClassField K Ω
  refine ⟨fun A g hg => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom _ g) = 1
    rw [restrict_ine _ hL A g hg.2, map_one]
  · show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom _ c) = 1
    rw [restrict_conj _ hL c j hj, map_one]
