import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem selFam_length_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.subtype_injective _)
    f.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective _ (Submodule.subtype_injective _))

private theorem selFam_abs {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {ι : Type} [Fintype ι]
    {Y Z : ι → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)]
    (A B : Submodule R X) (p : ∀ i, X →ₗ[R] Y i) (q : ∀ i, Y i →ₗ[R] Z i)
    (h1 : ∀ i, ∀ x ∈ A, q i (p i x) = 0) (h2 : ∀ x ∈ A, (∀ i, p i x = 0) → x ∈ B) :
    Module.length R A ≤ Module.length R B + ∑ i, Module.length R (LinearMap.ker (q i)) := by
  let f : A →ₗ[R] (∀ i, LinearMap.ker (q i)) :=
    LinearMap.pi fun i => LinearMap.codRestrict _ ((p i).comp A.subtype) (fun x => h1 i x.1 x.2)
  have hk : ∀ x : LinearMap.ker f, (A.subtype.comp (LinearMap.ker f).subtype) x ∈ B := fun x =>
    h2 x.1.1 x.1.2 fun i => congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 x.2) i)
  have := selFam_length_le f (LinearMap.codRestrict _ _ hk) (by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1))
  rwa [Module.length_pi_of_fintype] at this

private theorem selFam_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U D D' : Subgroup G) (u : G) (hu : u ∈ U) (hux : ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D) (z : Z1U ρ U)
    (hi : resU ρ (inf_le_left : U ⊓ D ≤ U) (Submodule.Quotient.mk z) = 0) :
    ∃ m, ∀ x : U, x.1 ∈ D' → z.1 x = ρ x m - m := by
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ _ z).1 hi
  refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun x hx => ?_⟩
  have hy : u⁻¹ * x.1 * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) x.2) hu
  have h1 : z.1 ⟨u⁻¹ * x.1 * u, hy⟩ = ρ (u⁻¹ * x.1 * u) m - m := hm ⟨_, hy, hux x.1 ⟨x.2, hx⟩⟩
  have e1 : (⟨u, hu⟩ : U) * ⟨_, hy⟩ = x * ⟨u, hu⟩ := Subtype.ext (by simp [mul_assoc])
  have e2 := congrArg z.1 e1
  rw [z.2.2, z.2.2] at e2
  have e3 : z.1 ⟨u, hu⟩ + ρ u (z.1 ⟨_, hy⟩) = z.1 x + ρ x (z.1 ⟨u, hu⟩) := e2
  have e4 : ρ u (ρ (u⁻¹ * x.1 * u) m) = ρ x (ρ u m) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [h1, map_sub, e4] at e3
  rw [eq_sub_of_add_eq e3.symm, map_sub]
  abel

theorem UpperTheory.V.Chr.selFam :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
          [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U : Subgroup G) (𝒟 𝒟' : Set (Subgroup G)) (ι : Type) [Fintype ι] (I D : ι → Subgroup G) (h : ∀ i, I i ≤ D i),
          (∀ i, I i ∈ 𝒟) → (∀ D' ∈ 𝒟', D' ∈ 𝒟 ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
          Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U 𝒟') +
            ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_left U (h i)))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U 𝒟 𝒟' ι _ I D h hI hc
  refine selFam_abs (LocSel ρ U 𝒟) (LocSel ρ U 𝒟') (fun i => resU ρ (inf_le_left : U ⊓ D i ≤ U))
    (fun i => resU ρ (inf_le_inf_left U (h i))) (fun i x hx => ?_) (fun x hx hi => ?_)
  · exact (resU_resU ρ _ _ x).trans (mem_locSel.1 hx (I i) (hI i))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine mk_mem_locSel.2 fun D' hD' => ?_
    rcases hc D' hD' with hle | ⟨i, u, hu, hux⟩
    · exact mk_mem_locSel.1 hx D' hle
    · exact selFam_conj ρ U (D i) D' u hu hux z (hi i)
