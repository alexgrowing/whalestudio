import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped nonZeroDivisors

theorem isFractionRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsFractionRing O C := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hv.hom_inj
  refine IsFractionRing.of_field O C fun z => ?_
  obtain ⟨a, h | h⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap z
  · exact ⟨a, 1, by simp [h]⟩
  · exact ⟨1, a, by simp [← h]⟩

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (M : Submodule A Ω) (hM : M.IsLattice K) : finrank A M = finrank K Ω := by
  haveI : IsLocalizedModule A⁰ M.subtype :=
    { map_units := fun s => by
        rw [← (Algebra.lsmul A (A := K) A Ω).commutes]
        exact (IsLocalization.map_units K s).map _
      surj := fun y => by
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K (M : Set Ω) y
          (by rw [hM.span_eq_top]; trivial)
        rw [Submodule.span_eq] at ht
        exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.val_injective h]⟩ }
  rw [← IsLocalizedModule.finrank_eq A⁰ M.subtype le_rfl]
  exact (IsLocalization.finrank_eq K A⁰ le_rfl).symm

theorem rankAtStalk_eq_finrank {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) : rankAtStalk M p = finrank A M := by
  have hp : p.asIdeal.primeCompl ≤ A⁰ := p.asIdeal.primeCompl_le_nonZeroDivisors
  rw [rankAtStalk, IsLocalization.finrank_eq _ p.asIdeal.primeCompl hp,
    IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp]

theorem finrank_baseChange_flat {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    [Algebra A O] (M : Type) [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.Finite A M] :
    finrank O (O ⊗[A] M) = finrank A M := by
  rw [← rankAtStalk_eq_finrank (O ⊗[A] M) (⊥ : PrimeSpectrum O), rankAtStalk_baseChange,
    rankAtStalk_eq_finrank]

theorem exists_lift {A O : Type} [CommRing A] [CommRing O] [Algebra A O] {M : Type} [AddCommGroup M]
    [Module A M] {Ω' : Type} [AddCommGroup Ω'] [Module O Ω'] (ι : M →ₛₗ[algebraMap A O] Ω') :
    ∃ j : O ⊗[A] M →ₗ[O] Ω', (∀ x, j (1 ⊗ₜ x) = ι x) ∧
      LinearMap.range j = Submodule.span O (Set.range ι) := by
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι, map_smul' := fun a x => ι.map_smulₛₗ a x }
  refine ⟨f.liftBaseChange O, fun x => by simp [f], ?_⟩
  rw [LinearMap.range_liftBaseChange]
  rfl

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsLattice K → Module.Projective A M → L.IsLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hP hL hspan hrk
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := isFractionRing_of_integers hv
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  obtain ⟨j, hj, hr⟩ := exists_lift ι
  rw [hspan] at hr
  refine ⟨j, ?_, hr, hj⟩
  have h1 : finrank O (O ⊗[A] M) = finrank O (LinearMap.range j) := by
    rw [finrank_baseChange_flat, finrank_lattice M hM, hr, finrank_lattice L hL, hrk]
  have h2 := j.rank_range_add_rank_ker
  haveI : Module.Finite O (LinearMap.range j) := inferInstance
  rw [← finrank_eq_rank O (O ⊗[A] M), ← finrank_eq_rank O (LinearMap.range j), h1] at h2
  have h3 : Module.rank O (LinearMap.ker j) = 0 := by
    rw [add_comm] at h2
    exact (Cardinal.add_nat_inj _).1 (h2.trans (zero_add _).symm)
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.rank_eq_zero).1 h3

end PositivityTheory.HtPt.Gb
