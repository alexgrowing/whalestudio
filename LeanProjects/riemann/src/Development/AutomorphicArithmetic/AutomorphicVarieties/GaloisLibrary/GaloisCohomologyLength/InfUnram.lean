import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllLeInf

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem UpperTheory.V.LDataCardLeFinrank.ine_le_NS {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {S : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {τ : G F Ω} (hτ : τ ∈ Ine (F := F) A) :
    τ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hτ⟩

private theorem UpperTheory.V.LDataCardLeFinrank.vanishAll {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {S : Set (HeightOneSpectrum (𝓞 F))} {R : Type} [CommRing R] {M : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M)
    {f : G F Ω → M} (hf : f ∈ Z1 (rhoS.comp (toGS Ω S) : Representation R (G F Ω) M))
    (hv0 : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ m, ∀ g ∈ Ine (F := F) A, f g = rhoS (toGS Ω S g) m - m) (n : G F Ω)
    (hn : n ∈ NS Ω S) : f n = 0 := by
  have htriv : ∀ n ∈ NS Ω S, ∀ x, rhoS (toGS Ω S n) x = x := by
    intro n hn x
    have : toGS Ω S n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [this, map_one]
    rfl
  have h1 : f 1 = 0 := by
    have := hf.2 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  let N : Subgroup (G F Ω) :=
    { carrier := {n | n ∈ NS Ω S ∧ f n = 0}
      one_mem' := ⟨one_mem _, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hf.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hf.2 a⁻¹ a
        rw [inv_mul_cancel, h1, ha.2, map_zero, add_zero] at this
        exact this.symm⟩ }
  haveI hN : N.Normal := ⟨fun a ha g => by
    have hc := (normal_NS (Ω := Ω) S).conj_mem a ha.1 g
    refine ⟨hc, ?_⟩
    rw [GlobalTheory.Cut.ShaBound.coc_conj _ f hf.2 g a 0 (by rw [ha.2, map_zero, sub_zero])]
    exact sub_eq_zero.2 (htriv _ hc _)⟩
  have hcl : IsClosed (N : Set (G F Ω)) :=
    (isClosed_NS Ω _).inter (isClosed_singleton.preimage hf.1)
  refine (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl hn).2
  intro τ hτ
  simp only [Set.mem_iUnion] at hτ
  obtain ⟨v, hv, A, hA, hτ⟩ := hτ
  have h4 : τ ∈ NS Ω S := ine_le_NS hv hA hτ
  refine ⟨h4, ?_⟩
  obtain ⟨m, hm⟩ := hv0 v hv A hA
  rw [hm _ hτ, htriv _ h4, sub_self]

theorem UpperTheory.V.LDataCardLeFinrank.infUnram :
    Formalism.GaloisCohomology.InfUnram := by
  intro F Ω _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact hm g
  · rintro ⟨c, rfl⟩ v hv A hA
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
    have h1 : z.1 1 = 0 := by
      have := z.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω S g.1 = 1 := (QuotientGroup.eq_one_iff g.1).2 (ine_le_NS hv hA g.2)
    rw [map_zero, sub_zero]
    change z.1 (toGS Ω S g.1) = 0
    rw [h2, h1]
  · intro hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv0 : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Ine (F := F) A, z.1 g = rhoS (toGS Ω S g) m - m := by
      intro v hv A hA
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (hc v hv A hA))
      exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩
    let f' : GS Ω S → M := Quotient.lift z.1 fun a b hab => by
      have h1 := vanishAll rhoS z.2 hv0 _ (QuotientGroup.leftRel_apply.1 hab)
      have h2 := z.2.2 a (a⁻¹ * b)
      rw [mul_inv_cancel_left, h1, map_zero, add_zero] at h2
      exact h2.symm
    refine ⟨Submodule.Quotient.mk ⟨f', z.2.1.quotient_lift _, fun a b => ?_⟩, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact z.2.2 a b
