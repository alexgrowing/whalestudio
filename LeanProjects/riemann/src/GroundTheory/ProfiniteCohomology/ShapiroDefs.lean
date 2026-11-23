import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.CoinducedModules
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Maps

variable (U : Subgroup G)

noncomputable def coindEvalOne (B : Rep.{u} k U) :
    Rep.res U.subtype (Rep.coind U.subtype B) ⟶ B :=
  Rep.ofHom ⟨(LinearMap.proj (1 : G)).comp (Representation.coindV U.subtype B.ρ).subtype,
    fun u => by
      ext f
      change f.1 (1 * (u : G)) = B.ρ u (f.1 1)
      rw [one_mul]
      simpa using f.2 u 1⟩

@[simp]
theorem coindEvalOne_hom_apply (B : Rep.{u} k U) (f : Rep.coind U.subtype B) :
    (coindEvalOne U B).hom f = f.1 1 :=
  rfl

noncomputable def coindUnit (A : Rep.{u} k G) :
    A ⟶ Rep.coind U.subtype (Rep.res U.subtype A) :=
  Rep.resCoindToHom U.subtype A (Rep.res U.subtype A) (𝟙 _)

@[simp]
theorem coindUnit_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((coindUnit U A).hom a).1 x = A.ρ x a :=
  rfl

theorem coindUnit_comp_coindEvalOne (A : Rep.{u} k G) :
    (Rep.resFunctor U.subtype).map (coindUnit U A) ≫ coindEvalOne U (Rep.res U.subtype A) =
      𝟙 _ := by
  ext a
  change A.ρ 1 a = a
  simp

section Trace

variable (A : Rep.{u} k G)

noncomputable def coindTraceTerm (c : G ⧸ U) :
    Rep.coind U.subtype (Rep.res U.subtype A) →ₗ[k] A :=
  A.ρ c.out ∘ₗ (LinearMap.proj c.out⁻¹).comp
    (Representation.coindV U.subtype (Rep.res U.subtype A).ρ).subtype

theorem coindTraceTerm_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) (x : G) :
    coindTraceTerm U A (x : G ⧸ U) f = A.ρ x (f.1 x⁻¹) := by
  change A.ρ (x : G ⧸ U).out (f.1 (x : G ⧸ U).out⁻¹) = A.ρ x (f.1 x⁻¹)
  obtain ⟨u, hu⟩ : ∃ u : U, (x : G ⧸ U).out = x * u := by
    have h := QuotientGroup.mk_out_eq_mul U x
    obtain ⟨u, hu⟩ := h
    exact ⟨u, hu⟩
  rw [hu]
  have h1 : (x * (u : G))⁻¹ = U.subtype u⁻¹ * x⁻¹ := by simp
  rw [h1, f.2 u⁻¹ x⁻¹]
  change A.ρ (x * u) (A.ρ (u⁻¹ : U) (f.1 x⁻¹)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def coindTrace : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A :=
  Rep.ofHom ⟨∑ c : G ⧸ U, coindTraceTerm U A c, fun g => by
    ext f
    change (∑ c : G ⧸ U, coindTraceTerm U A c) ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g f) =
      A.ρ g ((∑ c : G ⧸ U, coindTraceTerm U A c) f)
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun c => ?_).symm
    induction c using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAction.toPerm_apply, MulAction.Quotient.smul_mk]
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ g (A.ρ x (f.1 x⁻¹)) = A.ρ (g * x) (f.1 ((g * x)⁻¹ * g))
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_inv_rev, mul_assoc]⟩

theorem coindTrace_hom_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) :
    (coindTrace U A).hom f = ∑ c : G ⧸ U, coindTraceTerm U A c f := by
  simp [coindTrace]

theorem coindUnit_comp_coindTrace : coindUnit U A ≫ coindTrace U A = U.index • 𝟙 A := by
  ext a
  change (coindTrace U A).hom ((coindUnit U A).hom a) = (U.index • 𝟙 A : A ⟶ A).hom a
  rw [coindTrace_hom_apply]
  have h : ∀ c : G ⧸ U, coindTraceTerm U A c ((coindUnit U A).hom a) = a := fun c => by
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [coindTraceTerm_apply, coindUnit_hom_apply, ← Module.End.mul_apply, ← map_mul]
      simp
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Rep.nsmul_hom]
  rfl

end Trace

end Maps

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Discrete

variable (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B]

theorem isLocallyConstant_coind (f : Rep.coind (U : Subgroup G).subtype B) :
    IsLocallyConstant (f.1 : G → B) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  set S : Set G := Subtype.val '' (stabilizer B.ρ (f.1 x) : Set (U : Subgroup G))
  have hS : IsOpen S :=
    IsOpen.isOpenMap_subtype_val (s := (U : Set G)) U.isOpen _ (isOpen_stabilizer B (f.1 x))
  have h1 : S ∈ 𝓝 (1 : G) := hS.mem_nhds ⟨1, (stabilizer B.ρ (f.1 x)).one_mem, rfl⟩
  have hc : Continuous fun y : G => y * x⁻¹ := continuous_id.mul continuous_const
  have h2 : ∀ᶠ y in 𝓝 x, y * x⁻¹ ∈ S := hc.continuousAt.preimage_mem_nhds (by simpa using h1)
  filter_upwards [h2] with y hy
  obtain ⟨u, hu, huy⟩ := hy
  have hy' : y = (U : Subgroup G).subtype u * x := by
    simp only [Subgroup.subtype_apply, huy, inv_mul_cancel_right]
  rw [hy', f.2 u x]
  exact (mem_stabilizer _ _ _).1 hu

noncomputable def coindToLocallyConstant (f : Rep.coind (U : Subgroup G).subtype B) :
    LocallyConstant G B :=
  ⟨f.1, isLocallyConstant_coind U B f⟩

instance isDiscreteRep_coind [CompactSpace G] :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype B) :=
  ⟨fun f => Subgroup.isOpen_of_mem_nhds (g := 1) _ <|
    Filter.mem_of_superset (eventually_forall_mul_eq (coindToLocallyConstant U B f))
      fun g (hg : ∀ x, f.1 (x * g) = f.1 x) => Subtype.ext (funext fun x => hg x)⟩

instance finiteIndex_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

instance compactSpace_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace (U : Subgroup G) :=
  isCompact_iff_compactSpace.mp (U.isClosed.isCompact)

end Discrete

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B]

noncomputable def shapiroMap (n : ℕ) :
    cohomology (Rep.coind (U : Subgroup G).subtype B) n ⟶ cohomology B n :=
  cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
    (coindEvalOne (U : Subgroup G) B) n

theorem shapiroMap_eq (n : ℕ) :
    shapiroMap U B n = cohomologyMapAlong (U : Subgroup G).subtype
      (continuous_subgroup_subtype _) (coindEvalOne (U : Subgroup G) B) n :=
  rfl

end Shapiro

end GroundTheory.ProfCoh
