import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology Filter GlobalTheory.Points

namespace GlobalTheory.IntegralPower

theorem eventually_extends {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [TopologicalSpace C]
    (σ : V →+* C) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (y : Sp V ⟶ X) :
    ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), x ≫ q = spMap σ →
      ∃ z : Sp V ⟶ X, z ≫ q = 𝟙 _ ∧ spMap σ ≫ z = x := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_le y (le_preimage_top _)
  have hy' : ⊤ ≤ (spMap σ ≫ y) ⁻¹ᵁ U := le_preimage_comp _ y hy (le_preimage_top _)
  let c : V →+* Γ(X, U) := (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have hc : ∀ a, c a = constFn q U a := fun _ => rfl
  have hft : c.FiniteType := (q.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
  letI := c.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType V Γ(X, U) from hft).out
  have h1 : ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), ∀ f ∈ s, valR x U f ∈ Set.range σ := by
    refine (eventually_all_finset s).2 fun f _ => (continuousAt_valR f hy').eventually (ho.mem_nhds ?_)
    exact ⟨_, (valR_spMap_comp σ y U hy f).symm⟩
  filter_upwards [h1, (isOpen_setOf_le_preimage U).mem_nhds hy'] with x hx hxU hxq
  have h2 : ∀ f, (valMap x U hxU).hom f ∈ σ.range := by
    intro f
    have hf : f ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      rw [← valR_eq]
      exact hx f hf
    | algebraMap a =>
      rw [← valR_eq]
      exact ⟨a, (valR_constFn_of_over q σ x hxq U hxU a).symm⟩
    | add f g _ _ hf hg =>
      rw [map_add]
      exact add_mem hf hg
    | mul f g _ _ hf hg =>
      rw [map_mul]
      exact mul_mem hf hg
  let e : V ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => hσ (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((valMap x U hxU).hom.codRestrict σ.range h2)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom σ = valMap x U hxU := by
    ext f
    exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h2 f⟩)
  have hz : spMap σ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = x := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, specMap_valMap_fromSpec]
  refine ⟨_, ?_, hz⟩
  rw [← hz, Category.assoc] at hxq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ q)
  rw [← hφ, ← Spec.map_comp] at hxq
  rw [← hφ, ← Spec.map_id]
  congr 1
  ext a
  exact hσ (congrArg (fun u => u.hom a) (Spec.map_injective hxq))

section Group

variable {C : Type} [CommRing C] [TopologicalSpace C] {S : Scheme.{0}} (t : Sp C ⟶ S)

omit [TopologicalSpace C] in

abbrev leftPt {A : Over S} (x : Over.mk t ⟶ A) : Sp C ⟶ A.left := x.left

abbrev ptTopology (A : Over S) : TopologicalSpace (Over.mk t ⟶ A) :=
  TopologicalSpace.induced (leftPt t) (topology C A.left)

attribute [local instance] ptTopology

theorem isEmbedding_leftPt (A : Over S) : IsEmbedding (leftPt t (A := A)) :=
  ⟨⟨rfl⟩, fun _ _ h => Over.OverMorphism.ext h⟩

theorem compactSpace_of_ptsOver (A : Over S) [CompactSpace (PtsOver A.hom t)] :
    CompactSpace (Over.mk t ⟶ A) :=
  Function.Surjective.compactSpace (f := fun x : PtsOver A.hom t => (Over.homMk x.1 x.2 : Over.mk t ⟶ A))
    ((isEmbedding_leftPt t A).continuous_iff.2 continuous_subtype_val) fun x => ⟨⟨x.left, Over.w x⟩, rfl⟩

theorem continuous_comp_over {A B : Over S} (g : A ⟶ B) : Continuous fun x : Over.mk t ⟶ A => x ≫ g :=
  (isEmbedding_leftPt t B).continuous_iff.2 ((continuous_comp g.left).comp (isEmbedding_leftPt t A).continuous)

variable [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

theorem continuous_lift (A B : Over S) :
    Continuous fun q : (Over.mk t ⟶ A) × (Over.mk t ⟶ B) => lift q.1 q.2 := by
  refine (isEmbedding_leftPt t _).continuous_iff.2 ?_
  refine (isEmbedding_of_isPullback (C := C) (IsPullback.of_hasPullback A.hom B.hom)).continuous_iff.2 ?_
  refine ((isEmbedding_leftPt t A).continuous.prodMap (isEmbedding_leftPt t B).continuous).congr fun q => ?_
  exact Prod.ext (congrArg (·.left) (lift_fst q.1 q.2)).symm (congrArg (·.left) (lift_snd q.1 q.2)).symm

theorem isTopologicalGroup (G : Over S) [GrpObj G] : IsTopologicalGroup (Over.mk t ⟶ G) where
  continuous_mul := (continuous_comp_over t (μ[G])).comp (continuous_lift t G G)
  continuous_inv := continuous_comp_over t (GrpObj.inv (X := G))

end Group

attribute [local instance] ptTopology in

theorem exists_pow_extends {V F : Type} [CommRing V] [IsLocalRing V] [NormedField F] [ProperSpace F]
    (σ : V →+* F) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) (G : Over (Sp V)) [GrpObj G]
    [LocallyOfFiniteType G.hom] (h : IsProjOver (pullback.snd G.hom (spMap σ))) (a : Over.mk (spMap σ) ⟶ G) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp V)) ⟶ G, toUnit _ ≫ g = a ^ k := by
  have h1 : CompactSpace (Pts (pullback.snd G.hom (spMap σ))) := PtsOver.compactSpace h _
  have h2 := (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback G.hom (spMap σ))).compactSpace
  have h3 := compactSpace_of_ptsOver (spMap σ) G
  have h4 := isTopologicalGroup (spMap σ) G
  let r : (𝟙_ (Over (Sp V)) ⟶ G) →* (Over.mk (spMap σ) ⟶ G) :=
    MonoidHom.mk' (fun g => toUnit _ ≫ g) fun g g' => comp_mul _ g g'
  have hr : ∀ g, leftPt _ (r g) = spMap σ ≫ g.left := fun g => by
    have : (toUnit (Over.mk (spMap σ))).left = spMap σ := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap σ))))
    exact congrArg (· ≫ g.left) this
  have hopen : IsOpen (r.range : Set (Over.mk (spMap σ) ⟶ G)) := by
    refine r.range.isOpen_of_mem_nhds (g := r 1) ?_
    have h5 := eventually_extends σ hσ ho G.hom (1 : 𝟙_ (Over (Sp V)) ⟶ G).left
    rw [← hr] at h5
    filter_upwards [(isEmbedding_leftPt _ G).continuous.continuousAt.eventually h5] with x hx
    obtain ⟨z, hz, hzx⟩ := hx (Over.w x)
    exact ⟨Over.homMk z hz, (isEmbedding_leftPt _ G).injective ((hr _).trans hzx)⟩
  have h6 : Finite (_ ⧸ r.range) := r.range.quotient_finite_of_isOpen hopen
  obtain ⟨k, hk, -, g, hg⟩ := r.range.exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite a
  exact ⟨k, hk, g, hg⟩

theorem exists_pow_integral : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] [LocallyOfFiniteType G.hom] [IsSeparated G.hom], IsProjOver (pullback.snd G.hom (spMap (algebraMap (integralClosure ℤ_[p] K) K))) → ∀ a : Over.mk (spMap (algebraMap (integralClosure ℤ_[p] K) K)) ⟶ G, ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp (integralClosure ℤ_[p] K))) ⟶ G, toUnit _ ≫ g = a ^ k := by
  intro p _ K _ G _ _ _ h a
  letI : NormedField K := inferInstanceAs (NormedField K.toSubfield)
  letI : NormedSpace ℚ_[p] K := ⟨fun c x => norm_smul_le c (x : PadicAlgCl p)⟩
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  haveI : IsUltrametricDist K := ⟨fun x y z => IsUltrametricDist.dist_triangle_max (x : PadicAlgCl p) y z⟩
  refine exists_pow_extends _ Subtype.val_injective ?_ G h a
  convert IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero using 1
  ext x
  rw [mem_closedBall_zero_iff]
  exact (Set.ext_iff.1 Subtype.range_val x).trans (mem_integralClosure_padicInt_iff K x)

end GlobalTheory.IntegralPower
