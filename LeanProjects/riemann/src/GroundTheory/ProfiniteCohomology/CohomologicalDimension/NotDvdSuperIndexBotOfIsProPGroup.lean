import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

section Simple

attribute [local instance 2000] Rep.hV2

omit [TotallyDisconnectedSpace G] in

theorem exists_bijective_hom_of_isProPGroup {p : ℕ} (hp : p.Prime) (hG : IsProPGroup p G)
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hsimple : IsSimpleOrder (Subrepresentation A.ρ))
    (hA : ∀ a : A, p • a = 0) :
    ∃ f : Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod p)) ⟶ A, Function.Bijective f.hom := by
  have hpf : Fact p.Prime := ⟨hp⟩

  have hnt : Nontrivial A := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hsimple.toNontrivial.exists_pair_ne.elim fun W₁ ⟨W₂, hW⟩ => hW
      (Subrepresentation.ext (by
        ext a
        rw [Subsingleton.elim a 0]
        exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩))

  have htop : ∀ W : Submodule (ULift.{u} ℤ) A, (∀ g, W ≤ W.comap (A.ρ g)) →
      ∀ w ∈ W, w ≠ 0 → ∀ a : A, a ∈ W := by
    intro W hW w hw hw0 a
    let W' : Subrepresentation A.ρ := ⟨W, fun g v hv => hW g hv⟩
    rcases hsimple.eq_bot_or_eq_top W' with h | h
    · exfalso
      have : w ∈ W'.toSubmodule := hw
      rw [h] at this
      exact hw0 ((Submodule.mem_bot _).1 this)
    · have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
      rw [← h] at this
      exact this

  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have hfin : Finite A := by
    obtain ⟨W, hW, hWfin, haW⟩ := exists_finite_stable_submodule A hp.pos
      (fun a => ⟨1, by rw [pow_one]; exact hA a⟩) a₀
    have hall := htop W hW a₀ haW ha₀
    exact Finite.of_injective (fun x : A => (⟨x, hall x⟩ : W)) fun x y h => congrArg Subtype.val h

  have hdisc := (isDiscreteRep_iff_forall_exists_openNormalSubgroup A).1 inferInstance
  choose U hU using hdisc
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite U
  have hVfix : ∀ g ∈ (V : Subgroup G), ∀ a : A, A.ρ g a = a := by
    intro g hg a
    have := (Representation.mem_invariants _ _).1 (hU a) ⟨g, hV a hg⟩
    exact this

  let H := (Representation.asGroupHom A.ρ).range
  have hH : IsPGroup p H := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := isProPGroup_iff.1 hG V g
    refine ⟨k, Subtype.ext (Units.ext (LinearMap.ext fun a => ?_))⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    rw [← map_pow, Representation.asGroupHom_apply, hVfix _ hk]

  have hcard : p ∣ Nat.card A := by
    have hPA : IsPGroup p (Multiplicative A) := fun x =>
      ⟨1, by rw [pow_one]; exact hA (Multiplicative.toAdd x)⟩
    have : Nontrivial (Multiplicative A) := hnt
    obtain ⟨m, hm, hcm⟩ := hPA.nontrivial_iff_card.1 this
    rw [show Nat.card A = Nat.card (Multiplicative A) from rfl, hcm]
    exact dvd_pow_self p hm.ne'
  have h0 : (0 : A) ∈ MulAction.fixedPoints H A := fun h => by
    show (h : (A →ₗ[ULift.{u} ℤ] A)ˣ) • (0 : A) = 0
    exact smul_zero _
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hcard h0
  have hbfix : ∀ g : G, A.ρ g b = b := fun g => hb ⟨_, g, rfl⟩

  have htriv : ∀ (g : G) (a : A), A.ρ g a = a := by
    intro g a
    have hinv := htop A.ρ.invariants (fun g v hv h => by
      rw [hv g]
      exact hv h) b ((Representation.mem_invariants _ _).2 hbfix) hb0.symm a
    exact (Representation.mem_invariants _ _).1 hinv g

  have hspan : ∀ a : A, a ∈ AddSubgroup.zmultiples b := by
    intro a
    let W : Submodule (ULift.{u} ℤ) A :=
      { AddSubgroup.zmultiples b with
        smul_mem' := fun r x hx => by
          rw [show r = ((r.down : ℤ) : ULift.{u} ℤ) by ext; simp, Int.cast_smul_eq_zsmul]
          exact zsmul_mem (show x ∈ AddSubgroup.zmultiples b from hx) r.down }
    exact htop W (fun g x hx => by
      rw [Submodule.mem_comap, htriv]
      exact hx) b (AddSubgroup.mem_zmultiples b) hb0.symm a
  have horder : addOrderOf b = p := addOrderOf_eq_prime (hA b) hb0.symm
  have hcardA : Nat.card A = p := by
    rw [← horder, ← Nat.card_zmultiples]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hspan).symm
  let e : ZMod p ≃+ A := zmodAddEquivOfGenerator hspan hcardA
  let F : ULift.{u} (ZMod p) →ₗ[ULift.{u} ℤ] A :=
    { toFun := fun x => e x.down
      map_add' := fun x y => map_add e x.down y.down
      map_smul' := fun r x => by
        obtain ⟨r⟩ := r
        obtain ⟨x⟩ := x
        rw [RingHom.id_apply]
        conv_rhs => rw [show (⟨r⟩ : ULift.{u} ℤ) = ((r : ℤ) : ULift.{u} ℤ) by ext; simp,
          Int.cast_smul_eq_zsmul]
        rw [← map_zsmul]
        rfl }
  refine ⟨Rep.ofHom ⟨F, fun g => LinearMap.ext fun x => (htriv g (F x)).symm⟩, ?_⟩
  exact ⟨fun x y hxy => ULift.ext _ _ (e.injective hxy),
    fun a => ⟨⟨e.symm a⟩, e.apply_symm_apply a⟩⟩

end Simple

theorem cdp_le_iff_of_isProPGroup {p : ℕ} (hp : p.Prime) (hG : IsProPGroup p G) (n : ℕ) :
    cdp p G ≤ n ↔
      Subsingleton (cohomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod p))) (n + 1)) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    refine subsingleton_cohomology_of_cdp_le hp h _ (fun a => ?_) (Nat.lt_succ_self n)
    ext
    simp
  · intro h
    rw [cdp_le_iff_forall_simple hp]
    intro A _ hsimple hA
    obtain ⟨f, hf⟩ := exists_bijective_hom_of_isProPGroup hp hG A hsimple hA
    have : Mono f := (Rep.mono_iff_injective _).2 hf.1
    have : Epi f := (Rep.epi_iff_surjective _).2 hf.2
    have : IsIso f := isIso_of_mono_of_epi f
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : cohomology A (n + 1),
        (cohomologyMap f (n + 1)).hom ((cohomologyMap (inv f) (n + 1)).hom z) = z := by
      intro z
      change (cohomologyMap (inv f) (n + 1) ≫ cohomologyMap f (n + 1)).hom z = z
      rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]
      rfl
    rw [← key x, ← key y, Subsingleton.elim ((cohomologyMap (inv f) (n + 1)).hom x)]

end GroundTheory.ProfCoh
