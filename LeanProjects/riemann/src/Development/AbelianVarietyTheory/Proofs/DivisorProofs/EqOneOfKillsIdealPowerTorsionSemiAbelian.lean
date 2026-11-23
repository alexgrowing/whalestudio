import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense
open scoped nonZeroDivisors

theorem exists_pow_eq_span (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hI' : I ≠ ⊤) : ∃ (h : ℕ) (π : 𝓞 E), 0 < h ∧ I ^ h = Ideal.span {π} ∧ π ≠ 0 ∧ ¬ IsUnit π := by
  have hmem : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  let c := ClassGroup.mk0 ⟨I, hmem⟩
  have hc : c ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  have hmem' : I ^ Fintype.card (ClassGroup (𝓞 E)) ∈ (Ideal (𝓞 E))⁰ := pow_mem hmem _
  have hp : (I ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hmem']
    rw [← hc, ← map_pow]
    rfl
  obtain ⟨π, hπ⟩ := hp
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  refine ⟨_, π, hpos, by rw [hπ], ?_, ?_⟩
  · rintro rfl
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊥ := by rw [hπ]; simp
    exact hI (pow_eq_zero_iff hpos.ne' |>.1 this)
  · intro hu
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊤ := by
      rw [hπ]; exact Ideal.span_singleton_eq_top.2 hu
    exact hI' (eq_top_iff.2 (this ▸ Ideal.pow_le_self hpos.ne'))

theorem exists_act_pow_stable {k : Type} [Field k] [IsAlgClosed k] {O : Type} [CommRing O]
    (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (act : OAct O G) (π : O)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) (hKs : ∀ x ∈ K, x ≫ act.act π ∈ K) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ≫ act.act (π ^ (a + 1)) = x ≫ act.act (π ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ≫ act.act (π ^ n) = z} :=
    fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (act.act (π ^ n))
      (act.hom _) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    rfl
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl a⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    haveI := act.hom π
    refine ⟨y ≫ act.act π, ?_, by rw [Category.assoc, ← act.mul, ← pow_succ']⟩
    exact hKs y hy
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ≫ act.act (π ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

end GlobalTheory.IdealTorsion

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense

theorem eq_one_of_idealTorsion_comp_eq_one : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  intro E _ _ k _ _ _ G _ act u I hG hu hcomm hI hkill
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  haveI := hu
  have hact : ∀ a, IsMonHom (act.act a) := act.hom
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ u) fun x y => MonObj.mul_comp x y u
  by_cases hbot : I = ⊥
  · subst hbot
    refine eq_one_of_finite_range u ?_
    have : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ u) ⊆ {1} := by
      rintro _ ⟨x, rfl⟩
      refine hkill 1 x fun a ha => ?_
      rw [pow_one, Ideal.mem_bot] at ha
      rw [ha, h0, MonObj.comp_one]
    exact (Set.finite_singleton _).subset this
  obtain ⟨h, π, hh, hπ, hπ0, hπu⟩ := exists_pow_eq_span E I hbot hI
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), x ≫ act.act (π ^ n) = 1 → x ≫ u = 1 := by
    intro n x hx
    refine hkill (h * n) x fun a ha => ?_
    rw [pow_mul, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_comm, act.mul, ← Category.assoc, hx, MonObj.one_comp]
  obtain ⟨a, ha⟩ := exists_act_pow_stable G act π φ.ker (u.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)})
    ((isClosed_pt _).preimage u.left.continuous) (fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      change x ≫ act.act π ≫ u = 1
      rw [hcomm, ← Category.assoc]
      change (x ≫ u) ≫ act.act π = 1
      rw [show x ≫ u = 1 from hx, MonObj.one_comp])
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G u hu inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine GlobalTheory.T.finite_closed_stable_subgroup_semiAbelian_no_torsion E k G act π hG hπ0 hπu _ Z' hZ' (fun y => ?_) ?_ ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro b _ ⟨g, rfl⟩
      refine ⟨g ≫ act.act b, ?_⟩
      change (g ≫ act.act b) ≫ u = (g ≫ u) ≫ act.act b
      rw [Category.assoc, hcomm, Category.assoc]
    · rintro _ ⟨g, rfl⟩ hg
      have hgk : g ≫ act.act π ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        change (g ≫ act.act π) ≫ u = 1
        rw [Category.assoc, hcomm, ← Category.assoc]
        exact hg
      obtain ⟨y, hy, hyg⟩ := ha _ hgk
      let ψ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
        MonoidHom.mk' (fun x => x ≫ act.act (π ^ (a + 1))) fun x y => MonObj.mul_comp x y _
      have h1 : φ (g / y) = 1 := htors (a + 1) (g / y) (by
        change ψ (g / y) = 1
        rw [map_div, div_eq_one]
        change g ≫ act.act (π ^ (a + 1)) = y ≫ act.act (π ^ (a + 1))
        rw [hyg, pow_succ', act.mul, Category.assoc])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range u hfin

end GlobalTheory.IdealTorsion
