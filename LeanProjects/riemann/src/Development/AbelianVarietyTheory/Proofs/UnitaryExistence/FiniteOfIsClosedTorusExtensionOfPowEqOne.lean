import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem map_eq_one_of_pow_eq_one_of_finite_ker {H B : Type*} [Group H] [Group B] (φ : H →* B)
    [Finite φ.ker] {n : ℕ} (hn : n.Prime) (h : ∀ x : H, x ^ n = 1 → x = 1) (y : H)
    (hy : φ y ^ n = 1) : φ y = 1 := by
  have hmem : y ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have h1 : IsOfFinOrder (y ^ n) :=
    φ.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨y ^ n, hmem⟩ : φ.ker))
  have h2 : IsOfFinOrder y := h1.of_pow hn.ne_zero
  have h3 : ¬ n ∣ orderOf y := by
    rintro ⟨m, hm⟩
    have h4 : y ^ m = 1 := h _ (by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one])
    have h5 := orderOf_dvd_of_pow_eq_one h4
    have h6 := h2.orderOf_pos
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at h6)
    have h7 := Nat.le_of_dvd hm0 h5
    have h8 := hn.two_le
    nlinarith
  have h9 : orderOf (φ y) ∣ Nat.gcd n (orderOf y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_map_dvd φ y)
  rw [(hn.coprime_iff_not_dvd.2 h3).gcd_eq_one] at h9
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h9)

open RationalPoint in

theorem finite_of_isClosed_torusExtension_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ), LocallyOfFiniteType G.hom → QuasiCompact G.hom → Nonempty (TorusExtension G) → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro hab k _ _ G _ _ n _ _ ⟨E⟩ hp hn C Z hZ hC htors
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.isAbelian.proper
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ E.B) :=
    MonoidHom.mk' (fun x => x ≫ E.q) fun x y => MonObj.mul_comp x y E.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ E.i) fun x y => MonObj.mul_comp x y E.i
  have hj : Function.Injective j := fun x y hxy =>
    E.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨E.isKernel.lift x (toUnit _) hx, E.isKernel.lift_fst _ _ _⟩
  have hT : Finite (C.comap j) := by
    refine finite_of_isClosed_splitTorus_of_pow_eq_one k E.X n hp hn _ (E.i.left ⁻¹' Z)
      (hZ.preimage E.i.left.continuous) (fun x => ?_) fun x hx h1 => ?_
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · exact hj (by rw [map_one]; exact htors _ hx (by rw [← map_pow, h1, map_one]))
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ E.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G E.B E.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine hab k E.B n E.isAbelian hp hn _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · rintro _ ⟨y, rfl⟩ hy
      exact map_eq_one_of_pow_eq_one_of_finite_ker ψ hp
        (fun x hx => Subtype.ext (htors x.1 x.2 (congrArg Subtype.val hx))) y hy
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory
