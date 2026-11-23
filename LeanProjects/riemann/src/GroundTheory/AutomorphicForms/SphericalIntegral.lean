import Mathlib
import GroundTheory.AutomorphicForms.SphericalMinuscule

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Polynomial
open ValuativeRel (valuation)
open scoped ValuativeRel Pointwise

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

theorem minusculeSet_eq (k : ℕ) :
    minusculeSet F n k = ⋃ (S : {S : Finset (Fin n) // S.card = k}) (c : Pairs S.1 → 𝓀[F]),
      gMat S.1 c • (integralGL F n : Set (GL (Fin n) F)) := by
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hg
    refine ⟨⟨S, hS⟩, c, ?_⟩
    have hk : (gMat S c)⁻¹ * g ∈ integralGL F n := QuotientGroup.eq.1 hc
    exact ⟨_, hk, by simp [smul_eq_mul]⟩
  · rintro ⟨⟨S, hS⟩, c, k', hk', rfl⟩
    have := mul_mem_minusculeSet (gMat_mem_minusculeSet S c) (integralGL F n).one_mem hk'
    rw [one_mul, hS] at this
    exact this

theorem isCompact_minusculeSet (k : ℕ) : IsCompact (minusculeSet F n k) := by
  rw [minusculeSet_eq]
  exact isCompact_iUnion fun S => isCompact_iUnion fun c => (isCompact_integralGL F n).smul _

theorem isOpen_minusculeSet (k : ℕ) : IsOpen (minusculeSet F n k) := by
  rw [minusculeSet_eq]
  exact isOpen_iUnion fun S => isOpen_iUnion fun c => (isOpen_integralGL F n).smul _

theorem mul_mem_minusculeSet_iff {k : ℕ} {a g b : GL (Fin n) F} (ha : a ∈ integralGL F n)
    (hb : b ∈ integralGL F n) : a * g * b ∈ minusculeSet F n k ↔ g ∈ minusculeSet F n k := by
  refine ⟨fun h => ?_, fun h => mul_mem_minusculeSet h ha hb⟩
  have := mul_mem_minusculeSet h ((integralGL F n).inv_mem ha) ((integralGL F n).inv_mem hb)
  simpa [mul_assoc] using this

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

variable (μ) in

def indicatorHecke (U : Set (GL (Fin n) F)) (hc : IsCompact U) (ho : IsOpen U)
    (hU : ∀ k ∈ integralGL F n, ∀ x, (k * x ∈ U ↔ x ∈ U) ∧ (x * k ∈ U ↔ x ∈ U)) :
    SphericalHecke μ (F := F) (n := n) :=
  HeckeAlgebraLevel.mk _ _ (HeckeAlgebra.mk μ (U.indicator fun _ => (1 : ℂ))
    (indicator_mem_locallyConstantCompactSupport hc ho 1)) fun k hk x => by
      simp only [HeckeAlgebra.coe_mk]
      constructor
      · by_cases h : x ∈ U
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hU k hk x).1.2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hU k hk x).1.1 h'))]
      · by_cases h : x ∈ U
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hU k hk x).2.2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hU k hk x).2.1 h'))]

theorem indicatorHecke_apply (U : Set (GL (Fin n) F)) (hc : IsCompact U) (ho : IsOpen U) (hU)
    (g : GL (Fin n) F) :
    (indicatorHecke μ U hc ho hU : HeckeAlgebra μ) g = U.indicator (fun _ => (1 : ℂ)) g := rfl

variable (μ) in

def minusculeHecke (k : ℕ) : SphericalHecke μ (F := F) (n := n) :=
  indicatorHecke μ (minusculeSet F n k) (isCompact_minusculeSet k) (isOpen_minusculeSet k)
    fun a ha x => ⟨by simpa using mul_mem_minusculeSet_iff (g := x) ha (integralGL F n).one_mem,
      by simpa using mul_mem_minusculeSet_iff (g := x) (integralGL F n).one_mem ha⟩

theorem lamS_injective : Function.Injective (lamS : Finset (Fin n) → Fin n → ℤ) := by
  intro S S' h
  ext i
  have := congrFun h i
  simp only [lamS] at this
  split_ifs at this <;> simp_all

theorem satake_minusculeHecke (k : ℕ) :
    satake μ (minusculeHecke μ k) = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ S ∈ Finset.univ.powersetCard k,
        ((Nat.card (Pairs S → 𝓀[F]) : ℂ) • monomial (lamS S)) := by
  classical
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard k).biUnion
    fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)
  have hval : ∀ x, (minusculeHecke μ k : HeckeAlgebra μ) x =
      (minusculeSet F n k).indicator (fun _ => (1 : ℂ)) x := fun x => rfl
  rw [satake_eq_sum _ Cs]
  · congr 1
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hSk := (Finset.mem_powersetCard.1 hS).2
      rw [Finset.sum_image fun c _ c' _ h => gMat_injective S h]
      have : ∀ c : Pairs S → 𝓀[F], AddMonoidAlgebra.single (iwasawaExponent F n
          (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n).out)
          ((minusculeHecke μ k : HeckeAlgebra μ)
            (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n).out) =
          monomial (lamS S) := by
        intro c
        rw [iwasawaExponent_out, iwasawaExponent_gMat, apply_out, hval,
          Set.indicator_of_mem (hSk ▸ gMat_mem_minusculeSet S c)]
      simp only [this, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      rw [Nat.cast_smul_eq_nsmul]
    · intro S _ S' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_gMat] at this
      exact hne (lamS_injective this).symm
  · intro x hx
    rw [hval]
    refine Set.indicator_of_notMem (fun hm => hx ?_) _
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩,
      Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

theorem sum_card_filter_lt (S : Finset (Fin n)) :
    ∑ b ∈ S, (S.filter fun a => b < a).card = S.card.choose 2 := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a T haT ih =>
    have ha : a ∉ T := fun h => lt_irrefl a (haT a h)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.choose_succ_succ', Nat.choose_one_right]
    have h1 : ((insert a T).filter fun x => a < x) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | hx)
      · exact lt_irrefl _
      · exact fun h => lt_asymm h (haT x hx)
    have h2 : ∀ b ∈ T, ((insert a T).filter fun x => b < x) =
        insert a (T.filter fun x => b < x) := by
      intro b hb
      rw [Finset.filter_insert, if_pos (haT b hb)]
    rw [h1, Finset.card_empty, zero_add, Finset.sum_congr rfl fun b hb => by
      rw [h2 b hb, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1)],
      Finset.sum_add_distrib, ih, Finset.sum_const, smul_eq_mul, mul_one]
    ring

theorem card_pairs (S : Finset (Fin n)) :
    Fintype.card (Pairs S) = ∑ b ∈ S, ((Finset.Ioi b).filter fun a => a ∉ S).card := by
  classical
  rw [show Fintype.card (Pairs S) = (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2).card from Fintype.card_subtype _]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b ∈ S)]
  have h0 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ S),
      ∑ a, (if b ∈ S ∧ a ∉ S ∧ b < a then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun a _ => by
      rw [if_neg fun h => (Finset.mem_filter.1 hb).2 h.1]
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.card_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => b < a)]
  have h1 : ∑ a ∈ Finset.univ.filter (fun a => ¬ b < a),
      (if b ∈ S ∧ a ∉ S ∧ b < a then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun a ha => by rw [if_neg fun h => (Finset.mem_filter.1 ha).2 h.2.2]
  rw [h1, add_zero]
  have : Finset.univ.filter (fun a => b < a) = Finset.Ioi b := by
    ext a
    simp
  rw [this]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hba : b < a := Finset.mem_Ioi.1 ha
  by_cases haS : a ∈ S
  · rw [if_neg fun h => h.2.1 haS, if_neg fun h => h haS]
  · rw [if_pos ⟨hb, haS, hba⟩, if_pos haS]

theorem card_pairs_add_choose (S : Finset (Fin n)) :
    Fintype.card (Pairs S) + S.card.choose 2 = ∑ i ∈ S, (n - 1 - i.val) := by
  classical
  rw [card_pairs, ← sum_card_filter_lt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Fin.card_Ioi b, ← Finset.card_filter_add_card_filter_not (s := Finset.Ioi b) (fun a => a ∈ S),
    add_comm]
  congr 2
  ext a
  simp [and_comm]

theorem torusPow_const_comm (t : ℤ) (g : GL (Fin n) F) :
    torusPow F n (fun _ => t) * g = g * torusPow F n (fun _ => t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, coe_torusPow, diagonal_mul, mul_diagonal, mul_comm]

variable (F n) in

def centralSet : Set (GL (Fin n) F) :=
  torusPow F n (fun _ => -1) • (integralGL F n : Set (GL (Fin n) F))

theorem mem_centralSet {g : GL (Fin n) F} :
    g ∈ centralSet F n ↔ (torusPow F n (fun _ => -1))⁻¹ * g ∈ integralGL F n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [smul_eq_mul] using hx
  · intro h
    exact ⟨_, h, by simp [smul_eq_mul]⟩

variable (μ) in

def centralHecke : SphericalHecke μ (F := F) (n := n) :=
  indicatorHecke μ (centralSet F n) ((isCompact_integralGL F n).smul _)
    ((isOpen_integralGL F n).smul _) fun a ha x => by
      simp only [mem_centralSet]
      have hz : (torusPow F n (fun _ => (-1 : ℤ)))⁻¹ = torusPow F n (fun _ => 1) := by
        rw [← torusPow_neg]
        congr 1
      rw [hz]
      constructor
      · rw [← mul_assoc, torusPow_const_comm 1 a, mul_assoc]
        exact ⟨fun h => by simpa [mul_assoc] using mul_mem (inv_mem ha) h, fun h => mul_mem ha h⟩
      · rw [← mul_assoc]
        exact ⟨fun h => by simpa [mul_assoc] using mul_mem h (inv_mem ha), fun h => mul_mem h ha⟩

theorem centralHecke_apply (g : GL (Fin n) F) :
    (centralHecke μ (F := F) (n := n) : HeckeAlgebra μ) g =
      (centralSet F n).indicator (fun _ => (1 : ℂ)) g := rfl

theorem satake_centralHecke :
    satake μ (centralHecke μ (F := F) (n := n)) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) • monomial (fun _ => -1) := by
  classical
  set z := torusPow F n (fun _ => (-1 : ℤ))
  have hz : z ∈ centralSet F n := mem_centralSet.2 (by rw [inv_mul_cancel]; exact one_mem _)
  rw [satake_eq_sum _ {(QuotientGroup.mk z : GL (Fin n) F ⧸ integralGL F n)}]
  · rw [Finset.sum_singleton, iwasawaExponent_out, iwasawaExponent_torusPow, apply_out,
      centralHecke_apply, Set.indicator_of_mem hz]
  · intro x hx
    rw [centralHecke_apply]
    refine Set.indicator_of_notMem (fun hm => hx ?_) _
    rw [Finset.mem_singleton, ← QuotientGroup.out_eq' x]
    exact (QuotientGroup.eq.2 (mem_centralSet.1 hm)).symm

variable (F) in

def qF : ℕ := Nat.card 𝓀[F]

theorem qF_pos : 0 < qF F := Nat.card_pos

variable (F) in

def yElt (i : Fin n) : LaurentRing n := single (Pi.single i 1) ((qF F : ℂ) ^ (n - 1 - i.val))

theorem sum_single_one (S : Finset (Fin n)) : ∑ i ∈ S, (Pi.single i 1 : Fin n → ℤ) = lamS S := by
  classical
  funext m
  simp [Finset.sum_apply, Pi.single_apply, lamS]

theorem prod_yElt (S : Finset (Fin n)) :
    ∏ i ∈ S, yElt F i = ((qF F : ℂ) ^ S.card.choose 2 * (qF F : ℂ) ^ Fintype.card (Pairs S)) •
      monomial (lamS S) := by
  simp only [yElt]
  rw [AddMonoidAlgebra.prod_single, sum_single_one, Finset.prod_pow_eq_pow_sum,
    ← card_pairs_add_choose, AddMonoidAlgebra.smul_single', mul_one, pow_add, mul_comm]

theorem esymm_yElt_mem (k : ℕ) :
    (Finset.univ.val.map (yElt F (n := n))).esymm k ∈ (satakeHom μ (F := F) (n := n)).range := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rw [Finset.esymm_map_val]
  have : ∑ S ∈ Finset.univ.powersetCard k, ∏ i ∈ S, yElt F i =
      ((qF F : ℂ) ^ k.choose 2 * (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹) •
        satake μ (minusculeHecke μ k) := by
    rw [satake_minusculeHecke, smul_smul, mul_assoc, inv_mul_cancel₀ hK, mul_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [prod_yElt, (Finset.mem_powersetCard.1 hS).2, smul_smul, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Pairs S)]
    push_cast
    rfl
  rw [this]
  exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _

theorem isIntegral_yElt (i : Fin n) : IsIntegral (satakeHom μ (F := F) (n := n)).range (yElt F i) := by
  classical
  set A := (satakeHom μ (F := F) (n := n)).range
  set s : Multiset (LaurentRing n) := Finset.univ.val.map (yElt F (n := n))
  set p : (LaurentRing n)[X] := (s.map fun t => X - C t).prod
  have hmonic : p.Monic := monic_multiset_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hlifts : p ∈ lifts (algebraMap A (LaurentRing n)) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    by_cases hk : k ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hk]
      have hmem : (-1 : LaurentRing n) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) ∈ A :=
        Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
          (esymm_yElt_mem _)
      exact ⟨⟨_, hmem⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega)]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlifts hmonic
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq, eval_multiset_prod, Multiset.map_map]
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  exact ⟨yElt F i, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, rfl⟩, by simp⟩

theorem isIntegral_satake :
    Algebra.IsIntegral (satakeHom μ (F := F) (n := n)).range (LaurentRing n) := by
  classical
  have hq : ((qF F : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (qF_pos (F := F)).ne'
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h₁ : ∀ i, IsIntegral (satakeHom μ (F := F) (n := n)).range
      (monomial (Pi.single i 1 : Fin n → ℤ)) := by
    intro i
    have : monomial (Pi.single i 1 : Fin n → ℤ) = ((qF F : ℂ) ^ (n - 1 - i.val))⁻¹ • yElt F i := by
      rw [yElt, AddMonoidAlgebra.smul_single', inv_mul_cancel₀ (pow_ne_zero _ hq)]
    rw [this]
    exact (isIntegral_yElt i).smul _
  refine isIntegral_of_forall _ h₁ fun i => ?_
  have hc : monomial (fun _ => (-1 : ℤ)) ∈ (satakeHom μ (F := F) (n := n)).range := by
    have : monomial (fun _ => (-1 : ℤ)) =
        (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ • satake μ (centralHecke μ) := by
      rw [satake_centralHecke, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [this]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _
  have heq : monomial (Pi.single i (-1) : Fin n → ℤ) = monomial (fun _ => (-1 : ℤ)) *
      ∏ j ∈ Finset.univ.erase i, monomial (Pi.single j 1 : Fin n → ℤ) := by
    rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, Finset.prod_const_one,
      one_mul]
    congr 1
    funext m
    by_cases hm : m = i
    · subst hm
      simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, Pi.single_apply, hm]
  rw [heq]
  refine IsIntegral.mul (isIntegral_algebraMap (x := (⟨_, hc⟩ : (satakeHom μ).range))) ?_
  exact IsIntegral.prod _ fun j _ => h₁ j

end Spherical

end GroundTheory.Automorphic
