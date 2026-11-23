import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.SubZeta

theorem index_eq_mul_of_exact {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
    (π : G →+ A) (hπ : Function.Surjective π) (ι : B →+ G) (hι : ι.range = π.ker)
    (H : AddSubgroup G) : H.index = (H.map π).index * (H.comap ι).index := by
  have h1 : (H.map π).index = (H ⊔ π.ker).index := by
    rw [← AddSubgroup.index_comap_of_surjective (H := H.map π) hπ, AddSubgroup.comap_map_eq]
  have h2 : (H.comap ι).index = H.relIndex π.ker := by
    rw [AddSubgroup.index_comap, hι]
  rw [h1, h2, ← AddSubgroup.relIndex_sup_left, mul_comm, AddSubgroup.relIndex_mul_index le_sup_left]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem index_span_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup.index =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : (Ideal.span {ϖ ^ (n+1)} : Ideal O).toAddSubgroup ≤
        (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup := by
      intro x hx
      exact (Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ (pow_succ ϖ n).symm)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, ih, pow_succ (Nat.card (IsLocalRing.ResidueField O)) n, mul_comm]
    congr 1
    let f : O →+ O := AddMonoidHom.mulLeft (ϖ ^ n)
    have hr : f.range = (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup := by
      ext x
      simp [f, Ideal.mem_span_singleton', mul_comm]
    rw [← hr, ← AddSubgroup.index_comap]
    have hc : (Ideal.span {ϖ ^ (n+1)} : Ideal O).toAddSubgroup.comap f =
        (IsLocalRing.maximalIdeal O).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, f, AddMonoidHom.coe_mulLeft]
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton,
        Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
    rw [hc]
    rfl

end GlobalTheory.SubZeta

namespace GlobalTheory.SubZeta

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem infinite_of_dvr : Infinite O := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact IsDiscreteValuationRing.not_isField O (Finite.isField_of_domain O)

theorem sum_ideal_le [Finite (IsLocalRing.ResidueField O)] (σ : ℝ) (hσ : 0 < σ) (D : Finset (Ideal O))
    (hD : ∀ I ∈ D, I.toAddSubgroup.index ≠ 0) :
    ∑ I ∈ D, (I.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-σ))⁻¹ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq : (1 : ℝ) < (Nat.card (IsLocalRing.ResidueField O) : ℝ) := by
    exact_mod_cast Finite.one_lt_card
  have hne : ∀ I ∈ D, I ≠ ⊥ := by
    intro I hI h
    apply hD I hI
    rw [h, Submodule.bot_toAddSubgroup, AddSubgroup.index_bot]
    haveI := infinite_of_dvr (O := O)
    exact Nat.card_eq_zero_of_infinite
  choose! e he using fun I hI => IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (hne I hI) hϖ
  have hinj : Set.InjOn e D := fun I hI J hJ h => by rw [he I hI, he J hJ, h]
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField O) : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hval : ∀ I ∈ D, (I.toAddSubgroup.index : ℝ) ^ (-σ) = (q ^ (-σ)) ^ e I := by
    intro I hI
    have hidx : I.toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField O) ^ e I := by
      conv_lhs => rw [he I hI]
      exact index_span_pow hϖ _
    rw [hidx, Nat.cast_pow, ← hqdef, ← Real.rpow_natCast q, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast (q ^ (-σ)), ← Real.rpow_mul hq0.le, mul_comm]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_image (f := fun n : ℕ => (q ^ (-σ)) ^ n) hinj]
  have hx0 : 0 ≤ q ^ (-σ) := (Real.rpow_pos_of_pos hq0 _).le
  have hx1 : q ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  rw [← tsum_geometric_of_lt_one hx0 hx1]
  exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hx0 i) (summable_geometric_of_lt_one hx0 hx1)

def headL (r : ℕ) : (Fin (r+1) → O) →ₗ[O] O := LinearMap.proj (R := O) (φ := fun _ => O) 0

theorem headL_apply (r : ℕ) (x : Fin (r+1) → O) : headL r x = x 0 := rfl

def consL (r : ℕ) : (Fin r → O) →ₗ[O] (Fin (r+1) → O) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consL_apply (r : ℕ) (y : Fin r → O) : consL r y = Fin.cons 0 y := rfl

theorem index_split {r : ℕ} (M : Submodule O (Fin (r+1) → O)) :
    M.toAddSubgroup.index =
      (M.map (headL r)).toAddSubgroup.index * (M.comap (consL r)).toAddSubgroup.index := by
  have hπ : Function.Surjective (headL (O := O) r).toAddMonoidHom :=
    fun a => ⟨Fin.cons a 0, by simp [headL_apply]⟩
  have hι : (consL (O := O) r).toAddMonoidHom.range = (headL (O := O) r).toAddMonoidHom.ker := by
    ext x
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe,
      headL_apply, consL_apply]
    constructor
    · rintro ⟨y, rfl⟩
      simp
    · intro h
      exact ⟨Fin.tail x, by rw [← h]; exact Fin.cons_self_tail x⟩
  have := index_eq_mul_of_exact _ hπ _ hι M.toAddSubgroup
  rw [this]
  congr 2
  all_goals (ext x; simp)

theorem le_of_lift {r : ℕ} (M1 M2 : Submodule O (Fin (r+1) → O)) (g : O)
    (hI : M1.map (headL r) ≤ Ideal.span {g}) (hc : M1.comap (consL r) ≤ M2.comap (consL r))
    (w1 w2 : Fin (r+1) → O) (hw1 : w1 ∈ M1) (hw2 : w2 ∈ M2) (h1 : w1 0 = g) (h2 : w2 0 = g)
    (hd : Fin.tail w1 - Fin.tail w2 ∈ M2.comap (consL r)) : M1 ≤ M2 := by
  intro x hx
  have hx0 : x 0 ∈ Ideal.span {g} := hI (Submodule.mem_map_of_mem hx)
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.mp hx0
  have hA : Fin.tail x - c • Fin.tail w1 ∈ M2.comap (consL r) := by
    apply hc
    rw [Submodule.mem_comap]
    have : consL r (Fin.tail x - c • Fin.tail w1) = x - c • w1 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [consL_apply, h1, hc']
      · simp [consL_apply, Fin.tail]
    rw [this]
    exact M1.sub_mem hx (M1.smul_mem c hw1)
  have key : x = consL r (Fin.tail x - c • Fin.tail w1) + c • consL r (Fin.tail w1 - Fin.tail w2)
      + c • w2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [consL_apply, h2, hc']
    · simp only [consL_apply, Fin.tail, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Fin.cons_succ,
        smul_eq_mul]
      ring
  rw [key]
  exact M2.add_mem (M2.add_mem hA (M2.smul_mem c hd)) (M2.smul_mem c hw2)

end GlobalTheory.SubZeta

namespace GlobalTheory.SubZeta

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fiber_card_le {r : ℕ} (I : Ideal O) (M' : Submodule O (Fin r → O))
    (hM' : M'.toAddSubgroup.index ≠ 0) (S : Finset (Submodule O (Fin (r+1) → O)))
    (hS : ∀ M ∈ S, M.map (headL r) = I ∧ M.comap (consL r) = M') :
    S.card ≤ M'.toAddSubgroup.index := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  have hex : ∀ M ∈ S, ∃ w ∈ M, w 0 = g := by
    intro M hM
    have : g ∈ M.map (headL r) := by
      rw [(hS M hM).1, hg]
      exact Ideal.mem_span_singleton_self g
    obtain ⟨w, hw, hw0⟩ := Submodule.mem_map.mp this
    exact ⟨w, hw, hw0⟩
  choose! w hwM hw0 using hex
  haveI : Finite ((Fin r → O) ⧸ M'.toAddSubgroup) := Nat.finite_of_card_ne_zero hM'
  haveI := Fintype.ofFinite ((Fin r → O) ⧸ M'.toAddSubgroup)
  have hinj : Set.InjOn (fun M => (QuotientAddGroup.mk (Fin.tail (w M)) :
      (Fin r → O) ⧸ M'.toAddSubgroup)) S := by
    intro M1 h1 M2 h2 heq
    have hd : -Fin.tail (w M1) + Fin.tail (w M2) ∈ M' := (QuotientAddGroup.eq).mp heq
    have hd1 : Fin.tail (w M1) - Fin.tail (w M2) ∈ M' := by
      have := M'.neg_mem hd
      rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
    have hd2 : Fin.tail (w M2) - Fin.tail (w M1) ∈ M' := by
      rwa [neg_add_eq_sub] at hd
    apply le_antisymm
    · refine le_of_lift M1 M2 g ?_ ?_ _ _ (hwM M1 h1) (hwM M2 h2) (hw0 M1 h1) (hw0 M2 h2) ?_
      · rw [(hS M1 h1).1, hg]
      · rw [(hS M1 h1).2, (hS M2 h2).2]
      · rw [(hS M2 h2).2]; exact hd1
    · refine le_of_lift M2 M1 g ?_ ?_ _ _ (hwM M2 h2) (hwM M1 h1) (hw0 M2 h2) (hw0 M1 h1) ?_
      · rw [(hS M2 h2).1, hg]
      · rw [(hS M1 h1).2, (hS M2 h2).2]
      · rw [(hS M1 h1).2]; exact hd2
  calc S.card ≤ (Finset.univ : Finset ((Fin r → O) ⧸ M'.toAddSubgroup)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = M'.toAddSubgroup.index := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        rfl

theorem main_bound [Finite (IsLocalRing.ResidueField O)] : ∀ (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ →
    ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) →
    ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  classical
  intro r
  induction r with
  | zero =>
    intro σ _ C _
    have hC : C ⊆ {⊤} := fun M _ => Finset.mem_singleton.mpr (Subsingleton.elim _ _)
    calc ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ)
        ≤ ∑ M ∈ ({⊤} : Finset (Submodule O (Fin 0 → O))), (M.toAddSubgroup.index : ℝ) ^ (-σ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hC (fun _ _ _ => by positivity)
      _ = ∏ i ∈ Finset.range 0,
            (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by simp
  | succ r ih =>
    intro σ hσ C hC
    set q : ℝ := (Nat.card (IsLocalRing.ResidueField O) : ℝ) with hqdef
    have hσ' : (r : ℝ) - 1 < σ - 1 := by push_cast at hσ; linarith
    have hσ0 : 0 < σ := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      push_cast at hσ; linarith
    let p : Submodule O (Fin (r+1) → O) → Ideal O × Submodule O (Fin r → O) :=
      fun M => (M.map (headL r), M.comap (consL r))
    have hidx : ∀ M : Submodule O (Fin (r+1) → O), M.toAddSubgroup.index =
        (p M).1.toAddSubgroup.index * (p M).2.toAddSubgroup.index := fun M => index_split M
    have hC1 : ∀ x ∈ C.image p, x.1.toAddSubgroup.index ≠ 0 ∧ x.2.toAddSubgroup.index ≠ 0 := by
      intro x hx
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hx
      have := hC M hM
      rw [hidx] at this
      exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
    set D1 := (C.image p).image Prod.fst
    set D2 := (C.image p).image Prod.snd
    have hD1 : ∀ I ∈ D1, I.toAddSubgroup.index ≠ 0 := by
      intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hC1 x hx).1
    have hD2 : ∀ N ∈ D2, N.toAddSubgroup.index ≠ 0 := by
      intro N hN
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hN
      exact (hC1 x hx).2
    have hq1 : (1 : ℝ) < q := by
      have := Finite.one_lt_card (α := IsLocalRing.ResidueField O)
      rw [hqdef]
      exact_mod_cast this
    have hx1 : q ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    calc ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ)
        = ∑ x ∈ C.image p, ∑ M ∈ C with p M = x, (M.toAddSubgroup.index : ℝ) ^ (-σ) :=
          (Finset.sum_fiberwise_of_maps_to (fun M hM => Finset.mem_image_of_mem p hM) _).symm
      _ ≤ ∑ x ∈ C.image p, (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
            (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hterm : ∀ M ∈ C.filter (fun M => p M = x), (M.toAddSubgroup.index : ℝ) ^ (-σ) =
              (x.1.toAddSubgroup.index : ℝ) ^ (-σ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by
            intro M hM
            rw [Finset.mem_filter] at hM
            rw [hidx M, hM.2, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
          have hcard : ((C.filter (fun M => p M = x)).card : ℝ) ≤ x.2.toAddSubgroup.index := by
            exact_mod_cast fiber_card_le x.1 x.2 (hC1 x hx).2 _ (fun M hM => by
              rw [Finset.mem_filter] at hM
              rw [← hM.2]
              exact ⟨rfl, rfl⟩)
          have hpos2 : (0 : ℝ) < x.2.toAddSubgroup.index := by
            exact_mod_cast Nat.pos_of_ne_zero (hC1 x hx).2
          have hsplit : (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) =
              x.2.toAddSubgroup.index * (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by
            rw [show -(σ - 1) = 1 + -σ by ring, Real.rpow_add hpos2, Real.rpow_one]
          rw [hsplit]
          have ha : (0 : ℝ) ≤ (x.1.toAddSubgroup.index : ℝ) ^ (-σ) := by positivity
          have hb : (0 : ℝ) ≤ (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by positivity
          calc ((C.filter (fun M => p M = x)).card : ℝ) *
                ((x.1.toAddSubgroup.index : ℝ) ^ (-σ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ))
              = (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
                  (((C.filter (fun M => p M = x)).card : ℝ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ)) := by
                ring
            _ ≤ (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
                  ((x.2.toAddSubgroup.index : ℝ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ)) := by
                gcongr
      _ ≤ ∑ x ∈ D1 ×ˢ D2, (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
            (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro _ _ _
            positivity
      _ = (∑ I ∈ D1, (I.toAddSubgroup.index : ℝ) ^ (-σ)) *
            ∑ N ∈ D2, (N.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ (1 - q ^ (-σ))⁻¹ * ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - (σ - 1)))⁻¹ := by
          apply mul_le_mul (sum_ideal_le σ hσ0 D1 hD1) (ih (σ - 1) hσ' D2 hD2)
          · exact Finset.sum_nonneg (fun _ _ => by positivity)
          · exact (inv_pos.mpr (by linarith)).le
      _ = ∏ i ∈ Finset.range (r + 1), (1 - q ^ ((i : ℝ) - σ))⁻¹ := by
          rw [Finset.prod_range_succ', mul_comm]
          congr 1
          · apply Finset.prod_congr rfl
            intro i _
            congr 3
            push_cast
            ring
          · simp

theorem sum_index_rpow_le : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ →
    ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) →
    ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ :=
  fun _ _ _ _ _ r σ hσ C hC => main_bound r σ hσ C hC

end GlobalTheory.SubZeta
