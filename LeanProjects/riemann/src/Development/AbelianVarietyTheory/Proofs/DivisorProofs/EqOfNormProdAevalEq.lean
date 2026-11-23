import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PadicRootNorm

open Polynomial Filter Topology

variable {l : ℕ} [Fact l.Prime]

theorem norm_prod_map {β : Type*} (s : Multiset β) (f : β → PadicAlgCl l) :
    ‖(s.map f).prod‖ = (s.map fun a => ‖f a‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

open Classical in
theorem eventually_norm_prod (s : Multiset (PadicAlgCl l)) (M : ℚ_[l][X]) :
    ∀ᶠ n : ℕ in atTop, ‖(s.map fun a => aeval a (M + C ((l : ℚ_[l]) ^ n))).prod‖ =
      ‖(l : ℚ_[l])‖ ^ (n * (s.filter fun a => aeval a M = 0).card) *
        ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod := by
  have hl : Tendsto (fun n : ℕ => ‖(l : ℚ_[l])‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one
  have hev : ∀ᶠ n : ℕ in atTop, ∀ a ∈ (s.filter fun a => ¬ aeval a M = 0).toFinset,
      ‖(l : ℚ_[l])‖ ^ n < ‖aeval a M‖ := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have : aeval a M ≠ 0 := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 ha)).2
    exact (tendsto_order.1 hl).2 _ (norm_pos_iff.2 this)
  filter_upwards [hev] with n hn
  conv_lhs => rw [← Multiset.filter_add_not (fun a => aeval a M = 0) s]
  rw [Multiset.map_add, Multiset.prod_add, norm_mul, norm_prod_map, norm_prod_map]
  congr 1
  · rw [Multiset.map_congr rfl (g := fun _ => ‖(l : ℚ_[l])‖ ^ n), Multiset.map_const',
      Multiset.prod_replicate, ← pow_mul]
    intro a ha
    have h0 : aeval a M = 0 := (Multiset.mem_filter.1 ha).2
    rw [map_add, aeval_C, h0, zero_add, norm_algebraMap', norm_pow]
  · apply congrArg
    apply Multiset.map_congr rfl
    intro a ha
    have hlt := hn a (Multiset.mem_toFinset.2 ha)
    have hc : ‖algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
      rw [norm_algebraMap', norm_pow]
    rw [map_add, aeval_C, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hc]; exact hlt.ne'),
      hc, max_eq_left hlt.le]

open Classical in
theorem card_filter_eq (s t : Multiset (PadicAlgCl l))
    (h : ∀ F : ℚ_[l][X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (M : ℚ_[l][X]) :
    (s.filter fun a => aeval a M = 0).card = (t.filter fun a => aeval a M = 0).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_norm_prod s M).and (eventually_norm_prod t M))
  set x := ‖(l : ℚ_[l])‖ with hxdef
  have hx0 : 0 < x := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hx1 : x < 1 := Padic.norm_p_lt_one
  set k := (s.filter fun a => aeval a M = 0).card
  set k' := (t.filter fun a => aeval a M = 0).card
  set c := ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  set c' := ((t.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  have hc' : 0 < c' := Multiset.prod_pos fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
    exact norm_pos_iff.2 (Multiset.mem_filter.1 ha).2
  have e1 : x ^ (N * k) * c = x ^ (N * k') * c' := by
    rw [← (hN N le_rfl).1, ← (hN N le_rfl).2, h]
  have e2 : x ^ ((N + 1) * k) * c = x ^ ((N + 1) * k') * c' := by
    rw [← (hN (N + 1) (Nat.le_succ N)).1, ← (hN (N + 1) (Nat.le_succ N)).2, h]
  have e3 : x ^ k * (x ^ (N * k') * c') = x ^ k' * (x ^ (N * k') * c') := by
    calc x ^ k * (x ^ (N * k') * c') = x ^ k * (x ^ (N * k) * c) := by rw [e1]
      _ = x ^ ((N + 1) * k) * c := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
      _ = x ^ ((N + 1) * k') * c' := e2
      _ = x ^ k' * (x ^ (N * k') * c') := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
  have hne : x ^ (N * k') * c' ≠ 0 := by positivity
  exact pow_right_injective₀ hx0 hx1.ne (mul_right_cancel₀ hne e3)

theorem monic_eq_one_of_no_root {P : ℚ_[l][X]} (hP : P.Monic)
    (h : ∀ a : PadicAlgCl l, a ∉ P.aroots (PadicAlgCl l)) : P = 1 := by
  by_contra hne
  have hd : P.degree ≠ 0 := by
    intro hd
    exact hne (eq_one_of_monic_natDegree_zero hP (natDegree_eq_of_degree_eq_some hd))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero (PadicAlgCl l) P hd
  exact h a (mem_aroots.2 ⟨hP.ne_zero, ha⟩)

open Classical in
theorem exists_root_minpoly_eq_of_card_eq (P Q : ℚ_[l][X]) (hQ : Q ≠ 0)
    (hc : ∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card)
    (a : PadicAlgCl l) (ha : a ∈ P.aroots (PadicAlgCl l)) :
    ∃ b ∈ Q.aroots (PadicAlgCl l), minpoly ℚ_[l] a = minpoly ℚ_[l] b := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have h1 : 0 < ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨a, Multiset.mem_filter.2 ⟨ha, minpoly.aeval _ _⟩⟩
  rw [hc a] at h1
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 h1
  obtain ⟨hbQ, hbM⟩ := Multiset.mem_filter.1 hb
  exact ⟨b, hbQ, minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hbM (minpoly.monic hint)⟩

open Classical in
theorem eq_of_card_filter (n : ℕ) : ∀ P Q : ℚ_[l][X], P.natDegree = n → P.Monic → Q.Monic →
    (∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card) → P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hn hP hQ hc
  by_cases hr : ∃ a : PadicAlgCl l, a ∈ P.aroots (PadicAlgCl l)
  · obtain ⟨a, ha⟩ := hr
    have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
    obtain ⟨b, hbQ, hab⟩ := exists_root_minpoly_eq_of_card_eq P Q hQ.ne_zero hc a ha
    have hMQ : minpoly ℚ_[l] a ∣ Q := by rw [hab]; exact minpoly.dvd _ _ (mem_aroots.1 hbQ).2
    have hMP : minpoly ℚ_[l] a ∣ P := minpoly.dvd _ _ (mem_aroots.1 ha).2
    have hM : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
    have hMpos := minpoly.natDegree_pos hint
    obtain ⟨P', rfl⟩ := hMP
    obtain ⟨Q', rfl⟩ := hMQ
    have hP' := hM.of_mul_monic_left hP
    have hQ' := hM.of_mul_monic_left hQ
    have hdeg : (minpoly ℚ_[l] a * P').natDegree = (minpoly ℚ_[l] a).natDegree + P'.natDegree :=
      hM.natDegree_mul hP'
    rw [ih P'.natDegree (by omega) P' Q' rfl hP' hQ' ?_]
    intro b
    have h := hc b
    rw [aroots_mul hP.ne_zero, aroots_mul hQ.ne_zero, Multiset.filter_add, Multiset.filter_add,
      Multiset.card_add, Multiset.card_add] at h
    omega
  · push_neg at hr
    have hr' : ∀ b : PadicAlgCl l, b ∉ Q.aroots (PadicAlgCl l) := by
      intro b hb
      obtain ⟨a, haP, hab⟩ := exists_root_minpoly_eq_of_card_eq Q P hP.ne_zero (fun c => (hc c).symm) b hb
      have hint : IsIntegral ℚ_[l] b := Algebra.IsIntegral.isIntegral b
      exact hr a haP
    rw [monic_eq_one_of_no_root hP hr, monic_eq_one_of_no_root hQ hr']

theorem norm_eq_rat (s t : Multiset (PadicAlgCl l)) (hst : Multiset.card s = Multiset.card t)
    (h : ∀ F : ℤ[X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (R : ℚ[X]) :
    ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) R
  set G := IsLocalization.integerNormalization (nonZeroDivisors ℤ) R
  have key : ∀ a : PadicAlgCl l, aeval a G = ((b : ℤ) : PadicAlgCl l) * aeval a (R.map (algebraMap ℚ ℚ_[l])) := by
    intro a
    rw [aeval_map_algebraMap, ← aeval_map_algebraMap ℚ a G, hb, map_zsmul, zsmul_eq_mul]
  have hb0 : ((b : ℤ) : PadicAlgCl l) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero b)
  have hG := h G
  simp only [key] at hG
  rw [Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const', Multiset.map_const',
    Multiset.prod_replicate, Multiset.prod_replicate, norm_mul, norm_mul, hst] at hG
  exact mul_left_cancel₀ (by simpa using hb0) hG

theorem norm_eq_all (s t : Multiset (PadicAlgCl l))
    (h : ∀ R : ℚ[X], ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖)
    (F : ℚ_[l][X]) :
    ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖ := by
  have hr : ∀ (n i : ℕ), ∃ q : ℚ, ‖F.coeff i - q‖ < 1 / ((n : ℝ) + 1) :=
    fun n i => Padic.rat_dense l _ (by positivity)
  choose r hr using hr
  set D := F.natDegree
  let R : ℕ → ℚ[X] := fun n => ∑ i ∈ Finset.range (D + 1), C (r n i) * Polynomial.X ^ i
  have hcoef : ∀ i, Tendsto (fun n => ((r n i : ℚ) : ℚ_[l])) atTop (𝓝 (F.coeff i)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact (hr n i).le
  have hval : ∀ a : PadicAlgCl l, Tendsto (fun n => aeval a ((R n).map (algebraMap ℚ ℚ_[l])))
      atTop (𝓝 (aeval a F)) := by
    intro a
    have e : ∀ n, aeval a ((R n).map (algebraMap ℚ ℚ_[l])) =
        ∑ i ∈ Finset.range (D + 1), algebraMap ℚ_[l] (PadicAlgCl l) ((r n i : ℚ) : ℚ_[l]) * a ^ i := by
      intro n
      rw [aeval_map_algebraMap]
      simp [R, map_sum]
    simp only [e]
    rw [aeval_eq_sum_range]
    simp only [Algebra.smul_def]
    exact tendsto_finset_sum _ fun i _ =>
      (((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).tendsto _).comp (hcoef i)).mul_const _
  have hs := (tendsto_multiset_prod s fun a _ => hval a).norm
  have ht := (tendsto_multiset_prod t fun a _ => hval a).norm
  exact tendsto_nhds_unique hs (ht.congr fun n => (h (R n)).symm)

theorem card_aroots (P : ℚ_[l][X]) : Multiset.card (P.aroots (PadicAlgCl l)) = P.natDegree := by
  rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem eq_of_norm_prod_aeval_eq : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic →
    P.natDegree = Q.natDegree →
    (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ =
      ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  intro l _ P Q hP hQ hdeg h
  classical
  have hcard : Multiset.card (P.aroots (PadicAlgCl l)) = Multiset.card (Q.aroots (PadicAlgCl l)) := by
    rw [card_aroots, card_aroots, hdeg]
  have hall := norm_eq_all _ _ (norm_eq_rat _ _ hcard h)
  exact eq_of_card_filter _ P Q rfl hP hQ fun a => card_filter_eq _ _ hall _

end GlobalTheory.PadicRootNorm
