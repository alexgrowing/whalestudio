import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private theorem tele {ι G : Type} [LinearOrder ι] [AddCommGroup G] (f : Finset ι → G) (t : Finset ι) :
    ∑ j ∈ t, GlobalTheory.cubeSign t j • (f (t.filter (· < j)) + f (t.filter (· ≤ j))) =
      f ∅ - ((-1 : ℤ) ^ t.card) • f t := by
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert m t hm ih =>
    have hnot : m ∉ t := fun h => lt_irrefl _ (hm m h)
    have h1 : (insert m t).filter (· < m) = t := by
      ext y; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h, h2⟩
        · exact absurd h2 (lt_irrefl _)
        · exact h
      · intro h; exact ⟨Or.inr h, hm y h⟩
    have h2 : (insert m t).filter (· ≤ m) = insert m t := by
      apply Finset.filter_true_of_mem
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | h
      · exact le_rfl
      · exact (hm y h).le
    have h3 : GlobalTheory.cubeSign (insert m t) m = (-1) ^ t.card := by
      simp only [GlobalTheory.cubeSign, h1]
    have h4 : ∑ j ∈ t, GlobalTheory.cubeSign (insert m t) j • (f ((insert m t).filter (· < j)) + f ((insert m t).filter (· ≤ j))) =
        ∑ j ∈ t, GlobalTheory.cubeSign t j • (f (t.filter (· < j)) + f (t.filter (· ≤ j))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := hm j hj
      have a1 : (insert m t).filter (· < j) = t.filter (· < j) := by
        rw [Finset.filter_insert, if_neg (not_lt.2 hj'.le)]
      have a2 : (insert m t).filter (· ≤ j) = t.filter (· ≤ j) := by
        rw [Finset.filter_insert, if_neg (not_le.2 hj')]
      simp only [GlobalTheory.cubeSign, a1, a2]
    rw [Finset.sum_insert hnot, h1, h2, h3, h4, ih, Finset.card_insert_of_notMem hnot, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, smul_add]
    abel

end UpperTheory.Gal.productCup_of_system

namespace UpperTheory.Gal.productCup_of_system

private theorem leib {ι E E' E'' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (a : Finset ι → E) (b : Finset ι → E')
    (ha : a ∅ = 0) (hb : b ∅ = 0) (hδ : ∀ t, ∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i) = 0) (t : Finset ι) :
    ∑ i ∈ t, GlobalTheory.cubeSign t i • cupE μ a b (t.erase i) =
      ∑ j ∈ t, μ (∑ i ∈ t.filter (· ≤ j), GlobalTheory.cubeSign (t.filter (· ≤ j)) i • a ((t.filter (· ≤ j)).erase i))
        (b (t.filter (j ≤ ·))) := by
  let f : Finset ι → E'' := fun u => μ (a u) (b (t \ u))
  have hf0 : f ∅ = 0 := by simp [f, ha]
  have hft : f t = 0 := by simp [f, hb]
  have ht := tele f t
  rw [hf0, hft, smul_zero, sub_zero] at ht
  have key : ∀ j ∈ t, ∑ i ∈ t.erase j, GlobalTheory.cubeSign t i •
        μ (a ((t.erase i).filter (· ≤ j))) (b ((t.erase i).filter (j ≤ ·))) =
      μ (∑ i ∈ t.filter (· ≤ j), GlobalTheory.cubeSign (t.filter (· ≤ j)) i • a ((t.filter (· ≤ j)).erase i))
          (b (t.filter (j ≤ ·)))
        - GlobalTheory.cubeSign t j • (f (t.filter (· < j)) + f (t.filter (· ≤ j))) := by
    intro j hj
    have hf1 : f (t.filter (· < j)) = μ (a (t.filter (· < j))) (b (t.filter (j ≤ ·))) := by
      have : t \ t.filter (· < j) = t.filter (j ≤ ·) := by ext y; grind
      simp only [f, this]
    have hf2 : f (t.filter (· ≤ j)) = μ (a (t.filter (· ≤ j))) (b (t.filter (j < ·))) := by
      have : t \ t.filter (· ≤ j) = t.filter (j < ·) := by ext y; grind
      simp only [f, this]
    rw [hf1, hf2]
    set u := t.filter (j ≤ ·) with hu
    set v := t.filter (· ≤ j) with hv
    have ev : ∀ (G : ι → E), ∑ i ∈ v, G i = G j + ∑ i ∈ t.filter (· < j), G i := by
      intro G
      have : v = insert j (t.filter (· < j)) := by ext y; grind
      rw [this, Finset.sum_insert (by simp)]
    have eu : ∀ (G : ι → E'), ∑ i ∈ u, G i = G j + ∑ i ∈ t.filter (j < ·), G i := by
      intro G
      have : u = insert j (t.filter (j < ·)) := by ext y; grind
      rw [this, Finset.sum_insert (by simp)]
    have hs := Finset.sum_filter_add_sum_filter_not (t.erase j) (· < j) (fun i => GlobalTheory.cubeSign t i •
        μ (a ((t.erase i).filter (· ≤ j))) (b ((t.erase i).filter (j ≤ ·))))
    have e1 : (t.erase j).filter (· < j) = t.filter (· < j) := by ext y; grind
    have e2 : (t.erase j).filter (fun x => ¬ x < j) = t.filter (j < ·) := by ext y; grind
    rw [e1, e2] at hs
    have hA : ∑ i ∈ t.filter (· < j), GlobalTheory.cubeSign t i •
        μ (a ((t.erase i).filter (· ≤ j))) (b ((t.erase i).filter (j ≤ ·))) =
        μ (∑ i ∈ t.filter (· < j), GlobalTheory.cubeSign v i • a (v.erase i)) (b u) := by
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < j := (Finset.mem_filter.1 hi).2
      have c1 : (t.erase i).filter (· ≤ j) = v.erase i := by ext y; grind
      have c2 : (t.erase i).filter (j ≤ ·) = u := by ext y; grind
      have c3 : GlobalTheory.cubeSign v i = GlobalTheory.cubeSign t i := by
        have : v.filter (· < i) = t.filter (· < i) := by ext y; grind
        simp only [GlobalTheory.cubeSign, this]
      rw [c1, c2, c3, map_zsmul, LinearMap.smul_apply]
    have hB : ∑ i ∈ t.filter (j < ·), GlobalTheory.cubeSign t i •
        μ (a ((t.erase i).filter (· ≤ j))) (b ((t.erase i).filter (j ≤ ·))) =
        -(GlobalTheory.cubeSign t j • μ (a v) (b (t.filter (j < ·)))) := by
      have hd := hδ u
      rw [eu] at hd
      have c0 : u.erase j = t.filter (j < ·) := by ext y; grind
      have c00 : GlobalTheory.cubeSign u j = 1 := by
        have : u.filter (· < j) = ∅ := by ext y; grind
        simp [GlobalTheory.cubeSign, this]
      rw [c0, c00, one_smul] at hd
      have hb2 := eq_neg_of_add_eq_zero_right hd
      calc _ = GlobalTheory.cubeSign t j • μ (a v) (∑ i ∈ t.filter (j < ·), GlobalTheory.cubeSign u i • b (u.erase i)) := by
            rw [map_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : j < i := (Finset.mem_filter.1 hi).2
            have d1 : (t.erase i).filter (· ≤ j) = v := by ext y; grind
            have d2 : (t.erase i).filter (j ≤ ·) = u.erase i := by ext y; grind
            have d3 : GlobalTheory.cubeSign t i = GlobalTheory.cubeSign t j * GlobalTheory.cubeSign u i := by
              have h1 : t.filter (· < i) = t.filter (· < j) ∪ u.filter (· < i) := by ext y; grind
              have h2 : Disjoint (t.filter (· < j)) (u.filter (· < i)) :=
                Finset.disjoint_left.2 (by grind)
              simp only [GlobalTheory.cubeSign]
              rw [h1, Finset.card_union_of_disjoint h2, pow_add]
            rw [d1, d2, d3, map_zsmul, mul_smul]
        _ = _ := by rw [hb2, map_neg, smul_neg]
    have c4 : v.erase j = t.filter (· < j) := by ext y; grind
    have c5 : GlobalTheory.cubeSign v j = GlobalTheory.cubeSign t j := by
      have : v.filter (· < j) = t.filter (· < j) := by ext y; grind
      simp only [GlobalTheory.cubeSign, this]
    rw [← hs, hA, hB, ev, map_add, LinearMap.add_apply, c4, c5, map_zsmul, LinearMap.smul_apply, smul_add]
    abel
  have lhs : ∑ i ∈ t, GlobalTheory.cubeSign t i • cupE μ a b (t.erase i) =
      ∑ j ∈ t, ∑ i ∈ t.erase j, GlobalTheory.cubeSign t i •
        μ (a ((t.erase i).filter (· ≤ j))) (b ((t.erase i).filter (j ≤ ·))) := by
    simp only [cupE, Finset.smul_sum]
    exact Finset.sum_comm' (by intro i j; simp only [Finset.mem_erase]; tauto)
  rw [lhs, Finset.sum_congr rfl key, Finset.sum_sub_distrib, ht, sub_zero]

end UpperTheory.Gal.productCup_of_system

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_app {ν E : Type} [LinearOrder ν] [AddCommGroup E] [Module ℂ E] (w : ν → Module.End ℂ E)
    (f : Finset ν → E) (t : Finset ν) :
    wd w f t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (f (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem wd_sgn {ν E : Type} [LinearOrder ν] [AddCommGroup E] [Module ℂ E] (w : ν → Module.End ℂ E)
    (F : Finset ν → E) (σ : ℕ → ℤ) (τ : ℤ) (t : Finset ν) (h : ∀ n, n + 1 = t.card → σ n = τ) :
    wd w (fun t' => σ t'.card • F t') t = τ • wd w F t := by
  simp only [wd_app, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h _ (Finset.card_erase_add_one hi), map_zsmul]
  exact smul_comm _ _ _

private theorem wd_cup {ν ρ E E' E'' : Type} [LinearOrder ν] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (w : ν → Module.End ℂ E) (w' : ν → Module.End ℂ E'')
    (hw : ∀ l m y, μ (w l m) y = w' l (μ m y)) (I : Finset ρ) (g : ρ → Finset ν → E) (y : ρ → E') (t : Finset ν) :
    wd w' (fun t' => ∑ i ∈ I, μ (g i t') (y i)) t = ∑ i ∈ I, μ (wd w (g i) t) (y i) := by
  simp only [wd_app, map_sum, LinearMap.sum_apply, Finset.smul_sum, map_zsmul, LinearMap.smul_apply, hw]
  exact Finset.sum_comm

private theorem tri (hW : WdUni) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] (z : κ → S) (f : Finset (Two d ⊕ₗ κ) → E)
    (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    wd (T.wt z) f (uni (uni I J) L) =
      wd (fun _ => (1 : Module.End ℂ E)) (fun I' => f (uni (uni I' J) L)) I +
      ((-1 : ℤ) ^ I.card) • wd (fun _ => (1 : Module.End ℂ E)) (fun J' => f (uni (uni I J') L)) J +
      ((-1 : ℤ) ^ (I.card + J.card)) • wd (fun l => T.act (z l)) (fun L' => f (uni (uni I J) L')) L := by
  obtain ⟨h1, -, -, -, -⟩ := hW (Two d) κ E (T.wt z) f (uni I J) L
  obtain ⟨h2, -, -, h3, -⟩ := hW (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 1) (fun b' => f (uni b' L)) I J
  have h1' : wd (T.wt z) f (uni (uni I J) L) =
      wd (fun _ => (1 : Module.End ℂ E)) (fun b' => f (uni b' L)) (uni I J) +
      ((-1 : ℤ) ^ (uni I J).card) • wd (fun l => T.act (z l)) (fun L' => f (uni (uni I J) L')) L := h1
  have h2' : wd (fun _ => (1 : Module.End ℂ E)) (fun b' => f (uni b' L)) (uni I J) =
      wd (fun _ => (1 : Module.End ℂ E)) (fun I' => f (uni (uni I' J) L)) I +
      ((-1 : ℤ) ^ I.card) • wd (fun _ => (1 : Module.End ℂ E)) (fun J' => f (uni (uni I J') L)) J := h2
  rw [h1', h2', h3]

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.rCup_of :
    WdUni → RCup := by
  intro hW d S E _ _ _ _ T S' E' E'' _ _ _ _ _ _ T' κ _ _ z z' μ p c x hμ hc hc0 hx hxs
  have hR : ∀ I J L, rcup μ p c x (uni (uni I J) L) =
      ((-1 : ℤ) ^ (p * (J.card + L.card))) • cupE μ (fun I' => c (uni (uni I' J) L)) x I := by
    intro I J L
    obtain ⟨-, a1, a2, -, -⟩ := hW (Two d) κ E'' (T'.wt z') 0 (uni I J) L
    obtain ⟨-, b1, b2, -, -⟩ := hW (Fin (d + 1)) (Fin (d + 1)) E'' (fun _ => 1) 0 I J
    simp only [rcup, a1, a2, b1, b2, cupE]
  have hx0 : x ∅ = 0 := hxs ∅ (by simp)
  have hδ : ∀ t, ∑ i ∈ t, GlobalTheory.cubeSign t i • x (t.erase i) = 0 := fun t => congrFun hx t
  funext s
  obtain ⟨-, -, -, -, hs1⟩ := hW (Two d) κ E'' (T'.wt z') 0 ∅ ∅
  obtain ⟨-, -, -, -, hs2⟩ := hW (Fin (d + 1)) (Fin (d + 1)) E'' (fun _ => 1) 0 ∅ ∅
  rw [← hs1 s, ← hs2 (lft s)]
  generalize lft (lft s) = I
  generalize rgt (lft s) = J
  generalize rgt s = L
  rw [tri hW T' z' _ I J L]
  simp only [hR]
  have t1 : wd (fun _ => (1 : Module.End ℂ E''))
      (fun I' => ((-1 : ℤ) ^ (p * (J.card + L.card))) • cupE μ (fun I' => c (uni (uni I' J) L)) x I') I =
      ((-1 : ℤ) ^ (p * (J.card + L.card))) • ∑ i ∈ I, μ (wd (fun _ => (1 : Module.End ℂ E))
        (fun I' => c (uni (uni I' J) L)) (I.filter (· ≤ i))) (x (I.filter (i ≤ ·))) := by
    simp only [wd_app, Module.End.one_apply]
    have hl := leib μ (fun I' => c (uni (uni I' J) L)) x (hc0 J L) hx0 hδ I
    rw [← hl, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have t2 : wd (fun _ => (1 : Module.End ℂ E''))
      (fun J' => ((-1 : ℤ) ^ (p * (J'.card + L.card))) • cupE μ (fun I' => c (uni (uni I' J') L)) x I) J =
      ((-1 : ℤ) ^ (p * (J.card + L.card + 1))) • ∑ i ∈ I, μ (wd (fun _ => (1 : Module.End ℂ E))
        (fun J' => c (uni (uni (I.filter (· ≤ i)) J') L)) J) (x (I.filter (i ≤ ·))) := by
    refine (wd_sgn _ _ (fun n => (-1 : ℤ) ^ (p * (n + L.card))) ((-1 : ℤ) ^ (p * (J.card + L.card + 1))) J ?_).trans ?_
    · intro n hn
      rw [← hn, show p * (n + 1 + L.card + 1) = p * (n + L.card) + 2 * p by ring, pow_add, pow_mul]
      simp
    · congr 1
      exact wd_cup μ _ _ (fun _ _ _ => rfl) I (fun i J' => c (uni (uni (I.filter (· ≤ i)) J') L))
        (fun i => x (I.filter (i ≤ ·))) J
  have t3 : wd (fun l => T'.act (z' l))
      (fun L' => ((-1 : ℤ) ^ (p * (J.card + L'.card))) • cupE μ (fun I' => c (uni (uni I' J) L')) x I) L =
      ((-1 : ℤ) ^ (p * (J.card + L.card + 1))) • ∑ i ∈ I, μ (wd (fun l => T.act (z l))
        (fun L' => c (uni (uni (I.filter (· ≤ i)) J) L')) L) (x (I.filter (i ≤ ·))) := by
    refine (wd_sgn _ _ (fun n => (-1 : ℤ) ^ (p * (J.card + n))) ((-1 : ℤ) ^ (p * (J.card + L.card + 1))) L ?_).trans ?_
    · intro n hn
      rw [← hn, show p * (J.card + (n + 1) + 1) = p * (J.card + n) + 2 * p by ring, pow_add, pow_mul]
      simp
    · congr 1
      exact wd_cup μ _ _ hμ I (fun i L' => c (uni (uni (I.filter (· ≤ i)) J) L'))
        (fun i => x (I.filter (i ≤ ·))) L
  rw [t1, t2, t3]
  simp only [Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases hy : (I.filter (i ≤ ·)).card = p + 1
  · have h0 := tri hW T z c (I.filter (· ≤ i)) J L
    rw [hc] at h0
    have hcard : I.card = (I.filter (· ≤ i)).card + p := by
      have e1 : I.filter (· ≤ i) = insert i (I.filter (· < i)) := by ext y; grind
      have e2 : (I.filter (· < i)).card + (I.filter (i ≤ ·)).card = I.card := by
        have : I = I.filter (· < i) ∪ I.filter (i ≤ ·) := by ext y; grind
        conv_rhs => rw [this]
        exact (Finset.card_union_of_disjoint (Finset.disjoint_left.2 (by grind))).symm
      rw [e1, Finset.card_insert_of_notMem (by simp)]
      omega
    set n := (I.filter (· ≤ i)).card with hn
    have hs1 : ((-1 : ℤ) ^ I.card) * (-1) ^ (p * (J.card + L.card + 1)) =
        (-1) ^ (p * (J.card + L.card)) * (-1) ^ n := by
      rw [hcard, ← pow_add, ← pow_add,
        show n + p + p * (J.card + L.card + 1) = p * (J.card + L.card) + n + 2 * p by ring, pow_add _ _ (2 * p),
        pow_mul]
      simp
    have hs2 : ((-1 : ℤ) ^ (I.card + J.card)) * (-1) ^ (p * (J.card + L.card + 1)) =
        (-1) ^ (p * (J.card + L.card)) * (-1) ^ (n + J.card) := by
      rw [pow_add, pow_add _ n, mul_right_comm, hs1]
      ring
    have hz := congrArg (fun m => ((-1 : ℤ) ^ (p * (J.card + L.card))) • μ m (x (I.filter (i ≤ ·)))) h0
    simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, smul_zero, map_add, LinearMap.add_apply, map_zsmul,
      LinearMap.smul_apply, smul_add, smul_smul] at hz
    simp only [smul_smul, hs1, hs2]
    exact hz.symm
  · simp [hxs _ hy]
