import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

variable {D : D7} {L : SizeData₂ D}

section marg

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

open Classical in

def margC (φ : β → α) (T : α → Finset ℤ) : ℕ := ∏ t, (if ∃ i, φ i = t then 1 else (T t).card)

open Classical in
theorem marg_fibre (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (a' : β → ℤ)
    (ha' : ∀ i, a' i ∈ T (φ i)) :
    ((Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a')).card = margC φ T := by
  have key : (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a') =
      Fintype.piFinset (fun t => if h : ∃ i, φ i = t then ({a' h.choose} : Finset ℤ) else T t) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hT, rfl⟩ t
      split_ifs with h
      · simp only [Finset.mem_singleton]
        rw [h.choose_spec]
      · exact hT t
    · intro h
      refine ⟨fun t => ?_, funext fun i => ?_⟩
      · have ht := h t
        split_ifs at ht with hx
        · rw [Finset.mem_singleton] at ht
          rw [ht]
          have := ha' hx.choose
          rwa [hx.choose_spec] at this
        · exact ht
      · have ht := h (φ i)
        rw [dif_pos (⟨i, rfl⟩ : ∃ j, φ j = φ i), Finset.mem_singleton] at ht
        show a (φ i) = a' i
        rw [ht]
        exact congrArg a' (hφ (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, φ j = φ i)))
  rw [key, Fintype.card_piFinset]
  unfold margC
  refine Finset.prod_congr rfl fun t _ => ?_
  split_ifs <;> simp

open Classical in
theorem marg_sum (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (T' : β → Finset ℤ)
    (hT : ∀ i, T' i = T (φ i)) (F : (β → ℤ) → ℝ) :
    ∑ a ∈ Fintype.piFinset T, F (fun i => a (φ i)) = (margC φ T : ℝ) * ∑ a' ∈ Fintype.piFinset T', F a' := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset T) (t := Fintype.piFinset T')
    (g := fun a i => a (φ i)) (f := fun a => F (fun i => a (φ i))) (fun a ha => by
      rw [Fintype.mem_piFinset] at ha ⊢
      intro i
      rw [hT]
      exact ha (φ i))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' ha' => ?_
  rw [Fintype.mem_piFinset] at ha'
  have e : ∑ a ∈ (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a'), F (fun i => a (φ i)) =
      ∑ a ∈ (Fintype.piFinset T).filter (fun a => (fun i => a (φ i)) = a'), F a' :=
    Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]
  rw [e, Finset.sum_const, marg_fibre φ hφ T a' (fun i => by rw [← hT]; exact ha' i), nsmul_eq_mul]

theorem marg_card (φ : β → α) (hφ : Function.Injective φ) (T : α → Finset ℤ) (T' : β → Finset ℤ)
    (hT : ∀ i, T' i = T (φ i)) :
    ((Fintype.piFinset T).card : ℝ) = (margC φ T : ℝ) * ((Fintype.piFinset T').card : ℝ) := by
  have h := marg_sum φ hφ T T' hT (fun _ => (1 : ℝ))
  simpa using h

end marg

theorem frobenius_step_large_order (p : ℕ) (h : IsResidueClassZero D p) : stepP D p = hP D p := by
  unfold stepP
  rw [if_neg]
  intro hs
  simp only [IsSg] at hs
  simp only [IsResidueClassZero] at h
  rw [h] at hs
  cases hs

def phi (D : D7) (p : ℕ) (t0 : HH D) : Fin (addOrderOf (hP D p)) → HH D := fun i => t0 + (i : ℕ) • hP D p

theorem phi_inj (p : ℕ) (t0 : HH D) : Function.Injective (phi D p t0) := by
  intro i j hij
  simp only [phi, add_right_inj] at hij
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf i.2 j.2 hij)

theorem bs_iter (X : Inst D L) (h t : HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem bs_idem (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  calc X.bs h (X.bs h t) = X.bs h (X.bs h t + i • h) := (bs_iter X h _ i).symm
    _ = X.bs h t := by rw [hi]

theorem bs_rep (X : Inst D L) (p : ℕ) (t0 : HH D) (ht0 : t0 ∈ reps X p) : X.bs (stepP D p) t0 = t0 := by
  unfold reps at ht0
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht0
  obtain ⟨t, rfl⟩ := ht0
  exact bs_idem X _ t

theorem topsOn_eq_image (X : Inst D L) (p : ℕ) (hc : IsResidueClassZero D p) (t0 : HH D) (ht0 : t0 ∈ reps X p) :
    topsOn X p t0 = (topsPos D p t0).image (phi D p t0) := by
  have hs := frobenius_step_large_order p hc
  have hr := bs_rep X p t0 ht0
  rw [hs] at hr
  ext t
  simp only [topsOn, topsPos, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, phi, hs]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb (hP D p) t
    rw [hbt] at hi
    have hpos : 0 < addOrderOf (hP D p) := addOrderOf_pos _
    refine ⟨⟨i % addOrderOf (hP D p), Nat.mod_lt _ hpos⟩, ?_, ?_⟩ <;>
      simp only [Fin.val_mk, mod_addOrderOf_nsmul, hi, htT]
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, by rw [bs_iter, hr]⟩

theorem Nv_eq (X : Inst D L) (p : ℕ) (hc : IsResidueClassZero D p) (t0 : HH D) (ht0 : t0 ∈ reps X p) :
    Nv X p t0 = (topsPos D p t0).card := by
  unfold Nv
  rw [topsOn_eq_image X p hc t0 ht0, Finset.card_image_of_injective _ (phi_inj p t0)]

theorem sum_Nv_le (X : Inst D L) (p : ℕ) (S : Finset (HH D)) : ∑ t0 ∈ S, Nv X p t0 ≤ D.host.TT.card := by
  classical
  have hd : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (topsOn X p x) (topsOn X p y) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro t hx hy
    simp only [topsOn, Finset.mem_filter] at hx hy
    exact hxy (hx.2.symm.trans hy.2)
  simp only [Nv]
  rw [← Finset.card_biUnion hd]
  refine Finset.card_le_card (Finset.biUnion_subset.mpr fun t0 _ => ?_)
  unfold topsOn
  exact Finset.filter_subset _ _

theorem mem_goodReps {X : Inst D L} {p : ℕ} {t0 : HH D} (h : t0 ∈ goodReps X p) : t0 ∈ reps X p ∧ Good X p t0 := by
  unfold goodReps at h
  simp only [Finset.mem_filter] at h
  exact h

structure NumMean (D : D7) (L : SizeData₂ D) (K : Consts) (Cm : ℝ) : Prop where

  kII : K.kII * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A) ≤ L.sc.x ^ (-12 : ℝ)

  kI : Cm * (N1 L.sc : ℝ) / L.sc.x ^ (Scale.A / 2) ≤ L.sc.x ^ (-12 : ℝ)

  second_level_lt_good_bound : L2 D L.sc < goodU L.sc.delta1

  Gp : 3 * (Gp L.sc : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4)

  winA : 1 ≤ L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))

  winB : 1 ≤ Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k

  tot : (L.sc.x ^ L.sc.eps + 1) * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ) *
    (L.sc.x ^ (L.sc.eps / 3) * (2 + L.sc.x ^ (L.sc.eps / 3))) ≤ L.sc.x ^ (-9 : ℝ) / 4

def RestHypI (X : Inst D L) (K : Consts) : Prop :=
  ∀ p, Cand D L K p → L.sc.p0 D.R.k ≤ (p : ℝ) → ∀ t0 ∈ goodReps X p,
    HypI D L K p (addOrderOf (hP D p)) (topsPos D p t0).card

theorem inBand_of_inBand0 (D : D7) (K : Consts) (s : Scale) (h : rho D K s ≤ rhoB D K s) (p : ℕ)
    (hb : InBand0 D K s p) : InBand D K s p := by
  obtain ⟨h1, h2, d, hd, hl, hu⟩ := hb
  have hX : 0 ≤ s.X' := le_trans (Nat.cast_nonneg p) h2.le
  unfold InBand
  refine ⟨h1, h2, d, hd, le_trans ?_ hl, le_trans hu ?_⟩
  · exact mul_le_mul_of_nonneg_left (by linarith) hX
  · exact mul_le_mul_of_nonneg_left (by linarith) hX

theorem meanLoc_const_le (K : Consts) (s : Scale) (n' : ℕ) (TT : Finset (Fin n')) (c : ℝ) (hc : 0 ≤ c) :
    meanLoc D K s n' TT (fun _ _ => c) ≤ c := by
  unfold meanLoc
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, mul_div_right_comm]
  rcases eq_or_ne (((boxLoc n' TT (winA D s)).card : ℝ) * ((boxLoc n' TT (winB D K s)).card : ℝ)) 0 with h | h
  · rw [h, div_zero, zero_mul]
    exact hc
  · rw [div_self h, one_mul]

theorem kapIIf_nonneg (K : Consts) (hK : K.Nonneg) (L : SizeData₂ D) (N : ℕ) : 0 ≤ kapIIf K L N := by
  have hk : 0 ≤ K.kII := hK.2.2.1
  have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  unfold kapIIf
  exact le_min zero_le_one (by positivity)

theorem kappa_nonneg_and_mean_bound (X : Inst D L) (K : Consts) (Cm : ℝ) (h8 : adm8 D L X K Cm) (N : NumMean D L K Cm)
    (hI : RestHypI X K) (hρ : rho D K L.sc ≤ rhoB D K L.sc) (p : ℕ) (hc : Cand D L K p) (hp : L.sc.p0 D.R.k ≤ (p : ℝ)) (t0 : HH D)
    (ht0 : t0 ∈ goodReps X p) :
    (∀ a b, 0 ≤ X.kapI p (addOrderOf (hP D p)) (topsPos D p t0) a b) ∧
    meanLoc D K L.sc (addOrderOf (hP D p)) (topsPos D p t0) (X.kapI p (addOrderOf (hP D p)) (topsPos D p t0)) ≤
      Cm * ((topsPos D p t0).card : ℝ) * (N1 L.sc : ℝ) / L.sc.x ^ (Scale.A / 2) := by
  have hg := (mem_goodReps ht0).2
  refine h8 p (addOrderOf (hP D p)) hc.1 (topsPos D p t0) hg N.second_level_lt_good_bound ?_ hp hc.2.1 ?_ (hI p hc hp t0 ht0)
  · have h2 : (3 * Gp L.sc : ℝ) ≤ (addOrderOf (hP D p) : ℝ) := N.Gp.trans hc.2.2.2.1
    exact_mod_cast h2
  · intro h0
    exact hc.2.2.2.2 hp (inBand_of_inBand0 D K L.sc hρ p h0)

theorem slopeEstimate_of_lemmaB_slopeLine (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Cm : ℝ) (h8 : adm8 D L X K Cm)
    (N : NumMean D L K Cm) (hI : RestHypI X K) (hρ : rho D K L.sc ≤ rhoB D K L.sc) : Conclusion2 D L X K := by
  intro p hc t0 ht0
  have hr : t0 ∈ reps X p := (mem_goodReps ht0).1
  have hN := Nv_eq X p hc.2.2.1 t0 hr
  have hII : kapIIf K L (topsPos D p t0).card ≤ (Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ) := by
    rw [hN]
    unfold kapIIf
    have := mul_le_mul_of_nonneg_left N.kII (Nat.cast_nonneg (topsPos D p t0).card : (0 : ℝ) ≤ _)
    refine le_trans (min_le_right _ _) ?_
    calc K.kII * ((topsPos D p t0).card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A)
        = ((topsPos D p t0).card : ℝ) * (K.kII * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A)) := by ring
      _ ≤ _ := this
  by_cases hp : (p : ℝ) < L.sc.p0 D.R.k
  · constructor
    · simp only [kapLoc, if_pos hp]
      exact le_trans (meanLoc_const_le K L.sc _ _ _ (kapIIf_nonneg K hK L _)) hII
    · intro _ a b
      unfold kapv kapLoc
      rw [if_pos hp]
      exact hII
  · constructor
    · simp only [kapLoc, if_neg hp]
      refine le_trans (kappa_nonneg_and_mean_bound X K Cm h8 N hI hρ p hc (not_lt.1 hp) t0 ht0).2 ?_
      rw [hN]
      have := mul_le_mul_of_nonneg_left N.kI (Nat.cast_nonneg (topsPos D p t0).card : (0 : ℝ) ≤ _)
      calc Cm * ((topsPos D p t0).card : ℝ) * (N1 L.sc : ℝ) / L.sc.x ^ (Scale.A / 2)
          = ((topsPos D p t0).card : ℝ) * (Cm * (N1 L.sc : ℝ) / L.sc.x ^ (Scale.A / 2)) := by ring
        _ ≤ _ := this
    · intro h; exact absurd h hp

theorem kapv_nonneg (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Cm : ℝ) (h8 : adm8 D L X K Cm)
    (N : NumMean D L K Cm) (hI : RestHypI X K) (hρ : rho D K L.sc ≤ rhoB D K L.sc) (p : ℕ) (hc : Cand D L K p) (t0 : HH D)
    (ht0 : t0 ∈ goodReps X p) (a b : HH D → ℤ) : 0 ≤ kapv X K a b p t0 := by
  unfold kapv kapLoc
  split_ifs with hp
  · exact kapIIf_nonneg K hK L _
  · exact (kappa_nonneg_and_mean_bound X K Cm h8 N hI hρ p hc (not_lt.mp hp) t0 ht0).1 _ _

theorem Sig_nonneg (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Cm : ℝ) (h8 : adm8 D L X K Cm)
    (N : NumMean D L K Cm) (hI : RestHypI X K) (hρ : rho D K L.sc ≤ rhoB D K L.sc) (a b : HH D → ℤ) (p : ℕ) (hc : Cand D L K p) :
    0 ≤ Sig X K a b p := by
  unfold Sig
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun t0 ht0 => kapv_nonneg X K hK Cm h8 N hI hρ p hc t0 ht0 a b)

theorem box_marg (p : ℕ) (t0 : HH D) (W : Finset ℤ) :
    ∃ c : ℝ, (∀ F : (Fin (addOrderOf (hP D p)) → ℤ) → ℝ,
        ∑ a ∈ box D W, F (wPos D p t0 a) = c * ∑ a' ∈ boxLoc _ (topsPos D p t0) W, F a') ∧
      ((box D W).card : ℝ) = c * ((boxLoc _ (topsPos D p t0) W).card : ℝ) := by
  refine ⟨_, fun F => marg_sum (phi D p t0) (phi_inj p t0) _ _ ?_ F,
    marg_card (phi D p t0) (phi_inj p t0) _ _ ?_⟩
  all_goals
    intro i
    unfold topsPos phi
    split_ifs <;> simp_all

theorem box_nonempty (W : Finset ℤ) (hW : W.Nonempty) : (box D W).Nonempty := by
  unfold box
  rw [Fintype.piFinset_nonempty]
  intro t
  split_ifs
  · exact hW
  · exact Finset.singleton_nonempty 0

theorem boxLoc_nonempty (n' : ℕ) (TT : Finset (Fin n')) (W : Finset ℤ) (hW : W.Nonempty) :
    (boxLoc n' TT W).Nonempty := by
  unfold boxLoc
  rw [Fintype.piFinset_nonempty]
  intro t
  split_ifs
  · exact hW
  · exact Finset.singleton_nonempty 0

theorem Icc_ceil_floor_nonempty (y w : ℝ) (hw : 1 ≤ w) : (Finset.Icc ⌈y⌉ ⌊y + w⌋).Nonempty := by
  rw [Finset.nonempty_Icc, Int.le_floor]
  have := Int.ceil_lt_add_one y
  linarith

theorem winA_nonempty (K : Consts) (Cm : ℝ) (N : NumMean D L K Cm) : (winA D L.sc).Nonempty := Icc_ceil_floor_nonempty _ _ N.winA

theorem winB_nonempty (K : Consts) (Cm : ℝ) (N : NumMean D L K Cm) : (winB D K L.sc).Nonempty := Icc_ceil_floor_nonempty _ _ N.winB

theorem sum_box_product_eq_mean (K : Consts) (Cm : ℝ) (N : NumMean D L K Cm) (p : ℕ) (t0 : HH D)
    (F : (Fin (addOrderOf (hP D p)) → ℤ) → (Fin (addOrderOf (hP D p)) → ℤ) → ℝ) :
    ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), F (wPos D p t0 a) (wPos D p t0 b) =
      ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
        meanLoc D K L.sc _ (topsPos D p t0) F := by
  obtain ⟨cA, hA, hcA⟩ := box_marg (D := D) p t0 (winA D L.sc)
  obtain ⟨cB, hB, hcB⟩ := box_marg (D := D) p t0 (winB D K L.sc)
  have hLA : ((boxLoc _ (topsPos D p t0) (winA D L.sc)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (boxLoc_nonempty _ _ _ (winA_nonempty K Cm N)))
  have hLB : ((boxLoc _ (topsPos D p t0) (winB D K L.sc)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (boxLoc_nonempty _ _ _ (winB_nonempty K Cm N)))
  have e1 : ∀ a, ∑ b ∈ box D (winB D K L.sc), F (wPos D p t0 a) (wPos D p t0 b) =
      cB * ∑ b' ∈ boxLoc _ (topsPos D p t0) (winB D K L.sc), F (wPos D p t0 a) b' :=
    fun a => hB (fun b' => F (wPos D p t0 a) b')
  have e2 : ∀ b', ∑ a ∈ box D (winA D L.sc), F (wPos D p t0 a) b' =
      cA * ∑ a' ∈ boxLoc _ (topsPos D p t0) (winA D L.sc), F a' b' :=
    fun b' => hA (fun a' => F a' b')
  simp_rw [e1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [e2]
  rw [← Finset.mul_sum, Finset.sum_comm, hcA, hcB]
  unfold meanLoc
  field_simp

theorem sum_kapv_le (X : Inst D L) (K : Consts) (Cm : ℝ) (N : NumMean D L K Cm) (h2 : Conclusion2 D L X K)
    (p : ℕ) (hc : Cand D L K p) (t0 : HH D) (ht0 : t0 ∈ goodReps X p) :
    ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), kapv X K a b p t0 ≤
      ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
        ((Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
  rw [show (∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), kapv X K a b p t0) = _ from
    sum_box_product_eq_mean K Cm N p t0 (fun a b => kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) a b)]
  have hm := (h2 p hc t0 ht0).1
  exact mul_le_mul_of_nonneg_left hm (by positivity)

theorem sum_Sig_le (X : Inst D L) (K : Consts) (Cm : ℝ) (N : NumMean D L K Cm) (h2 : Conclusion2 D L X K)
    (p : ℕ) (hc : Cand D L K p) :
    ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), Sig X K a b p ≤
      ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
        ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
  have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  calc ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), Sig X K a b p
      = (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc),
          kapv X K a b p t0 := by
        simp only [Sig, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ ≤ (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, ((box D (winA D L.sc)).card : ℝ) *
          ((box D (winB D K L.sc)).card : ℝ) * ((Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun t0 ht0 => sum_kapv_le X K Cm N h2 p hc t0 ht0) ?_
        positivity
    _ = ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
          ((D.R.m : ℝ) * L.sc.x ^ (-12 : ℝ) * ((∑ t0 ∈ goodReps X p, Nv X p t0 : ℕ) : ℝ)) := by
        simp only [Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t0 _ => ?_
        ring
    _ ≤ _ := by
        have h' : ((∑ t0 ∈ goodReps X p, Nv X p t0 : ℕ) : ℝ) ≤ (D.host.TT.card : ℝ) := by
          exact_mod_cast sum_Nv_le X p (goodReps X p)
        have hm : 0 ≤ (D.R.m : ℝ) * L.sc.x ^ (-12 : ℝ) := by positivity
        have hc2 : 0 ≤ ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) := by
          positivity
        calc _ ≤ ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
              ((D.R.m : ℝ) * L.sc.x ^ (-12 : ℝ) * (D.host.TT.card : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h' hm) hc2
          _ = _ := by ring

theorem mem_candF {K : Consts} {p : ℕ} : p ∈ candF D L K ↔ p < ⌈L.sc.X'⌉₊ ∧ Cand D L K p := by
  unfold candF
  simp only [Finset.mem_filter, Finset.mem_range]

theorem sum_cand_le (K : Consts) :
    ∑ p ∈ candF D L K, Real.log p / p ≤ L.sc.x ^ (L.sc.eps / 3) * (2 + L.sc.x ^ (L.sc.eps / 3)) := by
  have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have ht : 0 < L.sc.x ^ (L.sc.eps / 3) := by positivity
  set t := L.sc.x ^ (L.sc.eps / 3) with htdef
  have hX : L.sc.X' = Real.exp t := rfl
  set M := ⌈L.sc.X'⌉₊ with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by
    rw [hM]
    exact (Nat.ceil_pos.mpr (by rw [hX]; exact Real.exp_pos t)).ne')
  have hlt : ∀ n ∈ Finset.range M, (n : ℝ) < Real.exp t := fun n hn => by
    rw [← hX]
    exact Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  calc ∑ p ∈ candF D L K, Real.log p / p
      ≤ ∑ n ∈ Finset.range M, Real.log n / n := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Finset.mem_range.mpr (mem_candF.mp hn).1)
          (fun n _ _ => div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
    _ ≤ ∑ n ∈ Finset.range M, t * (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · simp [h0]
        · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hpos
          have hlog : Real.log n < t := (Real.log_lt_iff_lt_exp hn0).mpr (hlt n hn)
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hlog.le (by positivity)
    _ = t * (harmonic (M - 1) : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel, Finset.sum_range_succ']
        simp only [harmonic]
        push_cast
        simp
    _ ≤ t * (1 + Real.log (M - 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) ht.le
    _ ≤ t * (1 + t) := by
        refine mul_le_mul_of_nonneg_left ?_ ht.le
        have : Real.log ((M - 1 : ℕ) : ℝ) ≤ t := by
          rcases Nat.eq_zero_or_pos (M - 1) with h0 | hpos
          · rw [h0]
            simpa using ht.le
          · have h1 : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hpos
            exact ((Real.log_lt_iff_lt_exp h1).mpr (hlt (M - 1) (Finset.mem_range.mpr (by omega)))).le
        linarith
    _ ≤ t * (2 + t) := by nlinarith

theorem markov_ind (s : Scale) (S : ℝ) (hS : 0 ≤ S) [Decidable (s.x ^ (-s.eps) < S)] :
    (if s.x ^ (-s.eps) < S then (1 : ℝ) else 0) ≤ s.x ^ s.eps * S := by
  have hx : 0 < s.x := lt_trans zero_lt_one s.one_lt_alt
  split_ifs with h
  · have e : s.x ^ s.eps * s.x ^ (-s.eps) = 1 := by
      rw [← Real.rpow_add hx]
      simp
    have hp : 0 < s.x ^ s.eps := by positivity
    nlinarith
  · positivity

theorem ZZ_le (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (hS : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p) :
    ZZ X K a b ≤ ∑ p ∈ candF D L K, Real.log p / p * (L.sc.x ^ L.sc.eps + 1) * Sig X K a b p := by
  unfold ZZ
  refine Finset.sum_le_sum fun p hp => ?_
  have hc : Cand D L K p := (mem_candF.mp hp).2
  have h0 : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h0
  have := markov_ind L.sc (Sig X K a b p) (hS p hc)
  rw [add_mul, one_mul]
  linarith

theorem meanEx_of (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Cm : ℝ) (h8 : adm8 D L X K Cm)
    (N : NumMean D L K Cm) (hI : RestHypI X K) (hρ : rho D K L.sc ≤ rhoB D K L.sc) (h2 : Conclusion2 D L X K) : MeanEx X K := by
  have hS : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p :=
    fun a b p hc => Sig_nonneg X K hK Cm h8 N hI hρ a b p hc
  unfold MeanEx
  refine ⟨hS, ?_⟩
  have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have key : ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), ZZ X K a b ≤
      ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) * (L.sc.x ^ (-9 : ℝ) / 4) := by
    calc _ ≤ ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), ∑ p ∈ candF D L K,
            Real.log p / p * (L.sc.x ^ L.sc.eps + 1) * Sig X K a b p :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ZZ_le X K a b (hS a b)
      _ = ∑ p ∈ candF D L K, Real.log p / p * (L.sc.x ^ L.sc.eps + 1) *
            ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), Sig X K a b p := by
          simp only [Finset.mul_sum]
          exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
      _ ≤ ∑ p ∈ candF D L K, Real.log p / p * (L.sc.x ^ L.sc.eps + 1) *
            (((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
              ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ))) := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
            (sum_Sig_le X K Cm N h2 p (mem_candF.mp hp).2) ?_
          have := Real.log_natCast_nonneg p
          positivity
      _ = ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
            ((L.sc.x ^ L.sc.eps + 1) * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) *
            ∑ p ∈ candF D L K, Real.log p / p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ((box D (winA D L.sc)).card : ℝ) * ((box D (winB D K L.sc)).card : ℝ) *
            ((L.sc.x ^ L.sc.eps + 1) * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) *
            (L.sc.x ^ (L.sc.eps / 3) * (2 + L.sc.x ^ (L.sc.eps / 3))) := by
          refine mul_le_mul_of_nonneg_left (sum_cand_le K) ?_
          positivity
      _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left N.tot (by positivity)
  have hA := box_nonempty (D := D) _ (winA_nonempty K Cm N)
  have hB := box_nonempty (D := D) _ (winB_nonempty K Cm N)
  have key2 : ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), ZZ X K a b ≤
      ∑ a ∈ box D (winA D L.sc), ∑ b ∈ box D (winB D K L.sc), L.sc.x ^ (-9 : ℝ) / 4 := by
    refine key.trans (le_of_eq ?_)
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  obtain ⟨a, ha, hab⟩ := Finset.exists_le_of_sum_le hA key2
  obtain ⟨b, hb, hle⟩ := Finset.exists_le_of_sum_le hB hab
  exact ⟨a, ha, b, hb, hle⟩

theorem weight_condition_of_mean_excess (X : Inst D L) (K : Consts) (h : MeanEx X K) : WeightVectorExists D L X K := by
  obtain ⟨hS, a, ha, b, hb, hZ⟩ := h
  unfold WeightVectorExists
  refine ⟨a, ha, b, hb, ?_⟩
  unfold WReq
  unfold ZZ at hZ
  have hc : cands D L K = candF D L K := rfl
  rw [hc]
  have h4 : ∑ p ∈ candF D L K, Real.log p / p *
      (2 * (if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then (1 : ℝ) else 0) + 4 * Sig X K a b p) ≤
      4 * ∑ p ∈ candF D L K, Real.log p / p *
        ((if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then (1 : ℝ) else 0) + Sig X K a b p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have h0 : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    have hi : (0 : ℝ) ≤ if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then 1 else 0 := by
      split_ifs <;> norm_num
    nlinarith
  linarith

end Formalism.MainNotions.AuxBlock8.Pf

end
