import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFundNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 ((unif_lt hx x).2 le_rfl)).2 (ha hij)

private theorem exists_cut (a : Fin n → ℤ) (ha : Antitone a) (c : ℤ) :
    ∃ m ≤ n, ∀ i : Fin n, (i : ℕ) < m ↔ c < a i := by
  classical
  have hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c := ⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj, hc⟩ := this
    exact hc.trans_le (ha (Fin.le_def.2 hj))
  · by_contra h
    exact absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)

private theorem const_central (y : kˣ) : diagT k (Fin n) (fun _ => y) ∈ Subgroup.center (GL (Fin n) k) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]

private theorem rot_norm (C : Subgroup 𝓀[k]ˣ) {x : kˣ} (hx : IsUnif x) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) :
    pm k n w * pw x a ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ?_
  have e : (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹)⁻¹ =
      pm k n w * pw x a * g⁻¹ * (pm k n w * pw x a)⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]

private theorem invLen_inv (w : Equiv.Perm (Fin n)) : invLen w⁻¹ = invLen w := by
  unfold invLen
  refine Finset.card_bij' (fun p _ => (w⁻¹ p.2, w⁻¹ p.1)) (fun p _ => (w p.2, w p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [and_comm] using hp
  · intro p hp
    simpa [and_comm] using hp
  · intro p _
    simp
  · intro p _
    simp

private theorem invLen_eq (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) :
    invLen w = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat := by
  rw [invLen, ← Finset.filter_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h := hw p.1 p.2
  rw [if_neg (lt_asymm (Finset.mem_filter.1 hp).2), add_zero] at h
  rw [← h]
  split_ifs <;> rfl

private theorem hk_triv {G : Type} [Group G] (I : Subgroup G) (hI : HeckePair I) (x : G) :
    hk (Representation.trivial ℤ G ℤ) I x = ((MulAction.orbit I (x : G ⧸ I)).ncard : Module.End ℤ _) := by
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := hI x
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  ext v
  rw [hk, (hkApply ℤ G _ (Representation.trivial ℤ G ℤ) I I x (hI x)).1 v, dc, finsum_eq_sum_of_fintype,
    LinearMap.sum_apply, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simp

private theorem endCast_inj {G : Type} [Group G] (I : Subgroup G) {a b : ℕ}
    (h : (a : Module.End ℤ (fixd (Representation.trivial ℤ G ℤ) I)) = b) : a = b := by
  have := congrArg Subtype.val (LinearMap.congr_fun h ⟨1, fun _ _ => rfl⟩)
  simpa using this

private theorem hk_norm {G : Type} [Group G] (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) : hk (Representation.trivial ℤ G ℤ) I u = 1 := by
  ext v
  rw [(hkNorm ℤ G ℤ _ I u hI hu).1 v]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.domCard :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ a : Fin n → ℤ, Antitone a → (MulAction.orbit (iwC k n C) ((pw x a : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat) := by
  intro k _ _ _ _ n C x hx a ha
  have hH := (heckePairIwC k n C).1
  have hmul := (domMul k n C ℤ ℤ (Representation.trivial ℤ (GL (Fin n) k) ℤ)).1
  refine endCast_inj (iwC k n C) ?_
  rw [← hk_triv _ hH]
  have hfund : ∀ m ≤ n, hk (Representation.trivial ℤ (GL (Fin n) k) ℤ) (iwC k n C) (pw x (fund n m)) =
      ((resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (fund n m p.1 - fund n m p.2).toNat) : ℕ) : Module.End ℤ _) := by
    intro m hm
    obtain ⟨w, hw⟩ := exists_rot n m hm
    have hn := rot_norm C hx _ w hw
    have e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m)) := by
      rw [map_inv, inv_mul_cancel_left]
    rw [e, ((hkNorm ℤ _ ℤ _ _ _ hH hn).2.2.2 _).2, hk_norm _ hH _ hn, mul_one, hk_triv _ hH, permCard,
      invLen_inv, invLen_eq _ w hw]
  have key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) →
      hk (Representation.trivial ℤ (GL (Fin n) k) ℤ) (iwC k n C) (pw x a) =
      ((resCard k ^ (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        (a p.1 - a p.2).toNat) : ℕ) : Module.End ℤ _) := by
    intro c N
    induction N with
    | zero =>
      intro a _ hb
      have e : a = fun _ : Fin n => c := by
        funext i
        have := hb i
        omega
      rw [e, pw, hk_norm _ hH _ (Subgroup.center_le_normalizer _ (const_central _))]
      simp
    | succ N ih =>
      intro a ha hb
      obtain ⟨m, hm, hc⟩ := exists_cut a ha c
      have hfa : Antitone (fund n m) := by
        intro i j hij
        have := Fin.le_def.1 hij
        simp only [fund]
        split_ifs <;> omega
      have ha' : Antitone (a - fund n m) := by
        intro i j hij
        have h1 := ha hij
        have h2 := hc i
        have h3 := hc j
        have h4 := hb i
        have h5 := hb j
        simp only [fund, Pi.sub_apply]
        split_ifs <;> omega
      have hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N := by
        intro i
        have h2 := hc i
        have h4 := hb i
        simp only [fund, Pi.sub_apply]
        split_ifs <;> omega
      have e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i := by
        funext i
        simp only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]
      have h1 := ih _ ha' hb'
      have h2 := hfund m hm
      rw [pw] at h1 h2 ⊢
      rw [e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa), h1, h2, ← Nat.cast_mul, ← pow_add,
        ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_filter.1 hp).2.le
      have h3 := ha' hp'
      have h4 := hfa hp'
      simp only [Pi.sub_apply] at h3 ⊢
      omega
  obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
  obtain ⟨d, hd⟩ := (Set.finite_range a).bddAbove
  exact key c (d - c).toNat a ha fun i => by
    have h1 : c ≤ a i := hc ⟨i, rfl⟩
    have h2 : a i ≤ d := hd ⟨i, rfl⟩
    omega
