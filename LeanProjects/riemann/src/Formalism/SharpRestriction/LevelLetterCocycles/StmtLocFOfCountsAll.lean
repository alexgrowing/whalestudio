import Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds

noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

theorem sum_pi_single {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (S0 : Finset α)
    (w : ι → α → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a ∈ S0, w i a ≤ 1) (v : ι) (P : α → Prop)
    [DecidablePred P] :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => S0), (if P (t v) then ∏ i, w i (t i) else 0) ≤
      ∑ a ∈ S0.filter P, w v a := by
  set h : ι → α → ℝ := fun i a => if i = v then (if P a then w i a else 0) else w i a with hh
  have hpt : ∀ t : ι → α, (if P (t v) then ∏ i, w i (t i) else 0) = ∏ i, h i (t i) := by
    intro t
    by_cases hp : P (t v)
    · rw [if_pos hp]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = v
      · subst hi; simp [hh, hp]
      · simp [hh, hi]
    · rw [if_neg hp]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hh, hp])
  rw [Finset.sum_congr rfl fun t _ => hpt t, ← Finset.prod_univ_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  have hv : ∑ a ∈ S0, h v a = ∑ a ∈ S0.filter P, w v a := by
    rw [Finset.sum_filter]; simp [hh]
  have hX : 0 ≤ ∑ a ∈ S0.filter P, w v a := Finset.sum_nonneg fun a _ => hw0 v a
  have hY : ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a ≤ 1 := by
    refine Finset.prod_le_one (fun i _ => Finset.sum_nonneg fun a _ => ?_) fun i hi => ?_
    · simp only [hh]; split_ifs <;> first | exact hw0 _ _ | exact le_rfl
    · have hne : i ≠ v := Finset.ne_of_mem_erase hi
      simp only [hh, if_neg hne]
      exact hw1 i
  rw [hv]
  calc (∑ a ∈ S0.filter P, w v a) * ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a
      ≤ (∑ a ∈ S0.filter P, w v a) * 1 := mul_le_mul_of_nonneg_left hY hX
    _ = ∑ a ∈ S0.filter P, w v a := mul_one _

theorem sum_pi_all {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (S0 : Finset α)
    (w : ι → α → ℝ) (Q : α → Prop) [DecidablePred Q] :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => S0), (if ∀ i, Q (t i) then ∏ i, w i (t i) else 0) =
      ∏ i, ∑ a ∈ S0.filter Q, w i a := by
  have hpt : ∀ t : ι → α, (if ∀ i, Q (t i) then ∏ i, w i (t i) else 0) =
      ∏ i, (if Q (t i) then w i (t i) else 0) := by
    intro t
    by_cases hq : ∀ i, Q (t i)
    · rw [if_pos hq]; exact Finset.prod_congr rfl fun i _ => by rw [if_pos (hq i)]
    · rw [if_neg hq]
      push Not at hq
      obtain ⟨i, hi⟩ := hq
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
  rw [Finset.sum_congr rfl fun t _ => hpt t]
  rw [← Finset.prod_univ_sum (fun _ => S0) (fun i a => if Q a then w i a else 0)]
  exact Finset.prod_congr rfl fun i _ => by rw [Finset.sum_filter]

variable (D : D7)

def IsLab (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0

def Eii (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  IsLab D k f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
    ∀ x ∈ Formalism.CyclotomicNorms.rootsBar f, ∀ y ∈ Formalism.CyclotomicNorms.rootsBar f,
      Formalism.CyclotomicNorms.primeToPart ℓ x = Formalism.CyclotomicNorms.primeToPart ℓ y → x = y)

def Eiii (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  IsLab D k f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ D.host.g k → ∀ x ∈ Formalism.CyclotomicNorms.rootsBar f,
    Formalism.CyclotomicNorms.primeToPart ℓ x ≠ Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))))

def Eiv (k : Fin 2) (a : ℕ) (f : (ZMod (D.host.g k))[X]) : Prop :=
  IsLab D k f ∧ Squarefree f ∧ ∃ q : (ZMod (D.host.g k))[X], q ∣ f ∧ q.natDegree = a

def Ev (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  IsLab D k f ∧ Squarefree f ∧ ¬ ∃ q : (ZMod (D.host.g k))[X], Irreducible q ∧ q ∣ f ∧ q.natDegree.Prime ∧
    D.R.r < 2 * q.natDegree ∧ q.natDegree + 3 ≤ D.R.r

def Counts : Prop :=
  TieAdmG D → 100 ≤ D.R.r → ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k →
    (∀ T : Finset (ZMod (D.host.g k))[X], (∀ f ∈ T, Eii D k f) →
      (T.card : ℝ) ≤ 23 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ)) *
        (D.host.g k : ℝ) ^ D.R.r) ∧
    (∀ (c : (ZMod (D.host.g k))ˣ) (T : Finset (ZMod (D.host.g k))[X]), (∀ f ∈ T, Eiii D k c f) →
      (T.card : ℝ) ≤ (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
        (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) * (D.host.g k : ℝ) ^ D.R.r) ∧
    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ D.R.r → ∀ T : Finset (ZMod (D.host.g k))[X], (∀ f ∈ T, Eiv D k a f) →
      (T.card : ℝ) ≤ 7 / 8 * (D.host.g k : ℝ) ^ D.R.r) ∧
    (∀ T : Finset (ZMod (D.host.g k))[X], (∀ f ∈ T, Ev D k f) →
      (T.card : ℝ) ≤ (1 - 1 / (5 * Real.log D.R.r)) * (D.host.g k : ℝ) ^ D.R.r)

variable {D}

theorem wt_le_count {eV : VecAt D} {CL : ℝ} (hCL : 0 ≤ CL) (hL : lawL D eV CL) (k : Fin 2) (v : D.nd.PlG k)
    (T : Finset (ZMod (D.host.g k))[X]) (hT : ∀ f ∈ T, IsLab D k f ∧ Squarefree f) (B : ℝ)
    (hB : (T.card : ℝ) ≤ B * (D.host.g k : ℝ) ^ D.R.r) :
    ∑ f ∈ T, wtOf D k (eV k v) f ≤ (1 + CL * D.R.r / D.host.g k) * B := by
  have hg : (0 : ℝ) < D.host.g k := by exact_mod_cast (D.host.g_prime k).pos
  have hgr : (0 : ℝ) < (D.host.g k : ℝ) ^ D.R.r := pow_pos hg _
  set U : ℝ := (1 + CL * D.R.r / D.host.g k) / (D.host.g k : ℝ) ^ D.R.r with hU
  have hU0 : 0 ≤ U := by positivity
  have h1 : ∀ f ∈ T, wtOf D k (eV k v) f ≤ U := fun f hf =>
    ((hL k v).2.1 f (hT f hf).1 (hT f hf).2).2
  calc ∑ f ∈ T, wtOf D k (eV k v) f ≤ T.card • U := Finset.sum_le_card_nsmul _ _ _ h1
    _ = (T.card : ℝ) * U := nsmul_eq_mul _ _
    _ ≤ (B * (D.host.g k : ℝ) ^ D.R.r) * U := mul_le_mul_of_nonneg_right hB hU0
    _ = (1 + CL * D.R.r / D.host.g k) * B := by rw [hU]; field_simp

theorem bad_cases (k : Fin 2) (t : Tup D k) (hlab : ∀ v, IsLab D k (t v)) (hbad : ¬ goodAt D k t) :
    (∃ v, ¬ Squarefree (t v)) ∨ (∃ v, Eii D k (t v)) ∨
      (∃ v j, Eiii D k (D.nd.chiT k v j) (t v) ∨ Eiii D k (D.nd.chiT k v j)⁻¹ (t v)) ∨
      (∃ a ∈ Finset.Icc 1 (D.R.r / 2), ∀ v, Eiv D k a (t v)) ∨ (∀ v, Ev D k (t v)) := by
  by_contra hno
  push Not at hno
  obtain ⟨hsq, hii, hiii, hiv, hv⟩ := hno
  apply hbad
  unfold goodAt
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have key : ∀ χ : D.nd.PlG k → Fin D.R.m → (ZMod (D.host.g k))ˣ, (∀ v j, ¬ Eiii D k (χ v j) (t v)) →
      Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t χ := by
    intro χ hχ
    refine ⟨hlab, hsq, ?_, ?_, ?_, ?_⟩
    · intro ℓ hℓ hbb v
      have h := hii v
      unfold Eii at h
      push Not at h
      exact h (hlab v) (hsq v) ℓ hℓ hbb
    · intro ℓ hℓ hne v j
      have h := hχ v j
      unfold Eiii at h
      push Not at h
      exact h (hlab v) (hsq v) ℓ hℓ hne
    · intro a ha1 ha2
      obtain ⟨v, hv'⟩ := hiv a (Finset.mem_Icc.2 ⟨ha1, by omega⟩)
      exact ⟨v, fun hq => hv' ⟨hlab v, hsq v, hq⟩⟩
    · obtain ⟨v, hv'⟩ := hv
      by_contra hn
      apply hv'
      refine ⟨hlab v, hsq v, ?_⟩
      rintro ⟨q, hq⟩
      exact hn ⟨v, q, hq⟩
  exact ⟨key _ fun v j => (hiii v j).1, key _ fun v j => (hiii v j).2⟩

theorem le_five {x a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (h : x ≤ a ∨ x ≤ b ∨ x ≤ c ∨ x ≤ d ∨ x ≤ e) : x ≤ a + b + c + d + e := by
  rcases h with h | h | h | h | h <;> linarith

set_option maxHeartbeats 4000000 in

theorem propW_of_counts (hC : Counts D) : PropW D := by
  classical
  intro eV CL hCL hL hA hr k hg S hS
  obtain ⟨Cii, Ciii, Civ, Cv⟩ := hC hA hr k hg
  obtain ⟨S0, hmem, hsum⟩ := D.ntypes.eSer_sum k
  have hw0 : ∀ v f, 0 ≤ wtOf D k (eV k v) f := fun v f => (hL k v).1 f
  have hw1 : ∀ v, ∑ f ∈ S0, wtOf D k (eV k v) f ≤ 1 := fun v => sum_wtOf_le_one k (eV k v) S0 hsum
  have hF0 : ∀ t : Tup D k, 0 ≤ ∏ v, wtOf D k (eV k v) (t v) :=
    fun t => Finset.prod_nonneg fun v _ => hw0 v (t v)
  have hite : ∀ (p : Prop) [Decidable p] (t : Tup D k), 0 ≤ (if p then ∏ v, wtOf D k (eV k v) (t v) else 0) := by
    intro p _ t; split_ifs
    · exact hF0 t
    · exact le_rfl
  have hg0 : (0 : ℝ) < D.host.g k := by exact_mod_cast (D.host.g_prime k).pos

  have P1 : ∀ v, ∑ f ∈ S0.filter (fun f => ¬ Squarefree f), wtOf D k (eV k v) f ≤ 3 / (D.host.g k : ℝ) :=
    fun v => (hL k v).2.2 _ fun f hf => (Finset.mem_filter.1 hf).2
  have P2 : ∀ v, ∑ f ∈ S0.filter (Eii D k), wtOf D k (eV k v) f ≤
      (1 + CL * D.R.r / D.host.g k) * (23 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ))) :=
    fun v => wt_le_count hCL hL k v _ (fun f hf => by
        obtain ⟨h1, h2, -⟩ := (Finset.mem_filter.1 hf).2; exact ⟨h1, h2⟩) _
      (Cii _ fun f hf => (Finset.mem_filter.1 hf).2)
  have P3 : ∀ v (c : (ZMod (D.host.g k))ˣ), ∑ f ∈ S0.filter (Eiii D k c), wtOf D k (eV k v) f ≤
      (1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
        (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) :=
    fun v c => wt_le_count hCL hL k v _ (fun f hf => by
        obtain ⟨h1, h2, -⟩ := (Finset.mem_filter.1 hf).2; exact ⟨h1, h2⟩) _
      (Ciii c _ fun f hf => (Finset.mem_filter.1 hf).2)
  have P4 : ∀ v, ∀ a ∈ Finset.Icc 1 (D.R.r / 2), ∑ f ∈ S0.filter (Eiv D k a), wtOf D k (eV k v) f ≤
      (1 + CL * D.R.r / D.host.g k) * (7 / 8) := by
    intro v a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.1 ha
    exact wt_le_count hCL hL k v _ (fun f hf => by
        obtain ⟨h1, h2, -⟩ := (Finset.mem_filter.1 hf).2; exact ⟨h1, h2⟩) _
      (Civ a ha1 (by omega) _ fun f hf => (Finset.mem_filter.1 hf).2)
  have P5 : ∀ v, ∑ f ∈ S0.filter (Ev D k), wtOf D k (eV k v) f ≤
      (1 + CL * D.R.r / D.host.g k) * (1 - 1 / (5 * Real.log D.R.r)) :=
    fun v => wt_le_count hCL hL k v _ (fun f hf => by
        obtain ⟨h1, h2, -⟩ := (Finset.mem_filter.1 hf).2; exact ⟨h1, h2⟩) _
      (Cv _ fun f hf => (Finset.mem_filter.1 hf).2)

  have cover : ∀ t : Tup D k, (∀ v, t v ∈ S0) → ¬ goodAt D k t →
      ∏ v, wtOf D k (eV k v) (t v) ≤
        ∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) +
        ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) +
        ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) +
          (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) +
        ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) +
        (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) := by
    intro t ht hbad
    have hlab : ∀ v, IsLab D k (t v) := fun v => (hmem (t v)).1 (ht v)
    have pick : ∀ (p : Prop) [Decidable p], p →
        ∏ v, wtOf D k (eV k v) (t v) ≤ (if p then ∏ v, wtOf D k (eV k v) (t v) else 0) :=
      fun p _ hp => by rw [if_pos hp]
    apply le_five (Finset.sum_nonneg fun v _ => hite _ t) (Finset.sum_nonneg fun v _ => hite _ t)
      (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun j _ => add_nonneg (hite _ t) (hite _ t))
      (Finset.sum_nonneg fun a _ => hite _ t) (hite _ t)
    rcases bad_cases k t hlab hbad with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, j, hv | hv⟩ | ⟨a, ha, hv⟩ | hv
    · left
      refine le_trans (pick (¬ Squarefree (t v)) hv) ?_
      exact Finset.single_le_sum (f := fun v => if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)
        (fun v _ => hite _ t) (Finset.mem_univ v)
    · right; left
      refine le_trans (pick (Eii D k (t v)) hv) ?_
      exact Finset.single_le_sum (f := fun v => if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)
        (fun v _ => hite _ t) (Finset.mem_univ v)
    · right; right; left
      refine le_trans (pick (Eiii D k (D.nd.chiT k v j) (t v)) hv) ?_
      refine le_trans (le_add_of_nonneg_right (hite (Eiii D k (D.nd.chiT k v j)⁻¹ (t v)) t)) ?_
      refine le_trans (Finset.single_le_sum (f := fun j => (if Eiii D k (D.nd.chiT k v j) (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0)) (fun j _ => add_nonneg (hite _ t) (hite _ t))
          (Finset.mem_univ j)) ?_
      exact Finset.single_le_sum (f := fun v => ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0)))
        (fun v _ => Finset.sum_nonneg fun j _ => add_nonneg (hite _ t) (hite _ t)) (Finset.mem_univ v)
    · right; right; left
      refine le_trans (pick (Eiii D k (D.nd.chiT k v j)⁻¹ (t v)) hv) ?_
      refine le_trans (le_add_of_nonneg_left (hite (Eiii D k (D.nd.chiT k v j) (t v)) t)) ?_
      refine le_trans (Finset.single_le_sum (f := fun j => (if Eiii D k (D.nd.chiT k v j) (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0)) (fun j _ => add_nonneg (hite _ t) (hite _ t))
          (Finset.mem_univ j)) ?_
      exact Finset.single_le_sum (f := fun v => ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then
          ∏ v, wtOf D k (eV k v) (t v) else 0)))
        (fun v _ => Finset.sum_nonneg fun j _ => add_nonneg (hite _ t) (hite _ t)) (Finset.mem_univ v)
    · right; right; right; left
      refine le_trans (pick (∀ v, Eiv D k a (t v)) hv) ?_
      exact Finset.single_le_sum (f := fun a => if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)
        (fun a _ => hite _ t) ha
    · right; right; right; right
      exact pick (∀ v, Ev D k (t v)) hv
  have h1 : locShare D eV k S = ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ S0), ∏ v, wtOf D k (eV k v) (t v) := by
    unfold locShare
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rfl
    · push Not at ht
      obtain ⟨v, hv⟩ := ht
      exact Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_off k _ _ fun h => hv ((hmem (t v)).2 h))
  have h2 : S.filter (fun t => ∀ v, t v ∈ S0) ⊆ Fintype.piFinset (fun _ : D.nd.PlG k => S0) := by
    intro t ht; rw [Fintype.mem_piFinset]; exact (Finset.mem_filter.1 ht).2
  have hR0 : ∀ t : Tup D k, 0 ≤ ∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) + ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) := by
    intro t
    have := Finset.sum_nonneg (s := Finset.univ) fun v (_ : v ∈ Finset.univ) => hite (¬ Squarefree (t v)) t
    have := Finset.sum_nonneg (s := Finset.univ) fun v (_ : v ∈ Finset.univ) => hite (Eii D k (t v)) t
    have := Finset.sum_nonneg (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
      Finset.sum_nonneg (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
        add_nonneg (hite (Eiii D k (D.nd.chiT k v j) (t v)) t) (hite (Eiii D k (D.nd.chiT k v j)⁻¹ (t v)) t)
    have := Finset.sum_nonneg (s := Finset.Icc 1 (D.R.r / 2)) fun a (_ : a ∈ Finset.Icc 1 (D.R.r / 2)) =>
      hite (∀ v, Eiv D k a (t v)) t
    have := hite (∀ v, Ev D k (t v)) t
    linarith
  have b1 : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) ≤ (D.R.f : ℝ) * (3 / (D.host.g k : ℝ)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ v : D.nd.PlG k, ∑ f ∈ S0.filter (fun f => ¬ Squarefree f), wtOf D k (eV k v) f :=
          Finset.sum_le_sum fun v _ => sum_pi_single S0 (fun v f => wtOf D k (eV k v) f) hw0 hw1 v (fun f => ¬ Squarefree f)
      _ ≤ ∑ v : D.nd.PlG k, 3 / (D.host.g k : ℝ) := Finset.sum_le_sum fun v _ => P1 v
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.nd.card_PlG k, nsmul_eq_mul]
  have b2 : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) ≤ (D.R.f : ℝ) * ((1 + CL * D.R.r / D.host.g k) * (23 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ v : D.nd.PlG k, ∑ f ∈ S0.filter (Eii D k), wtOf D k (eV k v) f :=
          Finset.sum_le_sum fun v _ => sum_pi_single S0 (fun v f => wtOf D k (eV k v) f) hw0 hw1 v (Eii D k)
      _ ≤ ∑ v : D.nd.PlG k, (1 + CL * D.R.r / D.host.g k) * (23 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ))) := Finset.sum_le_sum fun v _ => P2 v
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.nd.card_PlG k, nsmul_eq_mul]
  have b3 : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) * ((1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) + (1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)))) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ v : D.nd.PlG k, ∑ j : Fin D.R.m, ((1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) + (1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1))) := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_add_distrib]
          exact add_le_add
            ((sum_pi_single S0 (fun v f => wtOf D k (eV k v) f) hw0 hw1 v (Eiii D k (D.nd.chiT k v j))).trans (P3 v _))
            ((sum_pi_single S0 (fun v f => wtOf D k (eV k v) f) hw0 hw1 v (Eiii D k (D.nd.chiT k v j)⁻¹)).trans (P3 v _))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, D.nd.card_PlG k, nsmul_eq_mul, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hu0 : 0 ≤ (1 + CL * D.R.r / D.host.g k) := by positivity
  have b4 : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) ≤ (((D.R.r / 2 : ℕ) : ℝ)) * ((1 + CL * D.R.r / D.host.g k) * (7 / 8)) ^ D.R.f := by
    rw [Finset.sum_comm]
    calc _ = ∑ a ∈ Finset.Icc 1 (D.R.r / 2), ∏ v : D.nd.PlG k, ∑ f ∈ S0.filter (Eiv D k a), wtOf D k (eV k v) f :=
          Finset.sum_congr rfl fun a _ => sum_pi_all S0 (fun v f => wtOf D k (eV k v) f) (Eiv D k a)
      _ ≤ ∑ a ∈ Finset.Icc 1 (D.R.r / 2), ∏ v : D.nd.PlG k, ((1 + CL * D.R.r / D.host.g k) * (7 / 8)) :=
          Finset.sum_le_sum fun a ha => Finset.prod_le_prod
            (fun v _ => Finset.sum_nonneg fun f _ => hw0 v f) fun v _ => P4 v a ha
      _ = _ := by
          rw [Finset.sum_const, Nat.card_Icc, Finset.prod_const, Finset.card_univ, D.nd.card_PlG k, nsmul_eq_mul]
          norm_num
  have b5 : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) ≤ ((1 + CL * D.R.r / D.host.g k) * (1 - 1 / (5 * Real.log D.R.r))) ^ D.R.f := by
    calc _ = ∏ v : D.nd.PlG k, ∑ f ∈ S0.filter (Ev D k), wtOf D k (eV k v) f := sum_pi_all S0 (fun v f => wtOf D k (eV k v) f) (Ev D k)
      _ ≤ ∏ v : D.nd.PlG k, ((1 + CL * D.R.r / D.host.g k) * (1 - 1 / (5 * Real.log D.R.r))) :=
          Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun f _ => hw0 v f) fun v _ => P5 v
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  have hsplit : ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), (∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) + ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) =
      ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) + ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) := by
    simp only [Finset.sum_add_distrib]
  have hcard : (((D.R.r / 2 : ℕ) : ℝ)) ≤ (D.R.r : ℝ) / 2 := Nat.cast_div_le
  have hp4 : 0 ≤ ((1 + CL * D.R.r / D.host.g k) * (7 / 8)) ^ D.R.f := by positivity
  have b4' : (((D.R.r / 2 : ℕ) : ℝ)) * ((1 + CL * D.R.r / D.host.g k) * (7 / 8)) ^ D.R.f ≤ (D.R.r : ℝ) / 2 * (7 / 8 * (1 + CL * D.R.r / D.host.g k)) ^ D.R.f := by
    rw [mul_comm (1 + CL * D.R.r / D.host.g k) (7 / 8)]
    exact mul_le_mul_of_nonneg_right hcard (by rw [mul_comm]; exact hp4)
  have hWk : Wk D CL k = (D.R.f : ℝ) * (3 / (D.host.g k : ℝ)) + (D.R.f : ℝ) * ((1 + CL * D.R.r / D.host.g k) * (23 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ)))) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * ((1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) + (1 + CL * D.R.r / D.host.g k) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)))) + (D.R.r : ℝ) / 2 * (7 / 8 * (1 + CL * D.R.r / D.host.g k)) ^ D.R.f +
      ((1 + CL * D.R.r / D.host.g k) * (1 - 1 / (5 * Real.log D.R.r))) ^ D.R.f := by
    unfold Wk; ring
  calc locShare D eV k S = ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ S0), ∏ v, wtOf D k (eV k v) (t v) := h1
    _ ≤ ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ S0), (∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) + ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) :=
        Finset.sum_le_sum fun t ht => cover t (Finset.mem_filter.1 ht).2 (hS t (Finset.mem_filter.1 ht).1)
    _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => S0), (∑ v, (if ¬ Squarefree (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, (if Eii D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + ∑ v, ∑ j, ((if Eiii D k (D.nd.chiT k v j) (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if Eiii D k (D.nd.chiT k v j)⁻¹ (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) + ∑ a ∈ Finset.Icc 1 (D.R.r / 2), (if ∀ v, Eiv D k a (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0) + (if ∀ v, Ev D k (t v) then ∏ v, wtOf D k (eV k v) (t v) else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg h2 fun t _ _ => hR0 t
    _ ≤ Wk D CL k := by rw [hsplit, hWk]; linarith

end Formalism.MainNotions.N.LocalShareBounds
