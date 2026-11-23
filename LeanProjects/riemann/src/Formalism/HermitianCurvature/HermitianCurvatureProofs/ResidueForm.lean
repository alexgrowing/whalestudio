import Formalism.HermitianCurvature.StatementFr

namespace Formalism.FourierDecayAlt.P.Fr11

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

def dg (g : Ix S → ℂ) : SlopeTestRemainingChoices S A := Matrix.diagonal fun e => algebraMap ℂ A (g e)

lemma dg_mul (g h : Ix S → ℂ) : (dg g * dg h : SlopeTestRemainingChoices S A) = dg (fun e => g e * h e) := by
  unfold dg
  rw [Matrix.diagonal_mul_diagonal]
  simp only [map_mul]

lemma dg_add (g h : Ix S → ℂ) : (dg g + dg h : SlopeTestRemainingChoices S A) = dg (fun e => g e + h e) := by
  unfold dg
  rw [Matrix.diagonal_add]
  simp only [map_add]

lemma dg_smul (c : ℂ) (g : Ix S → ℂ) : (c • dg g : SlopeTestRemainingChoices S A) = dg (fun e => c * g e) := by
  apply Matrix.ext
  intro i j
  simp only [dg, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [Algebra.smul_def]

lemma dg_one : (dg (fun _ => 1) : SlopeTestRemainingChoices S A) = 1 := by
  simp [dg]

lemma eU_same (a : S) (i : Fin 2) : (eU a i i : SlopeTestRemainingChoices S A) = dg (fun e => if e a = i then 1 else 0) := by
  apply Matrix.ext
  intro x y
  simp only [eU, dg, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x a = i <;> simp [hx]
  · have hn : ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro ⟨h1, h2, h3⟩
      apply hxy
      funext b
      by_cases hb : b = a
      · subst hb
        rw [h1, h2]
      · exact h3 b hb
    rw [if_neg hn, if_neg hxy]

lemma dg_io (g : Ix S → ℂ) (x : A) : (dg g * io x : SlopeTestRemainingChoices S A) = io x * dg g := by
  apply Matrix.ext
  intro x y
  simp only [dg, io, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp [Algebra.commutes]

lemma dg_eU (g : Ix S → ℂ) (b : S) (i j : Fin 2)
    (h : ∀ x y : Ix S, (∀ c, c ≠ b → x c = y c) → g x = g y) :
    (dg g * eU b i j : SlopeTestRemainingChoices S A) = eU b i j * dg g := by
  apply Matrix.ext
  intro x y
  simp only [dg, eU, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with hc
  · rw [h x y hc.2.2]
    simp
  · simp

def Ph {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ) (U V : B) : B :=
  p0 * (U - c • (U - V)) + p1 * (U + c • (U - V))

section PhLemmas

variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)

lemma Ph_add (U V U' V' : B) : Ph p0 p1 c (U + U') (V + V') = Ph p0 p1 c U V + Ph p0 p1 c U' V' := by
  unfold Ph
  rw [add_sub_add_comm, smul_add]
  simp only [mul_add, mul_sub]
  abel

lemma Ph_sub (U V U' V' : B) : Ph p0 p1 c (U - U') (V - V') = Ph p0 p1 c U V - Ph p0 p1 c U' V' := by
  unfold Ph
  rw [sub_sub_sub_comm, smul_sub]
  simp only [mul_add, mul_sub]
  abel

lemma Ph_zero : Ph p0 p1 c (0 : B) 0 = 0 := by
  simp [Ph]

lemma Ph_sum {J : Type} (s : Finset J) (U V : J → B) :
    Ph p0 p1 c (∑ j ∈ s, U j) (∑ j ∈ s, V j) = ∑ j ∈ s, Ph p0 p1 c (U j) (V j) := by
  induction s using Finset.cons_induction with
  | empty => simp [Ph_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, Ph_add, ih]

lemma Ph_const (h : p0 + p1 = 1) (K : B) : Ph p0 p1 c K K = K := by
  simp only [Ph, sub_self, smul_zero, sub_zero, add_zero, ← add_mul, h, one_mul]

lemma Ph_res (T : B) (γ Ya Y : ℂ) (h1 : Y ≠ γ) (h2 : Ya ≠ γ) (h3 : Y ≠ Ya) :
    Ph p0 p1 (Y - Ya)⁻¹ ((Y - γ)⁻¹ • T) ((Ya - γ)⁻¹ • T) =
      (Y - γ)⁻¹ • (((1 + 1 / (Ya - γ)) • p0 + (1 - 1 / (Ya - γ)) • p1) * T) := by
  have h1' : Y - γ ≠ 0 := sub_ne_zero.mpr h1
  have h2' : Ya - γ ≠ 0 := sub_ne_zero.mpr h2
  have h3' : Y - Ya ≠ 0 := sub_ne_zero.mpr h3
  have key : (Y - Ya)⁻¹ • ((Y - γ)⁻¹ • T - (Ya - γ)⁻¹ • T) = (-((Y - γ)⁻¹ * (Ya - γ)⁻¹)) • T := by
    rw [← sub_smul, smul_smul]
    congr 1
    field_simp
    ring
  unfold Ph
  rw [key, ← sub_smul, ← add_smul, mul_smul_comm, mul_smul_comm, add_mul, smul_mul_assoc,
    smul_mul_assoc, smul_add, smul_smul, smul_smul]
  congr 2 <;> ring

end PhLemmas

lemma mult_eq (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult v γ : SlopeTestRemainingChoices S A) = dg fun e => (v.map fun l => 1 + sg (e l.intersection_update_fsHerm_neg_one) / (l.pt - γ)).prod := rfl

lemma mult_nil (γ : ℂ) : (mult ([] : List (Letter ℂ S)) γ : SlopeTestRemainingChoices S A) = 1 := by
  simp only [mult_eq, List.map_nil, List.prod_nil]
  exact dg_one

lemma mult_cons (l : Letter ℂ S) (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult (l :: v) γ : SlopeTestRemainingChoices S A) = mult [l] γ * mult v γ := by
  simp only [mult_eq, dg_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

lemma mult_single (l : Letter ℂ S) (γ : ℂ) :
    (mult [l] γ : SlopeTestRemainingChoices S A) =
      (1 + 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 0 0 + (1 - 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 1 1 := by
  rw [mult_eq, eU_same, eU_same, dg_smul, dg_smul, dg_add]
  congr 1
  funext e
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  generalize e l.intersection_update_fsHerm_neg_one = k
  fin_cases k <;> simp [sg] <;> ring

lemma eU_sum (a : S) : (eU a 0 0 + eU a 1 1 : SlopeTestRemainingChoices S A) = 1 := by
  rw [eU_same, eU_same, dg_add, ← dg_one]
  congr 1
  funext e
  generalize e a = k
  fin_cases k <;> simp

lemma mult_single_eU (l : Letter ℂ S) (γ : ℂ) (b : S) (hb : l.intersection_update_fsHerm_neg_one ≠ b) (i j : Fin 2) :
    (mult [l] γ * eU b i j : SlopeTestRemainingChoices S A) = eU b i j * mult [l] γ := by
  rw [mult_eq]
  refine dg_eU _ b i j ?_
  intro x y hxy
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hxy l.intersection_update_fsHerm_neg_one hb]

lemma Kw_cons {r : ℕ} (L : LevelData A r) (l : Letter ℂ S) (w : List (Letter ℂ S)) :
    (Kw L (l :: w) : SlopeTestRemainingChoices S A) = Kw L w + eU l.intersection_update_fsHerm_neg_one 0 0 * tz L := by
  have hc : (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) * tz L = tz L * eU l.intersection_update_fsHerm_neg_one 0 0 := by
    rw [eU_same, tz]
    exact dg_io _ _
  simp only [Kw]
  rw [hc, ← mul_add]
  congr 1
  rw [eU_same]
  unfold dg
  rw [Matrix.diagonal_add]
  congr 1
  funext e
  by_cases h : e l.intersection_update_fsHerm_neg_one = 0 <;> simp [List.filter_cons, h]

lemma letterSum_step (l : Letter ℂ S) (Y : ℂ) (hY : Y ≠ l.pt) :
    ∀ (w v : List (Letter ℂ S)), (∀ l' ∈ w, l.intersection_update_fsHerm_neg_one ≠ l'.intersection_update_fsHerm_neg_one ∧ Y ≠ l'.pt ∧ l.pt ≠ l'.pt) →
      Ph (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹ (letterSum v w Y) (letterSum v w l.pt) =
        letterSum (l :: v) w Y
  | [], v, _ => by simp [letterSum, Ph_zero]
  | l' :: w, v, h => by
    obtain ⟨h1, h2, h3⟩ := h l' (by simp)
    have ih := letterSum_step l Y hY w (v ++ [l']) (fun l'' hl => h l'' (by simp [hl]))
    simp only [letterSum]
    rw [Ph_add, ih, Ph_res _ _ _ _ _ _ h2 h3 hY, ← mult_single, ← mul_assoc, mult_single_eU _ _ _ h1,
      mul_assoc, ← mult_cons, List.cons_append]

section Points

variable {r : ℕ} (L : LevelData A r) (st : Start A)

lemma ofWord_cons_plus (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : l.plus = true) :
    ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by
  simp [ofWord, h]

lemma mem_inv_of (P : ℂ) (hP : P ∈ st.inv) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → (∀ l ∈ w, P - l.pt ≠ 0 ∧ P - l.pt ≠ 1) →
      P ∈ (ofWord L st w).inv
  | [], _, _ => hP
  | l :: w, hp, h => by
    rw [ofWord_cons_plus L st l w (hp l (by simp))]
    exact ⟨mem_inv_of P hP w (fun l' hl => hp l' (by simp [hl])) (fun l' hl => h l' (by simp [hl])),
      h l (by simp)⟩

lemma ne_of_mem_inv (Y : ℂ) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → Y ∈ (ofWord L st w).inv → ∀ l ∈ w, Y ≠ l.pt
  | [], _, _ => by simp
  | l :: w, hp, h => by
    rw [ofWord_cons_plus L st l w (hp l (by simp))] at h
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact sub_ne_zero.1 h.2.1
    · exact ne_of_mem_inv Y w (fun l'' hl => hp l'' (by simp [hl])) h.1 l' hl'

lemma Adm_tail (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : admitted st (l :: w)) : admitted st w := by
  unfold admitted at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
    fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.mp h4).2⟩
  rw [List.map_cons, List.nodup_cons] at h1
  exact h1.2

end Points

lemma ins_upper (a : S) (p q s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; 0, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 1 * s := by
  simp [ins, Fin.sum_univ_two]

lemma io_smul (c : ℂ) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  apply Matrix.ext
  intro i j
  simp [io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply]

lemma io_sum {J : Type} (s : Finset J) (x : J → A) : (io (∑ j ∈ s, x j) : SlopeTestRemainingChoices S A) = ∑ j ∈ s, io (x j) := by
  simp only [io, map_sum]

lemma Kw_nil {r : ℕ} (L : LevelData A r) : (Kw L ([] : List (Letter ℂ S)) : SlopeTestRemainingChoices S A) = 0 := by
  simp [Kw]

end

end Formalism.FourierDecayAlt.P.Fr11

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.Fr11

theorem fr_residue_form : Formalism.FourierDecayAlt.Fr.ResidueForm := by
  intro hFA hEC A S _ _ _ _ _ _ r L st J _ Z γ w hL hst
  induction w with
  | nil =>
    intro _ _ hee _ Y _ _ _
    have e1 : (ofWord L st ([] : List (Letter ℂ S))).ee Y = io (st.ee Y) := rfl
    rw [e1, hee Y, Kw_nil, Finset.mul_sum, io_sum]
    simp only [letterSum, mult_nil, mul_one, zero_add, sub_zero, mul_smul_comm, io_smul]
  | cons l w ih =>
    intro hA hp hee hγ Y hY hY1 hYγ
    have hAw := Adm_tail st l w hA
    have hpw : ∀ l' ∈ w, l'.plus = true := fun l' hl => hp l' (by simp [hl])
    have hγw : ∀ l' ∈ w, ∀ j, l'.pt ≠ γ j := fun l' hl => hγ l' (by simp [hl])
    have ih' := ih hAw hpw hee hγw
    have hc := ofWord_cons_plus L st l w (hp l (by simp))
    rw [hc] at hY hY1 ⊢
    obtain ⟨hs, _, hi, hpw2⟩ := hA
    have hpair := (List.pairwise_cons.1 hpw2).1
    have hli := hi l (by simp)

    have hYa : l.pt ∈ (ofWord L st w).inv := by
      refine mem_inv_of L st _ hli.1 w hpw fun l' hl => ⟨?_, ?_⟩
      · simpa using hpair l' hl 0 (by simp)
      · simpa using hpair l' hl 1 (by simp)
    have hYa1 : l.pt + 1 ∈ (ofWord L st w).inv := by
      refine mem_inv_of L st _ hli.2.1 w hpw fun l' hl => ⟨?_, ?_⟩
      · intro h0
        apply hpair l' hl (-1) (by simp)
        push_cast
        linear_combination h0
      · intro h0
        apply hpair l' hl 0 (by simp)
        push_cast
        linear_combination h0
    have hne : Y ≠ l.pt := sub_ne_zero.1 hY.2.1
    have hfr := hFA A S r L st w hL hst hAw
    have hconj := hEC A S r L (ofWord L st w) Y l.pt hfr hY.1 hY1.1 hYa hYa1 hne
    have hEY := ih' Y hY.1 hY1.1 hYγ
    have hEa := ih' l.pt hYa hYa1 (hγ l (by simp))
    have hYw := ne_of_mem_inv L st Y w hpw hY.1
    have hposition : ∀ l' ∈ w, l.intersection_update_fsHerm_neg_one ≠ l'.intersection_update_fsHerm_neg_one := by
      rw [List.map_cons] at hs
      intro l' hl he
      exact (List.nodup_cons.1 hs).1 (he ▸ List.mem_map_of_mem hl)
    have hls := letterSum_step (A := A) l Y hne w [] fun l' hl =>
      ⟨hposition l' hl, hYw l' hl, fun he => by simpa [he] using hpair l' hl 0 (by simp)⟩

    have e1 : ((ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt).ee Y =
        Ph (eU l.intersection_update_fsHerm_neg_one 0 0) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹ ((ofWord L st w).ee Y) ((ofWord L st w).ee l.pt) +
          eU l.intersection_update_fsHerm_neg_one 0 0 * tz L - (Y - l.pt)⁻¹ • eU l.intersection_update_fsHerm_neg_one 0 1 := by
      have e2 : ((ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt).ee Y =
        ins l.intersection_update_fsHerm_neg_one !![(ofWord L st w).ee Y - (ofWord L st w).DD Y l.pt + tz L, -((Y - l.pt)⁻¹ • 1); 0,
          (ofWord L st w).xi l.pt * (ofWord L st w).ee Y * (ofWord L st w).x l.pt] := rfl
      rw [e2, ins_upper, eq_add_of_sub_eq hconj, Ph, FrameData.DD]
      simp only [mul_add, mul_neg, mul_smul_comm, mul_one]
      abel
    rw [e1, hEY, hEa, Ph_sub, Ph_add, Ph_const _ _ _ (eU_sum l.intersection_update_fsHerm_neg_one), Ph_sum, hls, Kw_cons]
    have e3 : ∀ j, Ph (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹
        ((Y - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult w (γ j)))
        ((l.pt - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult w (γ j))) =
        (Y - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult (l :: w) (γ j)) := by
      intro j
      rw [Ph_res _ _ _ _ _ _ (hYγ j) (hγ l (by simp) j) hne, ← mult_single, ← mul_assoc, mult_eq [l], dg_io,
        ← mult_eq, mul_assoc, ← mult_cons]
    simp only [e3, letterSum, mult_nil, mul_one, List.nil_append]
    abel

end Formalism.FourierDecayAlt.P
