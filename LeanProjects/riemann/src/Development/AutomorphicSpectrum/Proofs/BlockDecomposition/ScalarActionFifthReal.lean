import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperators

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.CapScal

theorem qdetNext : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ),
    ∃ c : ℕ → A, c (m + 1) = 1 ∧ c m = ∑ i, E i i + (∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ))) • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := GlobalTheory.CapelliNext.prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

open Polynomial

theorem sum_top {n : ℕ} (L : Fin n → ℝ) (S B : Finset (Fin n)) (hc : S.card = B.card)
    (hsep : ∀ b ∈ B, ∀ s ∈ S, s ∉ B → L s < L b) :
    ∑ a ∈ S, L a ≤ ∑ a ∈ B, L a ∧ (∑ a ∈ S, L a = ∑ a ∈ B, L a → S = B) := by
  have h1 : ∑ a ∈ S, L a = ∑ a ∈ S \ B, L a + ∑ a ∈ S ∩ B, L a := by rw [add_comm]; exact (Finset.sum_inter_add_sum_sdiff S B L).symm
  have h2 : ∑ a ∈ B, L a = ∑ a ∈ B \ S, L a + ∑ a ∈ S ∩ B, L a := by
    rw [Finset.inter_comm, add_comm]; exact (Finset.sum_inter_add_sum_sdiff B S L).symm
  have hk : (S \ B).card = (B \ S).card := Finset.card_sdiff_comm hc
  by_cases he : (S \ B).Nonempty
  · have he' : (B \ S).Nonempty := Finset.card_pos.1 (hk ▸ Finset.card_pos.2 he)
    obtain ⟨s0, hs0, hs⟩ := Finset.exists_max_image (S \ B) L he
    obtain ⟨b0, hb0, hb⟩ := Finset.exists_min_image (B \ S) L he'
    have hlt : L s0 < L b0 := hsep b0 (Finset.mem_sdiff.1 hb0).1 s0 (Finset.mem_sdiff.1 hs0).1 (Finset.mem_sdiff.1 hs0).2
    have a1 : ∑ a ∈ S \ B, L a ≤ (S \ B).card • L s0 := Finset.sum_le_card_nsmul _ _ _ hs
    have a2 : (B \ S).card • L b0 ≤ ∑ a ∈ B \ S, L a := Finset.card_nsmul_le_sum _ _ _ hb
    have a3 : (S \ B).card • L s0 < (B \ S).card • L b0 := by
      rw [hk]
      exact nsmul_lt_nsmul_right (Finset.card_pos.2 he').ne' hlt
    have : ∑ a ∈ S, L a < ∑ a ∈ B, L a := by rw [h1, h2]; linarith
    exact ⟨this.le, fun h => absurd h this.ne⟩
  · have e1 : S \ B = ∅ := Finset.not_nonempty_iff_eq_empty.1 he
    have e2 : B \ S = ∅ := Finset.card_eq_zero.1 (by rw [← hk, e1]; rfl)
    have hSB : S = B := (Finset.sdiff_eq_empty_iff_subset.1 e1).antisymm (Finset.sdiff_eq_empty_iff_subset.1 e2)
    exact ⟨by rw [hSB], fun _ => hSB⟩

theorem topFirst : ∀ (n : ℕ) (L : Fin n → ℝ), StrictAnti L → ∀ lev π π' : Fin n → ℕ, Monotone lev →
    (∀ j, (univ.filter fun a => π a = j).card = (univ.filter fun a => lev a = j).card) →
    (∀ j, (univ.filter fun a => π' a = j).card = (univ.filter fun a => lev a = j).card) →
    (∀ j, ∑ a ∈ univ.filter (fun a => π a = j), L a + ∑ a ∈ univ.filter (fun a => π' a = j), L a =
      2 * ∑ a ∈ univ.filter (fun a => lev a = j), L a) → π = lev ∧ π' = lev := by
  intro n L hL lev π π' hlev hc hc' hs
  have step : ∀ (ρ : Fin n → ℕ) (j : ℕ),
      (∀ i < j, univ.filter (fun a => ρ a = i) = univ.filter (fun a => lev a = i)) →
      ∀ b ∈ univ.filter (fun a => lev a = j), ∀ s ∈ univ.filter (fun a => ρ a = j),
        s ∉ univ.filter (fun a => lev a = j) → L s < L b := by
    intro ρ j ih b hb s hs1 hs2
    simp only [mem_filter, mem_univ, true_and] at hb hs1 hs2
    have hgt : j < lev s := by
      rcases lt_trichotomy (lev s) j with h | h | h
      · have hm : s ∈ univ.filter (fun a => lev a = lev s) := by simp
        rw [← ih _ h] at hm
        simp only [mem_filter, mem_univ, true_and] at hm
        omega
      · exact absurd h hs2
      · exact h
    refine hL ?_
    by_contra hle
    have := hlev (not_lt.1 hle)
    omega
  have main : ∀ j, univ.filter (fun a => π a = j) = univ.filter (fun a => lev a = j) ∧
      univ.filter (fun a => π' a = j) = univ.filter (fun a => lev a = j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      obtain ⟨a1, a2⟩ := sum_top L _ _ (hc j) (step π j fun i hi => (ih i hi).1)
      obtain ⟨b1, b2⟩ := sum_top L _ _ (hc' j) (step π' j fun i hi => (ih i hi).2)
      have := hs j
      exact ⟨a2 (by linarith), b2 (by linarith)⟩
  have fin : ∀ ρ : Fin n → ℕ, (∀ j, univ.filter (fun a => ρ a = j) = univ.filter (fun a => lev a = j)) → ρ = lev := by
    intro ρ h
    funext a
    have hm : a ∈ univ.filter (fun b => lev b = lev a) := by simp
    rw [← h] at hm
    simpa using hm
  exact ⟨fin π fun j => (main j).1, fin π' fun j => (main j).2⟩

theorem coeff_prod_top {A : Type} [CommRing A] [Nontrivial A] {κ : Type} (S : Finset κ) (hS : S.Nonempty) (f : κ → A) :
    (∏ a ∈ S, (X + C (f a))).coeff (S.card - 1) = ∑ a ∈ S, f a := by
  have hm : ∀ a ∈ S, (X + C (f a)).Monic := fun a _ => monic_X_add_C _
  have h1 := Polynomial.Monic.nextCoeff_prod S (fun a => X + C (f a)) hm
  have hd : (∏ a ∈ S, (X + C (f a))).natDegree = S.card := by
    rw [natDegree_prod_of_monic _ _ hm]; simp
  have hc : S.card ≠ 0 := (Finset.card_pos.2 hS).ne'
  rw [nextCoeff, if_neg (by rw [hd]; exact hc), hd] at h1
  rw [h1]
  exact Finset.sum_congr rfl fun a _ => nextCoeff_X_add_C _

theorem natDegree_prod_lin {A : Type} [CommRing A] [Nontrivial A] {κ : Type} (S : Finset κ) (f : κ → A) :
    (∏ a ∈ S, (X + C (f a))).natDegree = S.card := by
  rw [natDegree_prod_of_monic _ _ fun a _ => monic_X_add_C _]; simp

theorem split2 {A : Type} [CommRing A] [IsLocalRing A] {κ : Type} [DecidableEq κ] (ℓ : κ → A) (S : Finset κ) :
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (ℓ a - ℓ b)) → ∀ f g : A[X], f.Monic → g.Monic →
    f * g = ∏ a ∈ S, (X + C (ℓ a)) →
    ∃ S1 ⊆ S, f = ∏ a ∈ S1, (X + C (ℓ a)) ∧ g = ∏ a ∈ S \ S1, (X + C (ℓ a)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ f g hf hg h
    have hd := hf.natDegree_mul hg
    rw [h] at hd
    simp only [prod_empty, natDegree_one] at hd
    refine ⟨∅, subset_rfl, ?_, ?_⟩
    · simpa using hf.natDegree_eq_zero.1 (by omega)
    · simpa using hg.natDegree_eq_zero.1 (by omega)
  | insert a S ha ih =>
    intro hu f g hf hg h
    have hu' : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (ℓ a - ℓ b) := fun x hx y hy =>
      hu x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
    rw [prod_insert ha] at h
    set x : A := -ℓ a with hx
    have hlin : (X + C (ℓ a) : A[X]).eval x = 0 := by simp [hx]
    set Q : A[X] := ∏ b ∈ S, (X + C (ℓ b)) with hQdef
    have hQ : IsUnit (Q.eval x) := by
      rw [hQdef, eval_prod]
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun b hb => ?_
      have hne : b ≠ a := fun e => ha (e ▸ hb)
      have := hu b (mem_insert_of_mem hb) a (mem_insert_self _ _) hne
      simpa [hx, sub_eq_add_neg, add_comm] using this
    have hd : (derivative f).eval x * g.eval x + f.eval x * (derivative g).eval x = Q.eval x := by
      have := congrArg (fun p => (derivative p).eval x) h
      simp only [derivative_mul, eval_add, eval_mul, derivative_add, derivative_X, derivative_C, add_zero, eval_one,
        one_mul, hlin, zero_mul] at this
      exact this
    have hz : f.eval x * g.eval x = 0 := by rw [← eval_mul, h, eval_mul, hlin, zero_mul]
    have hroot : ∀ p : A[X], p.eval x = 0 → ∃ p1, p = (X + C (ℓ a)) * p1 := by
      intro p hp
      have h0 := dvd_iff_isRoot.2 (show IsRoot p x from hp)
      have h1 : (X + C (ℓ a) : A[X]) ∣ p := by simpa [hx, C_neg, sub_neg_eq_add] using h0
      obtain ⟨p1, h2⟩ := h1
      exact ⟨p1, h2⟩
    have hlm : (X + C (ℓ a) : A[X]).Monic := monic_X_add_C _
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hd ▸ hQ) with h1 | h2
    · have hgu : IsUnit (g.eval x) := isUnit_of_mul_isUnit_right h1
      obtain ⟨f1, rfl⟩ := hroot f (hgu.mul_left_eq_zero.1 hz)
      have hf1 : f1.Monic := hlm.of_mul_monic_left hf
      have hfg : f1 * g = Q := hlm.isRegular.left (by
        show (X + C (ℓ a)) * (f1 * g) = (X + C (ℓ a)) * Q
        rw [← mul_assoc, h])
      obtain ⟨S1, hs, e1, e2⟩ := ih hu' f1 g hf1 hg hfg
      refine ⟨insert a S1, Finset.insert_subset_insert a hs, ?_, ?_⟩
      · rw [prod_insert (fun h' => ha (hs h')), ← e1]
      · have : insert a S \ insert a S1 = S \ S1 := by
          ext b
          by_cases hb : b = a
          · subst hb
            simp [ha]
          · simp [hb]
        rw [this]
        exact e2
    · have hfu : IsUnit (f.eval x) := isUnit_of_mul_isUnit_left h2
      obtain ⟨g1, rfl⟩ := hroot g (hfu.mul_right_eq_zero.1 hz)
      have hg1 : g1.Monic := hlm.of_mul_monic_left hg
      have hfg : f * g1 = Q := hlm.isRegular.left (by
        show (X + C (ℓ a)) * (f * g1) = (X + C (ℓ a)) * Q
        rw [mul_left_comm, h])
      obtain ⟨S1, hs, e1, e2⟩ := ih hu' f g1 hf hg1 hfg
      refine ⟨S1, hs.trans (Finset.subset_insert _ _), e1, ?_⟩
      have haS1 : a ∉ S1 := fun h' => ha (hs h')
      have : insert a S \ S1 = insert a (S \ S1) := by
        ext b
        by_cases hb : b = a
        · subst hb
          simp [haS1]
        · simp [hb]
      rw [this, prod_insert (by simp [ha]), ← e2]

theorem splitLocal : ∀ (A : Type) [CommRing A] [IsLocalRing A] (κ : Type) [DecidableEq κ] (ℓ : κ → A) (J : Finset ℕ)
    (Q : ℕ → A[X]) (S : Finset κ), (∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (ℓ a - ℓ b)) → (∀ j ∈ J, (Q j).Monic) →
    ∏ j ∈ J, Q j = ∏ a ∈ S, (X + C (ℓ a)) →
    ∃ π : κ → ℕ, (∀ a ∈ S, π a ∈ J) ∧ ∀ j ∈ J, Q j = ∏ a ∈ S.filter (fun a => π a = j), (X + C (ℓ a)) := by
  intro A _ _ κ _ ℓ J Q
  induction J using Finset.induction_on with
  | empty =>
    intro S _ _ h
    have hd := natDegree_prod_lin S ℓ
    rw [← h] at hd
    simp only [prod_empty, natDegree_one] at hd
    have hS : S = ∅ := Finset.card_eq_zero.1 hd.symm
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | insert j J hj ih =>
    intro S hu hm h
    rw [prod_insert hj] at h
    obtain ⟨S1, hs, e1, e2⟩ := split2 ℓ S hu (Q j) (∏ i ∈ J, Q i) (hm j (mem_insert_self _ _))
      (monic_prod_of_monic _ _ fun i hi => hm i (mem_insert_of_mem hi)) h
    obtain ⟨π0, h1, h2⟩ := ih (S \ S1)
      (fun a ha b hb => hu a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
      (fun i hi => hm i (mem_insert_of_mem hi)) e2
    refine ⟨fun a => if a ∈ S1 then j else π0 a, fun a ha => ?_, fun i hi => ?_⟩
    · by_cases haS : a ∈ S1
      · simp [haS]
      · simp only [haS, if_false]
        exact mem_insert_of_mem (h1 a (Finset.mem_sdiff.2 ⟨ha, haS⟩))
    · rcases Finset.mem_insert.1 hi with rfl | hiJ
      · have : S.filter (fun a => (if a ∈ S1 then i else π0 a) = i) = S1 := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨haS, hq⟩
            by_contra hn
            simp only [hn, if_false] at hq
            exact hj (hq ▸ h1 a (Finset.mem_sdiff.2 ⟨haS, hn⟩))
          · intro ha
            exact ⟨hs ha, by simp [ha]⟩
        rw [this]
        exact e1
      · have hne : j ≠ i := fun e => hj (e ▸ hiJ)
        have : S.filter (fun a => (if a ∈ S1 then j else π0 a) = i) = (S \ S1).filter (fun a => π0 a = i) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          by_cases haS : a ∈ S1
          · simp [haS, hne]
          · simp [haS]
        rw [this]
        exact h2 i hiJ

theorem polyTopLocal {n : ℕ} (L : Fin n → ℝ) (hL : StrictAnti L) (lev : Fin n → ℕ) (hlev : Monotone lev)
    {A : Type} [CommRing A] [IsLocalRing A] (ψ : ℂ →+* A) (Q Q' : ℕ → A[X])
    (hm : ∀ j ∈ univ.image lev, (Q j).Monic ∧ (Q j).natDegree = (blk lev j).card)
    (hm' : ∀ j ∈ univ.image lev, (Q' j).Monic ∧ (Q' j).natDegree = (blk lev j).card)
    (hp : ∏ j ∈ univ.image lev, Q j = ∏ a, (X + C (ψ (L a : ℂ))))
    (hp' : ∏ j ∈ univ.image lev, Q' j = ∏ a, (X + C (ψ (L a : ℂ))))
    (ht : ∀ j ∈ univ.image lev, (Q j).coeff ((blk lev j).card - 1) + (Q' j).coeff ((blk lev j).card - 1) =
      ψ (2 * ∑ a ∈ blk lev j, (L a : ℂ))) :
    ∀ j ∈ univ.image lev, Q j = ∏ a ∈ blk lev j, (X + C (ψ (L a : ℂ))) := by
  have hu : ∀ a ∈ (univ : Finset (Fin n)), ∀ b ∈ (univ : Finset (Fin n)), a ≠ b →
      IsUnit (ψ (L a : ℂ) - ψ (L b : ℂ)) := by
    intro a _ b _ hab
    rw [← map_sub]
    refine IsUnit.map ψ (isUnit_iff_ne_zero.2 ?_)
    rw [sub_ne_zero]
    intro h
    exact hab (hL.injective (Complex.ofReal_injective h))
  obtain ⟨π, hπ, hQ⟩ := splitLocal A (Fin n) (fun a => ψ (L a : ℂ)) _ Q univ hu (fun j hj => (hm j hj).1) hp
  obtain ⟨π', hπ', hQ'⟩ := splitLocal A (Fin n) (fun a => ψ (L a : ℂ)) _ Q' univ hu (fun j hj => (hm' j hj).1) hp'
  have hnot : ∀ (ρ : Fin n → ℕ), (∀ a ∈ (univ : Finset (Fin n)), ρ a ∈ univ.image lev) → ∀ j, j ∉ univ.image lev →
      univ.filter (fun a => ρ a = j) = ∅ := by
    intro ρ hρ j hj
    refine Finset.filter_eq_empty_iff.2 fun a _ h => hj (h ▸ hρ a (mem_univ a))
  have hblk0 : ∀ j, j ∉ univ.image lev → univ.filter (fun a => lev a = j) = ∅ := fun j hj =>
    hnot lev (fun a _ => Finset.mem_image_of_mem _ (mem_univ a)) j hj
  have hcard : ∀ (ρ : Fin n → ℕ) (P : ℕ → A[X]), (∀ a ∈ (univ : Finset (Fin n)), ρ a ∈ univ.image lev) →
      (∀ j ∈ univ.image lev, (P j).Monic ∧ (P j).natDegree = (blk lev j).card) →
      (∀ j ∈ univ.image lev, P j = ∏ a ∈ univ.filter (fun a => ρ a = j), (X + C (ψ (L a : ℂ)))) →
      ∀ j, (univ.filter fun a => ρ a = j).card = (univ.filter fun a => lev a = j).card := by
    intro ρ P hρ hP hPe j
    by_cases hj : j ∈ univ.image lev
    · have := (hP j hj).2
      rw [hPe j hj, natDegree_prod_lin] at this
      exact this
    · rw [hnot ρ hρ j hj, hblk0 j hj]
  have hc := hcard π Q hπ hm hQ
  have hc' := hcard π' Q' hπ' hm' hQ'
  have hψ : Function.Injective ψ := ψ.injective
  have hsum : ∀ j, ∑ a ∈ univ.filter (fun a => π a = j), L a + ∑ a ∈ univ.filter (fun a => π' a = j), L a =
      2 * ∑ a ∈ univ.filter (fun a => lev a = j), L a := by
    intro j
    by_cases hj : j ∈ univ.image lev
    · have hne : (blk lev j).Nonempty := by
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
        exact ⟨a, by simp [blk]⟩
      have hcj : (blk lev j).card = (univ.filter fun a => π a = j).card := (hc j).symm
      have hcj' : (blk lev j).card = (univ.filter fun a => π' a = j).card := (hc' j).symm
      have hne1 : (univ.filter fun a => π a = j).Nonempty := Finset.card_pos.1 (hcj ▸ Finset.card_pos.2 hne)
      have hne2 : (univ.filter fun a => π' a = j).Nonempty := Finset.card_pos.1 (hcj' ▸ Finset.card_pos.2 hne)
      have h := ht j hj
      have e1 : (Q j).coeff ((blk lev j).card - 1) = ψ (∑ a ∈ univ.filter (fun a => π a = j), (L a : ℂ)) := by
        rw [hQ j hj, hcj, coeff_prod_top _ hne1, map_sum]
      have e2 : (Q' j).coeff ((blk lev j).card - 1) = ψ (∑ a ∈ univ.filter (fun a => π' a = j), (L a : ℂ)) := by
        rw [hQ' j hj, hcj', coeff_prod_top _ hne2, map_sum]
      rw [e1, e2, ← map_add] at h
      have h2 := hψ h
      apply Complex.ofReal_injective
      push_cast
      exact h2
    · rw [hnot π hπ j hj, hnot π' hπ' j hj, hblk0 j hj]
      simp
  obtain ⟨e1, -⟩ := topFirst n L hL lev π π' hlev hc hc' hsum
  intro j hj
  rw [hQ j hj, e1]
  rfl

theorem polyTop {n : ℕ} (L : Fin n → ℝ) (hL : StrictAnti L) (lev : Fin n → ℕ) (hlev : Monotone lev)
    {B : Type} [CommRing B] [Algebra ℂ B] (Q Q' : ℕ → B[X])
    (hm : ∀ j ∈ univ.image lev, (Q j).Monic ∧ (Q j).natDegree = (blk lev j).card)
    (hm' : ∀ j ∈ univ.image lev, (Q' j).Monic ∧ (Q' j).natDegree = (blk lev j).card)
    (hp : ∏ j ∈ univ.image lev, Q j = ∏ a, (X + C (algebraMap ℂ B (L a : ℂ))))
    (hp' : ∏ j ∈ univ.image lev, Q' j = ∏ a, (X + C (algebraMap ℂ B (L a : ℂ))))
    (ht : ∀ j ∈ univ.image lev, (Q j).coeff ((blk lev j).card - 1) + (Q' j).coeff ((blk lev j).card - 1) =
      algebraMap ℂ B (2 * ∑ a ∈ blk lev j, (L a : ℂ))) :
    ∀ j ∈ univ.image lev, Q j = ∏ a ∈ blk lev j, (X + C (algebraMap ℂ B (L a : ℂ))) := by
  intro j hj
  ext k
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun m hmax => ?_
  let A := Localization.AtPrime m
  let φ : B →+* A := algebraMap B A
  have key := polyTopLocal L hL lev hlev (φ.comp (algebraMap ℂ B)) (fun j => (Q j).map φ) (fun j => (Q' j).map φ)
    (fun j hj => ⟨(hm j hj).1.map φ, by
      rw [(hm j hj).1.natDegree_map φ]; exact (hm j hj).2⟩)
    (fun j hj => ⟨(hm' j hj).1.map φ, by
      rw [(hm' j hj).1.natDegree_map φ]; exact (hm' j hj).2⟩)
    (by
      rw [← Polynomial.map_prod, hp, Polynomial.map_prod]
      simp [Polynomial.map_add])
    (by
      rw [← Polynomial.map_prod, hp', Polynomial.map_prod]
      simp [Polynomial.map_add])
    (fun j hj => by
      rw [coeff_map, coeff_map, ← map_add, ht j hj]; rfl) j hj
  have h2 := congrArg (fun p => p.coeff k) key
  simp only [coeff_map] at h2
  rw [map_sub, sub_eq_zero]
  have h3 : (∏ a ∈ blk lev j, (X + C ((φ.comp (algebraMap ℂ B)) (L a : ℂ))) : A[X]) =
      (∏ a ∈ blk lev j, (X + C (algebraMap ℂ B (L a : ℂ)))).map φ := by
    rw [Polynomial.map_prod]; simp [Polynomial.map_add]
  rw [h3, coeff_map] at h2
  exact h2

theorem coeffs_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (d : ℕ → V)
    (h : ∀ Y : ℂ, ∑ i ∈ range N, Y ^ i • d i = 0) : ∀ i ∈ range N, d i = 0 := by
  intro i hi
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (d i)).1 fun φ => ?_
  have hp : (∑ k ∈ range N, C (φ (d k)) * X ^ k : ℂ[X]) = 0 := by
    refine Polynomial.funext fun Y => ?_
    have := congrArg φ (h Y)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 := congrArg (fun q => Polynomial.coeff q i) hp
  simpa [finset_sum_coeff, coeff_C_mul, coeff_X_pow, hi] using h2

theorem poly_eq_zero_of_eval {B : Type} [CommRing B] [Algebra ℂ B] (p : B[X])
    (h : ∀ u : ℂ, p.eval (algebraMap ℂ B u) = 0) : p = 0 := by
  ext i
  by_cases hi : i < p.natDegree + 1
  · refine coeffs_zero (p.natDegree + 1) (fun k => p.coeff k) (fun Y => ?_) i (Finset.mem_range.2 hi)
    rw [← h Y, eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_pow, mul_comm]
  · simpa using coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i)

theorem coeff_mem_of_values {A : Type} [AddCommGroup A] [Module ℂ A] (W : Submodule ℂ A) (N : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ range N, u ^ k • c k ∈ W) : ∀ k ∈ range N, c k ∈ W := by
  intro k hk
  have := coeffs_zero N (fun i => W.mkQ (c i)) (fun Y => by
    have h0 := (Submodule.Quotient.mk_eq_zero W).2 (h Y)
    rw [← Submodule.mkQ_apply, map_sum] at h0
    simpa only [map_smul] using h0) k hk
  exact (Submodule.Quotient.mk_eq_zero W).1 this

theorem sum_fin_cast (m : ℕ) : ∑ k : Fin (m + 1), ((k : ℕ) : ℂ) = (m : ℂ) * ((m : ℂ) + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℂ)) (m + 1)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem qminor_eq_qdet {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (F : Fin n → Fin n → A) (e : Fin t → Fin n)
    (he : Function.Injective e) (u : ℂ) :
    Formalism.REAL.qminor F e e u = Formalism.REAL.qdet (fun p q => F (e p) (e q)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  refine congrArg List.ofFn (funext fun k => ?_)
  simp [Formalism.REAL.Tm, he.eq_iff]

theorem capCoeffs {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (ht : 0 < t) (F : Fin n → Fin n → A)
    (e : Fin t → Fin n) (he : Function.Injective e) (s : ℂ) :
    ∃ c : ℕ → A, c t = 1 ∧ c (t - 1) = ∑ i, F (e i) (e i) - ((t : ℂ) * s) • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qminor F e e (u - s + ((t : ℂ) - 1) / 2) = ∑ k ∈ range (t + 1), u ^ k • c k := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  obtain ⟨c, h1, h2, h3⟩ := qdetNext A m (fun p q => F (e p) (e q)) (s - (m : ℂ) / 2)
  refine ⟨c, h1, ?_, fun u => ?_⟩
  · have hs : ∑ k : Fin (m + 1), (-(s - (m : ℂ) / 2) - ((k : ℕ) : ℂ)) = -(((m + 1 : ℕ) : ℂ) * s) := by
      rw [Finset.sum_sub_distrib, sum_fin_cast]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Nat.add_sub_cancel, h2, hs, neg_smul, sub_eq_add_neg]
  · rw [qminor_eq_qdet F e he, ← h3 u]
    congr 1
    push_cast
    ring

theorem capPoly {R : Type} [CommRing R] [Nontrivial R] [Algebra ℂ R] {A : Type} [Ring A] [Algebra ℂ A] (ι : R →ₐ[ℂ] A) (t : ℕ)
    (q : ℂ → A) (c : ℕ → A) (hq : ∀ u, q u = ∑ k ∈ range (t + 1), u ^ k • c k) (h1 : c t = 1)
    (hmem : ∀ u, q u ∈ ι.range) :
    ∃ p : R[X], p.Monic ∧ p.natDegree = t ∧ (∀ u : ℂ, ι (p.eval (algebraMap ℂ R u)) = q u) ∧
      ∀ k ≤ t, ι (p.coeff k) = c k := by
  have hc : ∀ k ∈ range (t + 1), c k ∈ Subalgebra.toSubmodule ι.range :=
    coeff_mem_of_values _ _ c fun u => by
      rw [← hq u]
      exact hmem u
  have hd : ∀ k, ∃ d : R, k ∈ range (t + 1) → ι d = c k := by
    intro k
    by_cases hk : k ∈ range (t + 1)
    · obtain ⟨d, hd⟩ := hc k hk
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose d hd using hd
  set r : R[X] := ∑ k ∈ range t, C (d k) * X ^ k with hr
  have hcoef : ∀ k, r.coeff k = if k < t then d k else 0 := by
    intro k
    simp only [hr, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
    simp [Finset.sum_ite_eq, Finset.mem_range]
  have hdeg : r.degree < t := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [hcoef, if_neg (by omega)]
  refine ⟨X ^ t + r, monic_X_pow_add hdeg, by rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow], fun u => ?_, fun k hk => ?_⟩
  · rw [hq u, Finset.sum_range_succ, h1, eval_add, eval_pow, eval_X, map_add, map_pow, add_comm]
    congr 1
    · rw [hr, eval_finset_sum, map_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow, hd k (by
        have := Finset.mem_range.1 hk
        exact Finset.mem_range.2 (by omega)), AlgHom.commutes, Algebra.smul_def, map_pow]
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    · rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, _root_.smul_pow, one_pow]
  · rw [coeff_add, hcoef, coeff_X_pow]
    by_cases hkt : k = t
    · subst hkt
      simp [h1]
    · have hlt : k < t := by omega
      simp [hkt, hlt, hd k (Finset.mem_range.2 (by omega))]

theorem sum_blkE {n : ℕ} {M : Type} [AddCommMonoid M] (lev : Fin n → ℕ) (j : ℕ) (f : Fin n → M) :
    ∑ i, f (blkE lev j i) = ∑ a ∈ blk lev j, f a := by
  rw [← Finset.sum_coe_sort (blk lev j) f]
  exact Fintype.sum_equiv ((blk lev j).orderIsoOfFin rfl).toEquiv _ _ fun i => by simp [blkE]

variable {H : Type} [AddCommGroup H] [Module ℂ H] {n : ℕ}

theorem capS_poly {R : Type} [CommRing R] [Nontrivial R] [Algebra ℂ R] (ι : R →ₐ[ℂ] Module.End ℂ H)
    (F : Fin n → Fin n → Module.End ℂ H) (lev : Fin n → ℕ) (hmem : ∀ j u, capS F lev j u ∈ ι.range) (σ : ℕ → ℂ)
    (j : ℕ) (hj : j ∈ univ.image lev) :
    ∃ p : R[X], p.Monic ∧ p.natDegree = (blk lev j).card ∧
      (∀ u : ℂ, ι (p.eval (algebraMap ℂ R u)) = capS F lev j (u - σ j)) ∧
      ι (p.coeff ((blk lev j).card - 1)) = ∑ a ∈ blk lev j, F a a - (((blk lev j).card : ℂ) * σ j) • (1 : Module.End ℂ H) := by
  have hpos : 0 < (blk lev j).card := by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.card_pos.2 ⟨a, by simp [blk]⟩
  obtain ⟨c, h1, h2, h3⟩ := capCoeffs hpos F (blkE lev j) ((blk lev j).orderEmbOfFin rfl).injective (σ j)
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := capPoly ι (blk lev j).card (fun u => capS F lev j (u - σ j)) c (fun u => h3 u) h1
    (fun u => hmem j _)
  refine ⟨p, hp1, hp2, hp3, ?_⟩
  rw [hp4 _ (Nat.sub_le _ _), h2, sum_blkE lev j fun a => F a a]

theorem ι_prod_levs {R : Type} [CommRing R] [Algebra ℂ R] (ι : R →ₐ[ℂ] Module.End ℂ H) (lev : Fin n → ℕ) (g : ℕ → R) :
    ι (∏ j ∈ univ.image lev, g j) = ((levs lev).map fun j => ι (g j)).prod := by
  have h : ∏ j ∈ univ.image lev, g j = ((levs lev).map g).prod := by
    unfold levs
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [h, map_list_prod, List.map_map]
  rfl

theorem core {R : Type} [CommRing R] [Algebra ℂ R] (ι : R →ₐ[ℂ] Module.End ℂ H)
    (L : Fin n → ℝ) (hL : StrictAnti L) (lev : Fin n → ℕ) (hlev : Monotone lev) (ν : Fin n → ℝ) (σ1 σ2 : ℕ → ℂ)
    (hsh : ∀ j, (∑ a ∈ blk lev j, (ν a : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) = 2 * ∑ a ∈ blk lev j, (L a : ℂ))
    (F1 F2 : Fin n → Fin n → Module.End ℂ H) (hm1 : ∀ j u, capS F1 lev j u ∈ ι.range)
    (hm2 : ∀ j u, capS F2 lev j u ∈ ι.range) (c : H)
    (hsemi : ∀ a b, lev a = lev b → (F1 a b + F2 a b) c = if a = b then (ν a : ℂ) • c else 0)
    (h1 : ∀ u : ℂ, capProd F1 lev σ1 u c = (∏ a, (u + (L a : ℂ))) • c)
    (h2 : ∀ u : ℂ, capProd F2 lev σ2 u c = (∏ a, (u + (L a : ℂ))) • c) (j : ℕ) (hj : j ∈ univ.image lev) (u : ℂ) :
    capS F1 lev j u c = (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ))) • c := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]
  haveI : Nontrivial R := ⟨0, 1, fun h => hc0 (by simpa using (congrArg (fun r => ι r c) h).symm)⟩
  have e1 := fun j (hj : j ∈ univ.image lev) => capS_poly ι F1 lev hm1 σ1 j hj
  have e2 := fun j (hj : j ∈ univ.image lev) => capS_poly ι F2 lev hm2 σ2 j hj
  choose! p hp1 hp2 hp3 hp4 using e1
  choose! p' hp1' hp2' hp3' hp4' using e2
  let I : Ideal R :=
    { carrier := {r | ι r c = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, map_zero] }
  have hI : ∀ r : R, Ideal.Quotient.mk I r = 0 ↔ ι r c = 0 := fun r => Ideal.Quotient.eq_zero_iff_mem
  have hscal : ∀ x : ℂ, ι (algebraMap ℂ R x) c = x • c := fun x => by
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
  let mk := Ideal.Quotient.mkₐ ℂ I
  have hmk : ∀ r, mk r = Ideal.Quotient.mk I r := fun _ => rfl
  have hprod : ∀ (P : ℕ → R[X]) (σ : ℕ → ℂ) (F : Fin n → Fin n → Module.End ℂ H),
      (∀ j ∈ univ.image lev, ∀ u : ℂ, ι ((P j).eval (algebraMap ℂ R u)) = capS F lev j (u - σ j)) →
      (∀ u : ℂ, capProd F lev σ u c = (∏ a, (u + (L a : ℂ))) • c) →
      ∏ j ∈ univ.image lev, (P j).map mk.toRingHom = ∏ a, (X + C (algebraMap ℂ (R ⧸ I) (L a : ℂ))) := by
    intro P σ F hP hF
    rw [← sub_eq_zero]
    refine poly_eq_zero_of_eval _ fun u => ?_
    rw [eval_sub, eval_prod, eval_prod, sub_eq_zero]
    have a1 : ∀ j, ((P j).map mk.toRingHom).eval (algebraMap ℂ (R ⧸ I) u) = mk ((P j).eval (algebraMap ℂ R u)) := by
      intro j
      rw [← mk.commutes u]
      exact eval_map_apply _ _ |>.trans rfl
    have a2 : ∀ a, (X + C (algebraMap ℂ (R ⧸ I) (L a : ℂ))).eval (algebraMap ℂ (R ⧸ I) u) =
        mk (algebraMap ℂ R (u + (L a : ℂ))) := by
      intro a
      simp only [eval_add, eval_X, eval_C, AlgHom.commutes, map_add]
    simp only [a1, a2]
    rw [← map_prod, ← map_prod, ← sub_eq_zero, ← map_sub, hmk, hI, map_sub, LinearMap.sub_apply, sub_eq_zero,
      ι_prod_levs, ← map_prod, hscal]
    rw [← hF u]
    unfold capProd
    congr 2
    exact List.map_congr_left fun j hj => hP j (by simpa [levs] using hj) u
  have ht : ∀ j ∈ univ.image lev, ((p j).map mk.toRingHom).coeff ((blk lev j).card - 1) +
      ((p' j).map mk.toRingHom).coeff ((blk lev j).card - 1) =
      algebraMap ℂ (R ⧸ I) (2 * ∑ a ∈ blk lev j, (L a : ℂ)) := by
    intro j hj
    rw [coeff_map, coeff_map, ← mk.commutes]
    show mk _ + mk _ = mk _
    rw [← map_add, ← sub_eq_zero, ← map_sub, hmk, hI, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      hp4 j hj, hp4' j hj, hscal, ← hsh j]
    have hs : ∑ a ∈ blk lev j, (F1 a a c + F2 a a c) = ∑ a ∈ blk lev j, (ν a : ℂ) • c :=
      Finset.sum_congr rfl fun a _ => by simpa using hsemi a a rfl
    rw [Finset.sum_add_distrib, ← Finset.sum_smul] at hs
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [sub_smul, mul_add, add_smul, ← hs]
    abel
  haveI : Nontrivial (R ⧸ I) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun h => hc0 ?_
    have h1I : (1 : R) ∈ I := h ▸ Submodule.mem_top
    simpa using (show ι 1 c = 0 from h1I)
  have key := polyTop L hL lev hlev (fun j => (p j).map mk.toRingHom) (fun j => (p' j).map mk.toRingHom)
    (fun j hj => ⟨(hp1 j hj).map _, by rw [(hp1 j hj).natDegree_map]; exact hp2 j hj⟩)
    (fun j hj => ⟨(hp1' j hj).map _, by rw [(hp1' j hj).natDegree_map]; exact hp2' j hj⟩)
    (hprod p σ1 F1 hp3 h1) (hprod p' σ2 F2 hp3' h2) ht j hj
  have a1 : ((p j).map mk.toRingHom).eval (algebraMap ℂ (R ⧸ I) (u + σ1 j)) =
      mk ((p j).eval (algebraMap ℂ R (u + σ1 j))) := by
    rw [← mk.commutes]
    exact eval_map_apply _ _ |>.trans rfl
  have a2 : (∏ a ∈ blk lev j, (X + C (algebraMap ℂ (R ⧸ I) (L a : ℂ)))).eval (algebraMap ℂ (R ⧸ I) (u + σ1 j)) =
      mk (algebraMap ℂ R (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ)))) := by
    rw [eval_prod, map_prod, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [eval_add, eval_X, eval_C, AlgHom.commutes, map_add]
  have h3 : mk ((p j).eval (algebraMap ℂ R (u + σ1 j))) =
      mk (algebraMap ℂ R (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ)))) := by
    rw [← a1, ← a2]
    exact congrArg (fun P => P.eval (algebraMap ℂ (R ⧸ I) (u + σ1 j))) key
  rw [← sub_eq_zero, ← map_sub, hmk, hI, map_sub, LinearMap.sub_apply, sub_eq_zero, hp3 j hj, hscal,
    add_sub_cancel_right] at h3
  exact h3

theorem capS_eq {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ)
    (j : ℕ) (u : ℂ) : capS F lev j u = Formalism.REAL.qdet (fun p q => F (blkE lev j p) (blkE lev j q))
      (u + (((blk lev j).card : ℂ) - 1) / 2) :=
  qminor_eq_qdet F _ ((blk lev j).orderEmbOfFin rfl).injective _

theorem lev_blkE {n : ℕ} (lev : Fin n → ℕ) (j : ℕ) (i : Fin (blk lev j).card) : lev (blkE lev j i) = j := by
  have := Finset.orderEmbOfFin_mem (blk lev j) rfl i
  simpa [blk, blkE] using this

theorem blkE_inj {n : ℕ} (lev : Fin n → ℕ) (j : ℕ) : Function.Injective (blkE lev j) :=
  ((blk lev j).orderEmbOfFin rfl).injective

theorem capComm : ∀ (n : ℕ) (lev : Fin n → ℕ) (H : Type) [AddCommGroup H] [Module ℂ H]
    (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 → ∀ (j j' : ℕ) (u v : ℂ),
    Commute (capS F1 lev j u) (capS F1 lev j' v) ∧ Commute (capS F2 lev j u) (capS F2 lev j' v) ∧
      Commute (capS F1 lev j u) (capS F2 lev j' v) := by
  intro n lev H _ _ F1 F2 hF j j' u v
  have same : ∀ F : Fin n → Fin n → Module.End ℂ H,
      (∀ a b c d, lev a = lev b → lev c = lev d →
        F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)) →
      Commute (capS F lev j u) (capS F lev j' v) := by
    intro F hG
    rw [capS_eq, capS_eq]
    by_cases hjj : j = j'
    · subst hjj
      refine GlobalTheory.CompanionTheory.CapCoeff.qdet_commute_self _ (fun a b c d => ?_) _ _
      have h := hG (blkE lev j a) (blkE lev j b) (blkE lev j c) (blkE lev j d)
        (by rw [lev_blkE lev, lev_blkE lev]) (by rw [lev_blkE lev, lev_blkE lev])
      simpa only [(blkE_inj lev j).eq_iff] using h
    · refine GlobalTheory.CompanionTheory.CapCoeff.qdet_commute_of _ _ (fun a b c d => ?_) _ _
      have h := hG (blkE lev j a) (blkE lev j b) (blkE lev j' c) (blkE lev j' d)
        (by rw [lev_blkE lev, lev_blkE lev]) (by rw [lev_blkE lev, lev_blkE lev])
      have hne1 : blkE lev j b ≠ blkE lev j' c := fun e => hjj (by
        have := congrArg lev e; rwa [lev_blkE lev, lev_blkE lev] at this)
      have hne2 : blkE lev j' d ≠ blkE lev j a := fun e => hjj (by
        have := congrArg lev e; rw [lev_blkE lev, lev_blkE lev] at this; exact this.symm)
      rw [if_neg hne1, if_neg hne2, sub_zero] at h
      exact sub_eq_zero.1 h
  refine ⟨same F1 fun a b c d h1 h2 => (hF a b c d h1 h2).1, same F2 fun a b c d h1 h2 => (hF a b c d h1 h2).2.1, ?_⟩
  rw [capS_eq, capS_eq]
  refine GlobalTheory.CompanionTheory.CapCoeff.qdet_commute_of _ _ (fun a b c d => ?_) _ _
  exact (hF _ _ _ _ (by rw [lev_blkE lev, lev_blkE lev]) (by rw [lev_blkE lev, lev_blkE lev])).2.2

theorem capScal : CapelliProductsScalar := by
  intro n L hL lev hlev ν σ1 σ2 hsh H _ _ F1 F2 hF c hsemi h1 h2 j u
  by_cases hj : j ∈ univ.image lev
  · let Gs : Set (Module.End ℂ H) := Set.range (fun p : ℕ × ℂ => capS F1 lev p.1 p.2) ∪
      Set.range (fun p : ℕ × ℂ => capS F2 lev p.1 p.2)
    have hcomm : ∀ a ∈ Gs, ∀ b ∈ Gs, a * b = b * a := by
      rintro _ (⟨p, rfl⟩ | ⟨p, rfl⟩) _ (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact (capComm n lev H F1 F2 hF p.1 q.1 p.2 q.2).1
      · exact (capComm n lev H F1 F2 hF p.1 q.1 p.2 q.2).2.2
      · exact (capComm n lev H F1 F2 hF q.1 p.1 q.2 p.2).2.2.symm
      · exact (capComm n lev H F1 F2 hF p.1 q.1 p.2 q.2).2.1
    letI : CommRing (Algebra.adjoin ℂ Gs) := Algebra.adjoinCommRingOfComm ℂ hcomm
    exact core (Algebra.adjoin ℂ Gs).val L hL lev hlev ν σ1 σ2 hsh F1 F2
      (fun j u => ⟨⟨_, Algebra.subset_adjoin (Or.inl ⟨(j, u), rfl⟩)⟩, rfl⟩)
      (fun j u => ⟨⟨_, Algebra.subset_adjoin (Or.inr ⟨(j, u), rfl⟩)⟩, rfl⟩) c hsemi h1 h2 j hj u
  · have hb : blk lev j = ∅ := Finset.filter_eq_empty_iff.2 fun a _ h => hj (h ▸ Finset.mem_image_of_mem _ (mem_univ a))
    have h0 : ∀ (t : ℕ), t = 0 → ∀ (e : Fin t → Fin n) (x : ℂ), Formalism.REAL.qminor F1 e e x = 1 := by
      rintro _ rfl e x
      simp [Formalism.REAL.qminor]
    unfold capS
    rw [h0 _ (by rw [hb]; rfl), hb]
    simp

end GlobalTheory.CompanionTheory.CapScal
