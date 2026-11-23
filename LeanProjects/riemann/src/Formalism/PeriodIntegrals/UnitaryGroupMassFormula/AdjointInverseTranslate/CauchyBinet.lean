import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

open Matrix Finset

noncomputable section

namespace AAInvW

theorem collapse {A : Type*} [AddCommGroup A] [Module ℂ A] {N r m : ℕ} (hm : m ≤ r)
    (φ : Fin r → Fin N) (hφ : Function.Injective φ) (w : Fin N → Fin N → ℂ)
    (hw : ∀ (a : Fin r) (i : Fin N), (∀ b : Fin r, b.val < a.val → i ≠ φ b) →
      w i (φ a) = if i = φ a then 1 else 0)
    (q : (Fin m → Fin N) → A) (hq : ∀ c : Fin m → Fin N, ¬ Function.Injective c → q c = 0) :
    ∑ c : Fin m → Fin N, (∏ j, w (c j) (φ (Fin.castLE hm j))) • q c =
      q (fun j => φ (Fin.castLE hm j)) := by
  have hone : ∀ j : Fin m, w (φ (Fin.castLE hm j)) (φ (Fin.castLE hm j)) = 1 := by
    intro j
    have h := hw (Fin.castLE hm j) (φ (Fin.castLE hm j)) (fun b hb hb' => by
      have := hφ hb'
      rw [this] at hb
      exact lt_irrefl _ hb)
    rw [h, if_pos rfl]
  rw [Finset.sum_eq_single (fun j => φ (Fin.castLE hm j))]
  · simp only [hone, Finset.prod_const_one, one_smul]
  · intro c _ hc
    by_cases hinj : Function.Injective c
    · have hex : ∃ j, w (c j) (φ (Fin.castLE hm j)) = 0 := by
        by_contra hall
        push_neg at hall
        apply hc
        funext j
        obtain ⟨k, hk⟩ := j
        revert hk
        refine Nat.strong_induction_on k ?_
        intro k ih hk
        by_cases hex : ∃ b : Fin r, b.val < k ∧ c ⟨k, hk⟩ = φ b
        · obtain ⟨b, hbk, hb⟩ := hex
          have hbm : b.val < m := lt_trans hbk hk
          have e1 : c ⟨b.val, hbm⟩ = φ (Fin.castLE hm ⟨b.val, hbm⟩) := ih b.val hbk hbm
          have e2 : Fin.castLE hm ⟨b.val, hbm⟩ = b := Fin.ext rfl
          rw [e2] at e1
          have e3 := hinj (e1.trans hb.symm)
          have e4 : b.val = k := congrArg Fin.val e3
          omega
        · push_neg at hex
          have hw' := hw (Fin.castLE hm ⟨k, hk⟩) (c ⟨k, hk⟩) (fun b hb => hex b hb)
          have hne := hall ⟨k, hk⟩
          rw [hw'] at hne
          by_contra hcon
          exact hne (if_neg hcon)
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_smul]
    · rw [hq c hinj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem grouping {A : Type*} [Ring A] [Algebra ℂ A] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → A)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : A) * F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by
  classical
  have hR : ∀ C : Fin t → Fin N,
      (if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0) =
      ∑ σ : Equiv.Perm (Fin t),
        if StrictMono (fun l => κ (C l)) then W (C ∘ σ) • F (C ∘ σ) else 0 := by
    intro C
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hF C σ, mul_smul]
      first
      | rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_smul_comm]
      | simp only [Algebra.smul_def, map_intCast, ← mul_assoc, (Int.cast_commute _ _).eq]
    · simp
  simp only [hR]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1 ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨C, σ⟩ _ h1 ⟨C', σ'⟩ _ h2 heq
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    have hC' : StrictMono (fun l => κ (C' l)) := by
      by_contra hc
      exact h2 (by simp [hc])
    have heq' : C ∘ σ = C' ∘ σ' := heq
    have e1 : Set.range (fun l => κ (C l)) = Set.range (fun l => κ (C' l)) := by
      rw [← σ.surjective.range_comp (fun l => κ (C l)), ← σ'.surjective.range_comp (fun l => κ (C' l))]
      congr 1
      funext x
      exact congrArg κ (congrFun heq' x)
    have e2 : (fun l => κ (C l)) = (fun l => κ (C' l)) := by
      first
      | exact (StrictMono.range_inj hC hC').1 e1
      | exact (WellFounded.eq_strictMono_iff_eq_range wellFounded_lt hC hC').1 e1
    have e3 : C = C' := funext fun l => hκ (congrFun e2 l)
    subst e3
    have e4 : σ = σ' := Equiv.ext fun x => hC.injective (congrArg κ (congrFun heq' x))
    rw [e4]
  · intro d _ hd
    have hinj : Function.Injective d := by
      by_contra hni
      apply hd
      simp [hF0 d hni]
    have hmono : Monotone ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l))) :=
      Tuple.monotone_sort _
    have hsm : StrictMono (fun l => κ ((d ∘ Tuple.sort (fun l => κ (d l))) l)) :=
      hmono.strictMono_of_injective ((hκ.comp hinj).comp (Tuple.sort (fun l => κ (d l))).injective)
    have hcomp : (d ∘ Tuple.sort (fun l => κ (d l))) ∘ (Tuple.sort (fun l => κ (d l))).symm = d := by
      funext x
      simp
    refine ⟨(d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l))).symm),
      Finset.mem_univ _, ?_, ?_⟩
    · dsimp only
      rw [if_pos hsm, hcomp]
      exact hd
    · exact hcomp
  · rintro ⟨C, σ⟩ _ h1
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    dsimp only
    rw [if_pos hC]

theorem det_mul_expand {m N : ℕ} (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ d : Fin m → Fin N, (∏ l, Y (d l) l) • (Matrix.of fun a l => X a (d l)).det := by
  rw [← Matrix.det_transpose]
  have hT : (X * Y)ᵀ = fun l => ∑ k, Y k l • (fun a => X a k) := by
    ext l a
    simp [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [hT]
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_sum
    (fun l k => Y k l • (fun a => X a k))).trans ?_
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine ((Matrix.detRowAlternating (R := ℂ) (n := Fin m)).toMultilinearMap.map_smul_univ
    (fun l => Y (d l) l) (fun l a => X a (d l))).trans ?_
  congr 1
  rw [← Matrix.det_transpose]
  rfl

theorem cauchyBinet {m N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ C : Fin m → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (Matrix.of fun a l => X a (C l)).det * (Matrix.of fun i l => Y (C i) l).det else 0 := by
  have hF : ∀ (d : Fin m → Fin N) (τ : Equiv.Perm (Fin m)),
      (Matrix.of fun a l => X a ((d ∘ τ) l)).det =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Matrix.of fun a l => X a (d l)).det := by
    intro d τ
    exact Matrix.det_permute' τ (Matrix.of fun a l => X a (d l))
  have hF0 : ∀ d : Fin m → Fin N, ¬ Function.Injective d → (Matrix.of fun a l => X a (d l)).det = 0 := by
    intro d hd
    simp only [Function.Injective, not_forall] at hd
    obtain ⟨p, q, hpq, hne⟩ := hd
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hpq])
  rw [det_mul_expand X Y]
  rw [grouping κ hκ (fun d => (Matrix.of fun a l => X a (d l)).det) hF hF0 (fun d => ∏ l, Y (d l) l)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with h
  · rw [smul_eq_mul, mul_comm]
    congr 1
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp [Units.smul_def, zsmul_eq_mul]
  · rfl

end AAInvW
