import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSepFac

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Comm

variable {B : Type} [CommRing B] [Algebra ℂ B]

theorem factor_roots (e : B) (P : B[X]) (J : Finset ℂ) (h : ∀ α ∈ J, e * P.eval (algebraMap ℂ B α) = 0) :
    ∃ Rm : B[X], C e * P = (∏ α ∈ J, (X - C (algebraMap ℂ B α))) * Rm := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨C e * P, by simp⟩
  | insert β J hβ ih =>
    obtain ⟨Rm, hRm⟩ := ih fun α hα => h α (Finset.mem_insert_of_mem hα)
    have hu : IsUnit (∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α)) := by
      have e0 : ∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α) = algebraMap ℂ B (∏ α ∈ J, (β - α)) := by
        simp [map_prod, map_sub]
      rw [e0]
      refine (IsUnit.mk0 _ ?_).map (algebraMap ℂ B)
      exact Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 fun h' => hβ (h' ▸ hα)
    have h0 : Rm.eval (algebraMap ℂ B β) = 0 := by
      have e1 := congrArg (eval (algebraMap ℂ B β)) hRm
      rw [eval_mul, eval_C, h β (Finset.mem_insert_self _ _), eval_mul, eval_prod] at e1
      simp only [eval_sub, eval_X, eval_C] at e1
      exact hu.mul_right_eq_zero.1 e1.symm
    refine ⟨Rm /ₘ (X - C (algebraMap ℂ B β)), ?_⟩
    rw [hRm, Finset.prod_insert hβ]
    conv_lhs => rw [← (mul_divByMonic_eq_iff_isRoot).2 h0]
    ring

omit [Algebra ℂ B] in

theorem factor_deg {e : B} {P Pi Rm : B[X]} (hP : P.Monic) (hPi : Pi.Monic) (h : C e * P = Pi * Rm) :
    (Pi.natDegree ≤ P.natDegree ∨ e = 0) ∧ (Pi.natDegree = P.natDegree → ∀ k, e * P.coeff k = Pi.coeff k * e) := by
  by_cases hR : Rm = 0
  · have h0 : C e * P = 0 := by rw [h, hR, mul_zero]
    have he : e = 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h0
      simpa [coeff_C_mul, hP.coeff_natDegree] using this
    exact ⟨Or.inr he, fun _ k => by simp [he]⟩
  · have hdeg : (Pi * Rm).natDegree = Pi.natDegree + Rm.natDegree := hPi.natDegree_mul' hR
    have hle : (C e * P).natDegree ≤ P.natDegree := natDegree_C_mul_le e P
    rw [h, hdeg] at hle
    refine ⟨Or.inl (by omega), fun hm k => ?_⟩
    have hRC : Rm = C (Rm.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h2 : C e * P = Pi * C (Rm.coeff 0) := by
      rw [h]
      conv_lhs => rw [hRC]
    have hb : e = Rm.coeff 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h2
      simp only [coeff_C_mul, coeff_mul_C, hP.coeff_natDegree, mul_one] at this
      rw [this, ← hm, hPi.coeff_natDegree, one_mul]
    have := congrArg (fun F : B[X] => F.coeff k) h2
    simp only [coeff_C_mul, coeff_mul_C] at this
    rw [this, ← hb]

theorem isSS_coeff (p : ℂ[X]) (hp : p.Separable) (P Q : B[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = p.map (algebraMap ℂ B)) (k : ℕ) : IsSS (P.coeff k) := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨∅, Subsingleton.elim _ _⟩
  have hinj : Function.Injective (algebraMap ℂ B) := (algebraMap ℂ B).injective
  have hp0 : p ≠ 0 := hp.ne_zero
  set R := p.roots.toFinset with hR
  have hdegPQ : P.natDegree + Q.natDegree = p.natDegree := by
    rw [← hP.natDegree_mul hQ, hPQ, natDegree_map_eq_of_injective hinj]
  have hcard : R.card = p.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup (nodup_roots hp)]
    exact IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ α ∈ R, p.eval α = 0 := fun α hα => by
    rw [hR, Multiset.mem_toFinset, mem_roots hp0] at hα
    exact hα
  have hder : ∀ α ∈ R, p.derivative.eval α ≠ 0 := fun α hα h0 => by
    obtain ⟨u, v, huv⟩ : IsCoprime p (derivative p) := hp
    have := congrArg (eval α) huv
    simp [eval_add, eval_mul, hroot α hα, h0] at this
  have hPQa : ∀ α ∈ R, P.eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    rw [← eval_mul, hPQ, eval_map, eval₂_at_apply, hroot α hα, map_zero]
  have hDa : ∀ α ∈ R, (derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
      P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) = algebraMap ℂ B (p.derivative.eval α) := by
    intro α hα
    rw [← eval_mul, ← eval_mul, ← eval_add, ← derivative_mul, hPQ, derivative_map, eval_map, eval₂_at_apply]
  let e : ℂ → B := fun α =>
    P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹
  have heQ : ∀ α ∈ R, e α * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    linear_combination ((derivative Q).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  have hfP : ∀ α ∈ R, (1 - e α) * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    have hI : ((derivative P).eval (algebraMap ℂ B α) * Q.eval (algebraMap ℂ B α) +
        P.eval (algebraMap ℂ B α) * (derivative Q).eval (algebraMap ℂ B α)) *
          algebraMap ℂ B (p.derivative.eval α)⁻¹ = 1 := by
      rw [hDa α hα, ← map_mul, mul_inv_cancel₀ (hder α hα), map_one]
    linear_combination (-P.eval (algebraMap ℂ B α)) * hI +
      ((derivative P).eval (algebraMap ℂ B α) * algebraMap ℂ B (p.derivative.eval α)⁻¹) * hPQa α hα
  let E : Finset ℂ → B := fun I => (∏ α ∈ I, e α) * ∏ α ∈ R \ I, (1 - e α)
  have hsum : ∑ I ∈ R.powerset, E I = 1 := by
    simp only [E]
    rw [← Finset.prod_add]
    simp
  have hmonJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).Monic := fun J =>
    monic_prod_of_monic _ _ fun α _ => monic_X_sub_C _
  have hdegJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))).natDegree = J.card := by
    intro J
    rw [natDegree_prod_of_monic _ _ fun α _ => monic_X_sub_C _]
    simp
  have hmapJ : ∀ J : Finset ℂ, (∏ α ∈ J, (X - C (algebraMap ℂ B α))) = (∏ α ∈ J, (X - C α)).map (algebraMap ℂ B) := by
    intro J
    simp [Polynomial.map_prod]
  refine isSS_of_decomp R.powerset E (fun I => (∏ α ∈ R \ I, (X - C α)).coeff k) hsum fun I hI => ?_
  rw [Finset.mem_powerset] at hI
  by_cases hE : E I = 0
  · rw [hE, mul_zero, smul_zero]
  have hEQ : ∀ α ∈ I, E I * Q.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * Q.eval (algebraMap ℂ B α) =
        (e α * Q.eval (algebraMap ℂ B α)) * ((∏ β ∈ I.erase α, e β) * ∏ β ∈ R \ I, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase I e hα]
          ring
      _ = 0 := by rw [heQ α (hI hα), zero_mul]
  have hEP : ∀ α ∈ R \ I, E I * P.eval (algebraMap ℂ B α) = 0 := by
    intro α hα
    calc E I * P.eval (algebraMap ℂ B α) =
        ((1 - e α) * P.eval (algebraMap ℂ B α)) * ((∏ β ∈ I, e β) * ∏ β ∈ (R \ I).erase α, (1 - e β)) := by
          simp only [E]
          rw [← Finset.mul_prod_erase (R \ I) (fun β => 1 - e β) hα]
          ring
      _ = 0 := by rw [hfP α (Finset.mem_sdiff.1 hα).1, zero_mul]
  obtain ⟨R₁, hR₁⟩ := factor_roots (E I) P (R \ I) hEP
  obtain ⟨R₂, hR₂⟩ := factor_roots (E I) Q I hEQ
  obtain ⟨h1, h2⟩ := factor_deg hP (hmonJ _) hR₁
  obtain ⟨h3, -⟩ := factor_deg hQ (hmonJ _) hR₂
  rw [hdegJ] at h1 h2 h3
  have hsd := Finset.card_sdiff_add_card_eq_card hI
  have heq : (R \ I).card = P.natDegree := by
    rcases h1 with h1 | h1
    · rcases h3 with h3 | h3
      · omega
      · exact absurd h3 hE
    · exact absurd h1 hE
  have := h2 heq k
  rw [hmapJ, coeff_map] at this
  rw [mul_comm, this, Algebra.smul_def, mul_comm]

theorem eq_zero_of_eval_algebraMap (D : B[X]) (h : ∀ u : ℂ, D.eval (algebraMap ℂ B u) = 0) : D = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff k)).1 fun φ => ?_
  let q : ℂ[X] := ∑ i ∈ Finset.range (D.natDegree + 1), monomial i (φ (D.coeff i))
  have hq : q = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 : φ (D.eval (algebraMap ℂ B u)) = 0 := by rw [h u, map_zero]
    rw [eval_eq_sum_range, map_sum] at h1
    rw [eval_zero, ← h1, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hc : q.coeff k = φ (D.coeff k) := by
    simp only [q, finsetSum_coeff, coeff_monomial]
    by_cases hk : k ∈ Finset.range (D.natDegree + 1)
    · rw [Finset.sum_ite_eq']
      simp [hk]
    · rw [Finset.sum_eq_zero]
      · have : D.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hk)
        simp [this]
      · intro i hi
        rw [if_neg]
        rintro rfl
        exact hk hi
  rw [← hc, hq, coeff_zero]

end Comm

section Fun

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem IsSS.adjoin {s : Set A} (hs : ∀ x ∈ s, IsSS x) (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Algebra.adjoin ℂ s, IsSS y := by
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ s, ∀ y ∈ Algebra.adjoin ℂ s, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => ?_
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hc b hb a ha).symm
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap c => exact isSS_algebraMap c
  | add x y hx hy ihx ihy => exact ihx.add ihy (hcomm x hx y hy)
  | mul x y hx hy ihx ihy => exact ihx.mul ihy (hcomm x hx y hy)

set_option linter.deprecated false in

theorem isSS_coeff_fun (m : Multiset ℂ) (hm : m.Nodup) (r s : ℕ) (_hrs : Multiset.card m = r + s) (c₁ c₂ : ℂ)
    (a b : ℕ → A) (ha : a r = 1) (hb : b s = 1)
    (hcomm : ∀ i j, Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), (u + c₁) ^ k • a k) *
      (∑ k ∈ Finset.range (s + 1), (u + c₂) ^ k • b k) = algebraMap ℂ A (m.map (u + ·)).prod) (k : ℕ) :
    (k ≤ r → IsSS (a k)) ∧ (k ≤ s → IsSS (b k)) := by
  classical
  let S : Set A := Set.range a ∪ Set.range b
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact (hcomm i j).1.eq
    · exact (hcomm i j).2.1.eq
    · exact ((hcomm j i).2.1.eq).symm
    · exact (hcomm i j).2.2.eq
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  let a' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨b i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

  have key : ∀ (n : ℕ) (a' : ℕ → Algebra.adjoin ℂ S), a' n = 1 →
      ∃ P : (Algebra.adjoin ℂ S)[X], P.Monic ∧ (∀ k ≤ n, P.coeff k = a' k) ∧
        ∀ y : ℂ, P.eval (algebraMap ℂ _ y) = ∑ k ∈ Finset.range (n + 1), y ^ k • a' k := by
    intro n a' hn
    refine ⟨X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i, monic_X_pow_add ?_, fun k hk => ?_, fun y => ?_⟩
    · refine mem_degreeLT.1 (Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_)
      exact (degree_C_mul_X_pow_le i (a' i)).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)
    · simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
      rcases hk.lt_or_eq with hk | rfl
      · rw [if_neg hk.ne, zero_add, Finset.sum_ite_eq]
        simp [Finset.mem_range.2 hk]
      · rw [if_pos rfl, Finset.sum_ite_eq]
        simp [hn]
    · simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_range_succ, hn, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_pow, mul_comm, ← Algebra.smul_def]
      · rw [← map_pow, Algebra.algebraMap_eq_smul_one]
  obtain ⟨P, hPm, hPc, hPe⟩ := key r a' (Subtype.ext ha)
  obtain ⟨Q, hQm, hQc, hQe⟩ := key s b' (Subtype.ext hb)
  let p : ℂ[X] := (m.map fun x => X + C x).prod
  have hpe : p = ∏ x ∈ m.toFinset, (X - C (-x)) := by
    simp only [p]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hm]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [map_neg, sub_neg_eq_add]
  have hps : p.Separable := by
    rw [hpe]
    exact separable_prod_X_sub_C_iff'.2 fun x _ y _ h => neg_inj.1 h
  have hval : ∀ u : ℂ, p.eval u = (m.map (u + ·)).prod := by
    intro u
    simp only [p, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X, eval_C]

  have hrelP : P.comp (X + C (algebraMap ℂ _ c₁)) * Q.comp (X + C (algebraMap ℂ _ c₂)) =
      p.map (algebraMap ℂ (Algebra.adjoin ℂ S)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eval_algebraMap _ fun u => ?_
    rw [eval_sub, eval_mul, eval_comp, eval_comp, eval_map, eval₂_at_apply, hval]
    simp only [eval_add, eval_X, eval_C, ← map_add]
    rw [hPe, hQe, sub_eq_zero]
    apply Subtype.ext
    have hv : ∀ x y : Algebra.adjoin ℂ S, ((x * y : Algebra.adjoin ℂ S) : A) = (x : A) * y := fun x y => rfl
    have hsm : ∀ (c : ℂ) (x : Algebra.adjoin ℂ S), ((c • x : Algebra.adjoin ℂ S) : A) = c • (x : A) :=
      fun c x => rfl
    have halg : ∀ c : ℂ, ((algebraMap ℂ (Algebra.adjoin ℂ S) c : Algebra.adjoin ℂ S) : A) = algebraMap ℂ A c :=
      fun c => rfl
    have hsum : ∀ (t : Finset ℕ) (g : ℕ → Algebra.adjoin ℂ S),
        ((∑ i ∈ t, g i : Algebra.adjoin ℂ S) : A) = ∑ i ∈ t, (g i : A) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => rfl
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        rfl
    rw [hv, hsum, hsum, halg]
    simp only [hsm]
    exact hrel u

  let P₁ := P.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))
  let Q₁ := Q.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))
  have hP₁ : P₁.Monic := hPm.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQm.comp_X_add_C _
  have hss₁ : ∀ j, IsSS (P₁.coeff j) := isSS_coeff p hps P₁ Q₁ hP₁ hQ₁ hrelP
  have hss₂ : ∀ j, IsSS (Q₁.coeff j) := isSS_coeff p hps Q₁ P₁ hQ₁ hP₁ (by rw [mul_comm]; exact hrelP)

  have unshift : ∀ (P₁ : (Algebra.adjoin ℂ S)[X]) (c : ℂ), (∀ j, IsSS (P₁.coeff j)) →
      ∀ k, IsSS ((P₁.comp (X - C (algebraMap ℂ _ c))).coeff k) := by
    intro P₁ c h k
    rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
    refine IsSS.sum _ _ (fun j _ => ?_) fun i _ j _ => Commute.all _ _
    rw [coeff_C_mul]
    have hmap : (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c)) ^ j = ((X - C c) ^ j).map (algebraMap ℂ _) := by
      simp [Polynomial.map_pow]
    rw [hmap, coeff_map, mul_comm, ← Algebra.smul_def]
    exact (h j).smul _
  have hPP : P = P₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁)) := by
    simp only [P₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have hQQ : Q = Q₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂)) := by
    simp only [Q₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have toA : ∀ x : Algebra.adjoin ℂ S, IsSS x → IsSS (x : A) := by
    rintro x ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have := aeval_algHom_apply (Algebra.adjoin ℂ S).val x (∏ v ∈ t, (X - C v))
    rw [Subalgebra.coe_val] at this
    rw [this, ht]
    rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h1 := unshift P₁ c₁ hss₁ k
    rw [← hPP, hPc k hk] at h1
    exact toA _ h1
  · have h1 := unshift Q₁ c₂ hss₂ k
    rw [← hQQ, hQc k hk] at h1
    exact toA _ h1

end Fun

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end
