import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

theorem aeval_isWH {σ τ R : Type} [CommSemiring R] (w' : σ → ℕ) (w : τ → ℕ)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : ℕ} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by
  rw [aeval_def, eval₂_eq]
  refine IsWeightedHomogeneous.sum _ _ _ (fun m hm => ?_)
  have hdeg : Finsupp.weight w' m = d := hf (mem_support_iff.mp hm)
  have hprod : IsWeightedHomogeneous w (∏ i ∈ m.support, g i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))
  have hC := (isWeightedHomogeneous_C w (coeff m f)).mul hprod
  rw [zero_add] at hC
  rw [← hdeg, Finsupp.weight_apply]
  exact hC

theorem weight_fst {M r : ℕ} (G : Fin M → ℕ) (m : Fin M × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin M × Fin r => G x.1) m = ∑ b, G b * ∑ c, m (b, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • G i.1) (fun i => zero_smul _ _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [smul_eq_mul, mul_comm]

theorem isWH_of_eq {σ R : Type} [CommSemiring R] {w : σ → ℕ} {φ : MvPolynomial σ R} {a b : ℕ}
    (h : IsWeightedHomogeneous w φ a) (e : a = b) : IsWeightedHomogeneous w φ b := by
  subst e
  exact h

theorem isWH_X_fst {M r : ℕ} {R : Type} [CommSemiring R] (g : Fin M → ℕ) (b : Fin M) (c : Fin r) :
    IsWeightedHomogeneous (fun x : Fin M × Fin r => g x.1) (X (b, c) : MvPolynomial _ R) (g b) :=
  isWeightedHomogeneous_X R _ (b, c)

theorem freezeSub_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (g : Fin (N + 1) → ℕ) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freezeSub p LL ρ x)
      (g (Fin.castSucc x.1) + g (Fin.last N)) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact IsWeightedHomogeneous.sum _ _ _ (fun c' _ => (isWH_X_fst g _ c').mul (isWH_X_fst g _ c'))
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
  · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ ρ)) (add_comm _ _)
  · rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ ?_
    · exact isWH_of_eq ((isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)) (add_comm _ _)
    · exact (isWH_X_fst g _ ρ).mul (isWH_X_fst g _ c)

theorem pol_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (G : Fin N → ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun x : Fin N × Fin r => G x.1) f (∑ b, G b * LL.deg b) := by
  intro m hm
  have hf' : (↑f.support : Set (Fin N × Fin r →₀ ℕ)) ⊆ {m | M.MultiDeg LL m} := hf
  have hms : M.MultiDeg LL m := hf' (mem_support_iff.mpr hm)
  rw [weight_fst]
  exact Finset.sum_congr rfl (fun b _ => by rw [hms b])

theorem freeze_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (g : Fin (N + 1) → ℕ) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => g y.1) (M.freeze p LL ρ n f)
      ((n - LL.total) • g (Fin.last N) + ∑ b, (g (Fin.castSucc b) + g (Fin.last N)) * LL.deg b) := by
  exact ((isWH_X_fst g (Fin.last N) ρ).pow _).mul
    (aeval_isWH (fun x => g (Fin.castSucc x.1) + g (Fin.last N)) (fun y => g y.1) (M.freezeSub p LL ρ)
      (fun x => freezeSub_isWH p LL ρ g x) (pol_isWH p LL (fun b => g (Fin.castSucc b) + g (Fin.last N)) hf))

theorem freeze_mem_pol (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (hn : LL.total ≤ n) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    M.freeze p LL ρ n f ∈ M.Pol p r (LL.snoc n) := by
  suffices hs : (↑(M.freeze p LL ρ n f).support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆
      {m | M.MultiDeg (LL.snoc n) m} from hs
  intro m hm i
  have key := freeze_isWH p LL ρ n (fun j => if j = i then 1 else 0) hf (mem_support_iff.mp hm)
  have hw : Finsupp.weight (fun y : Fin (N + 1) × Fin r => if y.1 = i then 1 else 0) m = ∑ c, m (i, c) := by
    rw [weight_fst (fun j => if j = i then 1 else 0) m]
    simp
  rw [← hw, key]
  have ht : LL.total = ∑ b, LL.deg b := rfl
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.castSucc_ne_last, if_false, if_true, zero_add, one_mul, smul_eq_mul, mul_one,
      M.Letters.snoc, Fin.lastCases_last]
    rw [← ht]
    omega
  | cast j =>
    simp only [(Fin.castSucc_ne_last _).symm, Fin.castSucc_inj, if_false, add_zero, smul_eq_mul, mul_zero,
      zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, M.Letters.snoc,
      Fin.lastCases_castSucc]

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)

theorem glAct_full_apply (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ F = ∑ i : Fin K,
      (if L.vec i then X (i, c) * pderiv (i, ρ) F else -(X (i, ρ) * pderiv (i, c) F)) := by
  unfold M.glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_pos i.isLt]
  split_ifs <;> simp

theorem glAct_full_mul (F G : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ (F * G) = F * M.glAct p L K c ρ G + G * M.glAct p L K c ρ F := by
  rw [glAct_full_apply, glAct_full_apply, glAct_full_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

theorem glAct_full_C (a : ℚ_[p]) : M.glAct p L K c ρ (C a) = 0 := by
  rw [glAct_full_apply]
  simp

theorem glAct_full_X (b : Fin K) (d : Fin r) :
    M.glAct p L K c ρ (X (b, d)) =
      if L.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by
  rw [glAct_full_apply, Finset.sum_eq_single b]
  · by_cases hv : L.vec b
    · by_cases hd : d = ρ <;> simp [hv, hd, pderiv_X, Pi.single_apply]
    · by_cases hd : d = c <;> simp [hv, hd, pderiv_X, Pi.single_apply]
  · intro i _ hi
    simp [pderiv_X, Pi.single_apply, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem glAct_full_pow (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hF : M.glAct p L K c ρ F = 0)
    (k : ℕ) : M.glAct p L K c ρ (F ^ k) = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, glAct_full_C]
  | succ k ih => rw [pow_succ, glAct_full_mul, hF, ih, mul_zero, mul_zero, add_zero]

theorem glAct_full_aeval {τ : Type} (σ : τ → MvPolynomial (Fin K × Fin r) ℚ_[p])
    (hσ : ∀ x, M.glAct p L K c ρ (σ x) = 0) (f : MvPolynomial τ ℚ_[p]) :
    M.glAct p L K c ρ (aeval σ f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, glAct_full_C]
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add, hf, hg, add_zero]
  | mul_X f x hf =>
    rw [_root_.map_mul, aeval_X, glAct_full_mul, hf, hσ x, mul_zero, mul_zero, add_zero]
end

theorem snoc_vec_castSucc {N : ℕ} (LL : M.Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [M.Letters.snoc]

theorem snoc_vec_last {N : ℕ} (LL : M.Letters N) (n : ℕ) :
    (LL.snoc n).vec (Fin.last N) = false := by
  simp [M.Letters.snoc]

theorem freeze_inv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.IsFrozenInv p LL ρ n (M.freeze p LL ρ n f) := by
  intro c hc
  have hX := glAct_full_X p (LL.snoc n) c ρ
  have hlast : M.glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [hX, snoc_vec_last]
    simp [Ne.symm hc]
  have hsub : ∀ x, M.glAct p (LL.snoc n) (N + 1) c ρ (M.freezeSub p LL ρ x) = 0 := by
    rintro ⟨i, c'⟩
    simp only [M.freezeSub]
    by_cases hv : LL.vec i
    · by_cases hc' : c' = ρ
      · rw [if_pos hv, if_pos hc', _root_.map_sum]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, if_true, Bool.false_eq_true,
          if_false, mul_ite, mul_zero, mul_neg, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
        ring
      · rw [if_pos hv, if_neg hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
    · by_cases hc' : c' = ρ
      · rw [if_neg hv, if_pos hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
      · rw [if_neg hv, if_neg hc', _root_.map_sub]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
        by_cases hcc : c' = c
        · simp only [hcc, if_true]
          ring
        · simp only [hcc, if_false, mul_zero, sub_zero]
  unfold M.freeze
  rw [glAct_full_mul, glAct_full_pow _ _ _ _ _ hlast, glAct_full_aeval _ _ _ _ _ hsub, mul_zero, mul_zero,
    add_zero]

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM.FrozenVariableLemmas

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {τ : Type}

theorem intPol_iff (F : MvPolynomial τ ℚ_[p]) :
    F ∈ M.IntPol p τ ↔ ∃ F₀ : MvPolynomial τ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by
  unfold M.IntPol
  rw [LinearMap.mem_range]
  rfl

theorem intPol_mul {F G : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (hG : G ∈ M.IntPol p τ) :
    F * G ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF hG ⊢
  obtain ⟨F₀, rfl⟩ := hF
  obtain ⟨G₀, rfl⟩ := hG
  exact ⟨F₀ * G₀, _root_.map_mul _ _ _⟩

theorem intPol_X (x : τ) : (X x : MvPolynomial τ ℚ_[p]) ∈ M.IntPol p τ := by
  rw [intPol_iff]
  exact ⟨X x, MvPolynomial.map_X _ _⟩

theorem intPol_pow {F : MvPolynomial τ ℚ_[p]} (hF : F ∈ M.IntPol p τ) (k : ℕ) :
    F ^ k ∈ M.IntPol p τ := by
  rw [intPol_iff] at hF ⊢
  obtain ⟨F₀, rfl⟩ := hF
  exact ⟨F₀ ^ k, _root_.map_pow _ _ _⟩

theorem intPol_aeval {υ : Type} (σ : υ → MvPolynomial τ ℚ_[p]) (hσ : ∀ x, σ x ∈ M.IntPol p τ)
    {f : MvPolynomial υ ℚ_[p]} (hf : f ∈ M.IntPol p υ) : aeval σ f ∈ M.IntPol p τ := by
  rw [intPol_iff] at hf
  obtain ⟨f₀, rfl⟩ := hf
  induction f₀ using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, aeval_C, MvPolynomial.algebraMap_eq, intPol_iff]
    exact ⟨C a, MvPolynomial.map_C _ _⟩
  | add f g hf hg =>
    rw [_root_.map_add, _root_.map_add]
    exact Submodule.add_mem _ hf hg
  | mul_X f x hf =>
    rw [_root_.map_mul, MvPolynomial.map_X, _root_.map_mul, aeval_X]
    exact intPol_mul p hf (hσ x)
end

theorem freezeSub_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (x : Fin N × Fin r) : M.freezeSub p LL ρ x ∈ M.IntPol p (Fin (N + 1) × Fin r) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact Submodule.sum_mem _ (fun c' _ => intPol_mul p (intPol_X p _) (intPol_X p _))
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact Submodule.sub_mem _ (intPol_mul p (intPol_X p _) (intPol_X p _))
      (intPol_mul p (intPol_X p _) (intPol_X p _))

theorem freeze_int (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.IntPol p (Fin N × Fin r)) :
    M.freeze p LL ρ n f ∈ M.IntPol p (Fin (N + 1) × Fin r) :=
  intPol_mul p (intPol_pow p (intPol_X p _) _) (intPol_aeval p _ (freezeSub_int p LL ρ) hf)

end Formalism.GM.FrozenVariableLemmas

namespace Formalism.GM

theorem extendMapsTo : M.FreezeInto := by
  intro p _ N r LL ρ n hn f hf
  exact ⟨FrozenVariableLemmas.freeze_mem_pol p LL ρ n hn hf, FrozenVariableLemmas.freeze_inv p LL ρ n f,
    fun h => FrozenVariableLemmas.freeze_int p LL ρ n h⟩

theorem extendSucc : M.FreezeStep := by
  intro p _ N r LL ρ n hn f
  unfold M.freeze
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_comm hn]

end Formalism.GM
