import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA

namespace Formalism.InvariantFactorPaths.PW

open Finset

section gen

variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]

def lop (A B : Module.End K W) : Module.End K (Module.End K W) :=
  LinearMap.mulLeft K A * LinearMap.mulRight K B

theorem lop_apply (A B X : Module.End K W) : lop A B X = A * X * B := by
  simp [lop, mul_assoc]

theorem lop_pow_apply (A B X : Module.End K W) (k : ℕ) : (lop A B ^ k) X = A ^ k * X * B ^ k := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, lop_apply, pow_succ A k, pow_succ' B k]
    simp only [mul_assoc]

theorem lop_commute {A B A' B' : Module.End K W} (hA : Commute A A') (hB : Commute B B') :
    Commute (lop A B) (lop A' B') := by
  show lop A B * lop A' B' = lop A' B' * lop A B
  refine LinearMap.ext fun X => ?_
  simp only [Module.End.mul_apply, lop_apply]
  have e1 : A * (A' * X * B') * B = (A * A') * X * (B' * B) := by simp only [mul_assoc]
  have e2 : A' * (A * X * B) * B' = (A' * A) * X * (B * B') := by simp only [mul_assoc]
  rw [e1, e2, hA.eq, hB.eq]

theorem Om_eq_pow (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (q : ℕ) :
    Om E S z q = ((∑ i ∈ S, lop (E z i) (E i z)) ^ q) 1 := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih, LinearMap.sum_apply]
    simp only [lop_apply]
    rfl

theorem GlRel.commF {E : ι → ι → Module.End K W} (h : GlRel E) {z i j : ι} (hi : i ≠ z) (hj : j ≠ z) :
    Commute (E z i) (E z j) := by
  have := h z i z j
  simp only [hi, hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this

theorem GlRel.commE {E : ι → ι → Module.End K W} (h : GlRel E) {z i j : ι} (hi : i ≠ z) (hj : j ≠ z) :
    Commute (E i z) (E j z) := by
  have := h i z j z
  simp only [Ne.symm hi, Ne.symm hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this

theorem Om_insert {E : ι → ι → Module.End K W} (h : GlRel E) {S : Finset ι} {z i : ι} (hz : z ∉ insert i S)
    (hi : i ∉ S) (q : ℕ) :
    Om E (insert i S) z q =
      ∑ k ∈ range (q + 1), (q.choose k : K) • ((E z i) ^ k * Om E S z (q - k) * (E i z) ^ k) := by
  have hzi : i ≠ z := fun e => hz (e ▸ Finset.mem_insert_self _ _)
  have hcomm : Commute (lop (E z i) (E i z)) (∑ j ∈ S, lop (E z j) (E j z)) := by
    refine Commute.sum_right _ _ _ fun j hj => ?_
    have hjz : j ≠ z := fun e => hz (e ▸ Finset.mem_insert_of_mem hj)
    exact lop_commute (h.commF hzi hjz) (h.commE hzi hjz)
  rw [Om_eq_pow, Finset.sum_insert hi, hcomm.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    ← Om_eq_pow, lop_pow_apply, ← Nat.cast_smul_eq_nsmul K]

end gen

section padic

variable {p : ℕ} [Fact p.Prime]

theorem norm_pow_p_le_one (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

theorem norm_pow_log_div_choose {n k N : ℕ} (hk : k ≤ n) (hn : n ≤ N) :
    ‖(p : ℚ_[p]) ^ (Nat.log p N) / (n.choose k : ℚ_[p])‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hv : (n.choose k).factorization p ≤ Nat.log p N :=
    Nat.factorization_choose_le_log.trans (Nat.log_mono_right hn)
  have hdecomp : ((n.choose k : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ ((n.choose k).factorization p) *
      ((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hr : ‖((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_ordCompl hp hC))
  rw [hdecomp, norm_div, norm_mul, hr, mul_one, Padic.norm_p_pow, Padic.norm_p_pow,
    div_le_one (zpow_pos (by exact_mod_cast hp.pos) _)]
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.one_lt.le) (by omega)

variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]

theorem Om_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) (z : ι) (N : ℕ) (S : Finset ι) : z ∉ S → ∀ c q : ℕ, q + c ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (S.card * Nat.log p N) *
        ((c.factorial : ℚ_[p]) / (((q + c).factorial : ℚ_[p]) * (q.factorial : ℚ_[p])))) • Om E S z q u ∈ M := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ c q _ u hu
    cases q with
    | zero => simpa [Om, Nat.factorial_ne_zero] using hu
    | succ q => simpa [Om] using M.zero_mem
  | insert i S hi ih =>
    intro hz c q hqc u hu
    have hzi : z ≠ i := fun e => hz (e ▸ Finset.mem_insert_self _ _)
    have hzS : z ∉ S := fun e => hz (Finset.mem_insert_of_mem e)
    rw [Om_insert hE hz hi q, LinearMap.sum_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hu' : ((k.factorial : ℚ_[p]))⁻¹ • ((E i z) ^ k) u ∈ M := hD i z (Ne.symm hzi) k u hu
    have hY := ih hzS (c + k) (q - k) (by omega) _ hu'
    have hDY := hD z i hzi k _ hY
    have hnorm := norm_pow_log_div_choose (p := p) (n := c + k) (k := k) (N := N) (by omega)
      (by omega)
    have key := hZ _ hnorm _ hDY
    convert key using 1
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    congr 1
    have hqk : q - k + (c + k) = q + c := by omega
    rw [hqk, Finset.card_insert_of_notMem hi, Nat.cast_choose ℚ_[p] hkq,
      Nat.cast_choose ℚ_[p] (Nat.le_add_left k c), Nat.add_sub_cancel]
    have h1 : (c.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((q - k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : ((q + c).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : (q.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h6 : ((c + k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring

theorem Pstep_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) {z : ι} {S : Finset ι} (hz : z ∉ S) (l : ℕ) {u : W} (hu : u ∈ M) :
    ((p : ℚ_[p]) ^ (S.card * Nat.log p (l + S.card))) • Pstep E S z l u ∈ M := by
  unfold Pstep
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun q hq => ?_
  have hql : q ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h := Om_int hE hZ hD z (l + S.card) S hz S.card q (by omega) u hu
  have h2 := hZ ((-1 : ℚ_[p]) ^ q) (by simp) _ h
  convert h2 using 1
  simp only [LinearMap.smul_apply, smul_smul]
  congr 1
  ring

end padic

theorem invariant_integral_holds : InvInt := by
  intro p _ W ι _ _ _ E hE M hZ hD l L hL u hu
  have up : ∀ (a b : ℕ) (x : W), a ≤ b → (p : ℚ_[p]) ^ a • x ∈ M → (p : ℚ_[p]) ^ b • x ∈ M := by
    intro a b x hab hx
    have := hZ _ (norm_pow_p_le_one (p := p) (b - a)) _ hx
    rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hab] at this
  have main : ∀ (L : List ι), L.Nodup → ∀ N, l + L.length - 1 ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p N)) • InvOp E l L u ∈ M := by
    intro L
    induction L with
    | nil =>
      intro _ N _ u hu
      simpa [InvOp] using hu
    | cons z L ih =>
      intro hnd N hN u hu
      rw [List.nodup_cons] at hnd
      obtain ⟨hzL, hnd⟩ := hnd
      simp only [List.length_cons] at hN
      have hv := ih hnd N (by omega) u hu
      have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
      have hz : z ∉ L.toFinset := by simpa using hzL
      have hP := Pstep_int hE hZ hD hz l hv
      rw [hcard] at hP
      have hP' := up _ (L.length * Nat.log p N) _
        (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))) hP
      convert hP' using 1
      rw [InvOp, Module.End.mul_apply, map_smul, smul_smul, ← pow_add, List.length_cons,
        Nat.choose_succ_succ, Nat.choose_one_right]
      congr 2
      ring
  exact main L hL (l + L.length - 1) le_rfl u hu

end Formalism.InvariantFactorPaths.PW
