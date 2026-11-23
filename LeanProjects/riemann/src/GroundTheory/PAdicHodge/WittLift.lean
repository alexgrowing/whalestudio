import Mathlib
import GroundTheory.PAdicHodge.SemilinearResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WittLift

open WittVector Finset Matrix

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*}

local notation "𝕎" => WittVector p

section Perfect

variable [CommRing k] [CharP k p] [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in
theorem sMod_iff (x y : 𝕎 k) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {(p : 𝕎 k)}) ^ n • ⊤ : Submodule (𝕎 k) (𝕎 k))] ↔
      x - y ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]

theorem exists_limit (a : ℕ → 𝕎 k) (h : ∀ n, a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ n}) :
    ∃ L, ∀ n, L - a n ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  have hmono : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {(p : 𝕎 k) ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ m} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hmn) (h n)
      have := Ideal.add_mem _ ih h1
      convert this using 1
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : 𝕎 k)}) a (fun {m n} hmn => by
    rw [sMod_iff, ← neg_sub]
    exact neg_mem (hmono m n hmn))
  refine ⟨L, fun n => ?_⟩
  have := (sMod_iff _ _ _).mp (hL n)
  rw [← neg_sub]
  exact neg_mem this

theorem eq_zero_of_forall_mem (x : 𝕎 k) (h : ∀ n, x ∈ Ideal.span {(p : 𝕎 k) ^ n}) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : 𝕎 k)}) x (fun n => by
    rw [sMod_iff, sub_zero]
    exact h n)

theorem surjective_of_mod_p {ι : Type*} (T : (ι → 𝕎 k) →+ (ι → 𝕎 k))
    (hT : ∀ x, T ((p : 𝕎 k) • x) = (p : 𝕎 k) • T x)
    (hmod : ∀ z, ∃ x y, z = T x + (p : 𝕎 k) • y) : Function.Surjective T := by
  choose X Y hXY using hmod
  have hTpow : ∀ n x, T ((p : 𝕎 k) ^ n • x) = (p : 𝕎 k) ^ n • T x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [pow_succ', mul_smul, hT, ih, mul_smul]
  intro z
  let zs : ℕ → (ι → 𝕎 k) := fun n => Nat.rec z (fun _ w => Y w) n
  let s : ℕ → (ι → 𝕎 k) := fun n => ∑ j ∈ range n, (p : 𝕎 k) ^ j • X (zs j)
  have hA : ∀ n, z - T (s n) = (p : 𝕎 k) ^ n • zs n := by
    intro n
    induction n with
    | zero => simp [s, zs]
    | succ n ih =>
      have e1 : s (n + 1) = s n + (p : 𝕎 k) ^ n • X (zs n) := Finset.sum_range_succ _ _
      have e2 : zs (n + 1) = Y (zs n) := rfl
      have h' : zs n - T (X (zs n)) = (p : 𝕎 k) • Y (zs n) := by
        rw [sub_eq_iff_eq_add']
        exact hXY (zs n)
      rw [e1, map_add, hTpow, ← sub_sub, ih, ← smul_sub, h', smul_smul, ← pow_succ, e2]
  have hstep : ∀ i n, s (n + 1) i - s n i ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
    intro i n
    have e1 : s (n + 1) = s n + (p : 𝕎 k) ^ n • X (zs n) := Finset.sum_range_succ _ _
    rw [e1, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  choose L hL using fun i => exists_limit (fun n => s n i) (hstep i)
  choose u hu using fun n i => Ideal.mem_span_singleton'.mp (hL i n)
  refine ⟨L, ?_⟩
  have hLs : ∀ n, L - s n = (p : 𝕎 k) ^ n • (fun i => u n i) := by
    intro n
    funext i
    simp [← hu n i, mul_comm]
  funext i
  symm
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_mem
  intro n
  have : z - T L = (p : 𝕎 k) ^ n • (zs n - T (fun i => u n i)) := by
    rw [show L = s n + (L - s n) by abel, map_add, ← sub_sub, hA, hLs, hTpow, smul_sub]
  rw [← Pi.sub_apply, this, Pi.smul_apply, smul_eq_mul]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end Perfect

section Matrix

variable [CommRing k] [CharP k p] {ι : Type*} [Fintype ι]

noncomputable def matOp (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) :
    (ι → 𝕎 k) →+ (ι → 𝕎 k) where
  toFun x := A *ᵥ (fun i => τ (x i))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero A
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

omit [CharP k p] in
theorem matOp_apply (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) (x : ι → 𝕎 k) :
    matOp A τ x = A *ᵥ (fun i => τ (x i)) := rfl

omit [CharP k p] in
theorem matOp_p_smul (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) (x : ι → 𝕎 k) :
    matOp A τ ((p : 𝕎 k) • x) = (p : 𝕎 k) • matOp A τ x := by
  rw [matOp_apply, matOp_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_natCast]

def red (x : ι → 𝕎 k) : ι → k := fun i => (x i).coeff 0

variable {e : ℕ}

noncomputable def resOp (A : Matrix ι ι (𝕎 k)) (e : ℕ) : (ι → k) →+ (ι → k) where
  toFun x := A.map (fun a => a.coeff 0) *ᵥ (fun i => x i ^ p ^ e)
  map_zero' := by
    rw [← Matrix.mulVec_zero (A.map (fun a => a.coeff 0))]
    congr 1
    funext i
    simp [hp.out.ne_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [add_pow_char_pow]

theorem resOp_apply (A : Matrix ι ι (𝕎 k)) (x : ι → k) :
    resOp A e x = A.map (fun a => a.coeff 0) *ᵥ (fun i => x i ^ p ^ e) := rfl

theorem resOp_smul (A : Matrix ι ι (𝕎 k)) (c : k) (x : ι → k) :
    resOp A e (c • x) = c ^ p ^ e • resOp A e x := by
  rw [resOp_apply, resOp_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [mul_pow]

theorem red_matOp (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (x : ι → 𝕎 k) :
    red (matOp A τ x) = resOp A e (red x) := by
  funext i
  simp only [red, matOp_apply, resOp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [← WittVector.constantCoeff_apply, map_sum]
  simp [WittVector.mul_coeff_zero, hτ]

theorem red_iterate_matOp (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (x : ι → 𝕎 k) (N : ℕ) :
    red ((⇑(matOp A τ))^[N] x) = (⇑(resOp A e))^[N] (red x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', red_matOp A hτ, ih]

omit [CharP k p] [Fintype ι] in
theorem red_sub (x y : ι → 𝕎 k) : red (x - y) = red x - red y := by
  funext i
  simp [red, ← WittVector.constantCoeff_apply]

omit [Fintype ι] in
theorem red_p_smul (x : ι → 𝕎 k) : red ((p : 𝕎 k) • x) = 0 := by
  funext i
  simp [red, ← WittVector.constantCoeff_apply]

variable [PerfectRing k p]

omit [Fintype ι] in
theorem exists_eq_p_smul_of_red (x : ι → 𝕎 k) (h : red x = 0) : ∃ y, x = (p : 𝕎 k) • y := by
  have : ∀ i, ∃ y, x i = (p : 𝕎 k) * y := fun i => by
    have hi : (x i).coeff 0 = 0 := congrFun h i
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp
      ((mem_span_p_iff_coeff_zero_eq_zero (x i)).mpr hi)
    exact ⟨y, by rw [← hy, mul_comm]⟩
  choose y hy using this
  exact ⟨y, funext fun i => by simp [hy i]⟩

omit [CharP k p] [Fintype ι] [PerfectRing k p] in
theorem exists_lift (x : ι → k) : ∃ y : ι → 𝕎 k, red y = x :=
  ⟨fun i => teichmuller p (x i), funext fun _ => rfl⟩

end Matrix

section AlgClosed

variable [Field k] [IsAlgClosed k] [CharP k p] {ι : Type*} [Fintype ι] {e : ℕ}

theorem matOp_sub_surjective (he : 0 < e) (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (z : ι → 𝕎 k) :
    ∃ x, matOp A τ x - x = z := by
  obtain ⟨x, hx⟩ := surjective_of_mod_p (matOp A τ - AddMonoidHom.id _)
    (fun x => by simp [matOp_p_smul, smul_sub]) (fun z => by
      obtain ⟨xb, hxb⟩ := SemilinearResidue.exists_sub_eq (p := p) he (resOp_smul (p := p) (e := e) A) (red z)
      obtain ⟨x, rfl⟩ := exists_lift (p := p) xb
      obtain ⟨y, hy⟩ := exists_eq_p_smul_of_red (z - (matOp A τ x - x)) (by
        rw [red_sub, red_sub, red_matOp A hτ, hxb, sub_self])
      exact ⟨x, y, by simp [← hy]⟩) z
  exact ⟨x, by simpa using hx⟩

theorem exists_fixed (he : 0 < e) (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (x₀ : ι → 𝕎 k)
    (hx₀ : ∀ N, red ((⇑(matOp A τ))^[N] x₀) ≠ 0) :
    ∃ y, matOp A τ y = y ∧ red y ≠ 0 := by
  obtain ⟨yb, hyb0, hyb⟩ := SemilinearResidue.exists_fixed_ne_zero (p := p) he (resOp_smul (p := p) (e := e) A) (red x₀)
    (fun N => by rw [← red_iterate_matOp A hτ]; exact hx₀ N)
  obtain ⟨y₀, rfl⟩ := exists_lift (p := p) yb
  obtain ⟨w, hw⟩ := exists_eq_p_smul_of_red (matOp A τ y₀ - y₀) (by
    rw [red_sub, red_matOp A hτ, hyb, sub_self])
  obtain ⟨x, hx⟩ := matOp_sub_surjective he A hτ w
  refine ⟨y₀ - (p : 𝕎 k) • x, ?_, ?_⟩
  · rw [map_sub, matOp_p_smul, sub_eq_sub_iff_sub_eq_sub, hw, ← smul_sub, hx]
  · rw [red_sub, red_p_smul, sub_zero]
    exact hyb0

end AlgClosed

end WittLift

end GroundTheory.PAdicHodge
