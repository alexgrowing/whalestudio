import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

noncomputable section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem hJ_fsum_r {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) : hJ ε x (∑ i, g i • y i) = ∑ i, g i * hJ ε x (y i) := by
  classical
  have key : ∀ s : Finset ι, hJ ε x (∑ i ∈ s, g i • y i) = ∑ i ∈ s, g i * hJ ε x (y i) := by
    intro s
    refine Finset.induction_on s (by simp [hJ]) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_r, hJ_smul_r, ih]
  exact key Finset.univ

theorem hJ_eq_dot (x y : Fin n → ℂ) : hJ ε x y = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := rfl

theorem dual_exists {m : ℕ} (V : Fin m → Fin n → ℂ) (hV : LinearIndependent ℂ V) :
    ∃ q : Fin m → Fin n → ℂ, ∀ i j, hJ ε (V i) (q j) = if i = j then 1 else 0 := by
  classical
  have key : ∀ j : Fin m, ∃ w : Fin n → ℂ, ∀ i, ∑ k, V i k * w k = if i = j then 1 else 0 := by
    intro j
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply j).comp hV.repr)
    refine ⟨fun k => g (fun l => if k = l then 1 else 0), fun i => ?_⟩
    have h1 := LinearMap.congr_fun hg ⟨V i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h1
    rw [hV.repr_eq_single i _ rfl, Finsupp.single_apply] at h1
    rw [← h1]
    conv_rhs => rw [pi_eq_sum_univ (V i), map_sum]
    simp only [map_smul, smul_eq_mul]
  choose w hw using key
  refine ⟨fun j => Formalism.REAL.Jm ε *ᵥ star (w j), fun i j => ?_⟩
  rw [hJ_eq_dot, Matrix.mulVec_mulVec, Jm_mul_self, Matrix.one_mulVec]
  have h := hw j i
  calc star (V i) ⬝ᵥ star (w j) = conj (∑ k, V i k * w j k) := by
        simp only [dotProduct, Pi.star_apply, map_sum, map_mul]
        rfl
    _ = _ := by rw [h]; split_ifs <;> simp

end Lin

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_fsum_l {ι : Type*} [Fintype ι] (g : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i, g i • x i) y = ∑ i, conj (g i) * hJ ε (x i) y := by
  classical
  have key : ∀ s : Finset ι, hJ ε (∑ i ∈ s, g i • x i) y = ∑ i ∈ s, conj (g i) * hJ ε (x i) y := by
    intro s
    refine Finset.induction_on s (by simp [hJ]) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_l, hJ_smul_l, ih]
  exact key Finset.univ

theorem not_mem_span_of_orth (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzz : hJ ε z z ≠ 0) : z ∉ Submodule.span ℂ (Set.range e) := by
  intro hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  apply hzz
  have h1 : hJ ε z z = hJ ε (∑ a, c a • e a) z := by rw [hc]
  rw [h1, hJ_fsum_l]
  simp [hez]

theorem partner_exists (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (he : LinearIndependent ℂ e)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hzz : hJ ε z z ≠ 0) :
    ∃ p : Fin r → Fin n → ℂ, (∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0) ∧
      (∀ a b, hJ ε (p a) (p b) = 0) ∧ ∀ b, hJ ε z (p b) = 0 := by
  classical
  have hz : z ∉ Submodule.span ℂ (Set.range e) := not_mem_span_of_orth ε e z hez hzz
  have hV : LinearIndependent ℂ (Fin.snoc e z : Fin (r + 1) → Fin n → ℂ) :=
    linearIndependent_fin_snoc.2 ⟨he, hz⟩
  obtain ⟨q, hq⟩ := dual_exists ε (Fin.snoc e z : Fin (r + 1) → Fin n → ℂ) hV
  have hEq : ∀ a b, hJ ε (e a) (q (Fin.castSucc b)) = if a = b then 1 else 0 := by
    intro a b
    have h := hq (Fin.castSucc a) (Fin.castSucc b)
    rw [Fin.snoc_castSucc] at h
    rw [h]
    simp [Fin.castSucc_inj]
  have hZq : ∀ b, hJ ε z (q (Fin.castSucc b)) = 0 := by
    intro b
    have h := hq (Fin.last r) (Fin.castSucc b)
    rw [Fin.snoc_last] at h
    rw [h, if_neg (Fin.castSucc_lt_last b).ne']
  have hqE : ∀ a d, hJ ε (q (Fin.castSucc a)) (e d) = if d = a then 1 else 0 := by
    intro a d
    rw [hJ_cj ε (q (Fin.castSucc a)) (e d), hEq]
    split_ifs <;> simp
  have hEz : ∀ c, hJ ε z (e c) = 0 := fun c => hJ_zero_of_cj ε (hez c)
  have hA : ∀ a b, hJ ε (q (Fin.castSucc a))
      (∑ d, (-(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc d)) (q (Fin.castSucc b))) • e d) =
      -(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc a)) (q (Fin.castSucc b)) := by
    intro a b
    rw [hJ_fsum_r]
    simp only [hqE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hB : ∀ a b, hJ ε (∑ c, (-(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc c)) (q (Fin.castSucc a))) • e c)
      (q (Fin.castSucc b)) = -(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc a)) (q (Fin.castSucc b)) := by
    intro a b
    rw [hJ_fsum_l]
    simp only [hEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [map_mul, hJ_cj ε (q (Fin.castSucc a)) (q (Fin.castSucc b))]
    have hc2 : conj (-(1 / 2 : ℂ)) = -(1 / 2) := by
      rw [map_neg, map_div₀, map_one, map_ofNat]
    rw [hc2]
  have hC : ∀ a b, hJ ε (∑ c, (-(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc c)) (q (Fin.castSucc a))) • e c)
      (∑ d, (-(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc d)) (q (Fin.castSucc b))) • e d) = 0 := by
    intro a b
    rw [hJ_fsum_l]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hJ_fsum_r]
    simp [hee]
  refine ⟨fun b => q (Fin.castSucc b) +
      ∑ c, (-(1 / 2 : ℂ) * hJ ε (q (Fin.castSucc c)) (q (Fin.castSucc b))) • e c, ?_, ?_, ?_⟩
  · intro a b
    dsimp only
    rw [hJ_add_r, hJ_fsum_r, hEq]
    simp [hee]
  · intro a b
    dsimp only
    rw [hJ_add_l, hJ_add_r, hJ_add_r, hA, hB, hC]
    ring
  · intro b
    dsimp only
    rw [hJ_add_r, hJ_fsum_r, hZq]
    simp [hEz]

theorem scalar_frame_w_zero_exists (k : ℕ) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℝ)
    (hdim : n = 2 * r + 1 + k) (hk : 1 ≤ k) (hsig : (Finset.univ.filter fun i => ε i = false).card = r + 1)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0)
    (hpp : ∀ a b, hJ ε (p a) (p b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hzp : ∀ b, hJ ε z (p b) = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hT : 0 < T) :
    ∃ w, hJ ε w w = 1 ∧ (∀ a, hJ ε (e a) w = 0) ∧ (∀ a, hJ ε (p a) w = 0) ∧ hJ ε z w = 0 := by
  classical
  have hsl : ∀ x x' y : Fin n → ℂ, hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
    intro x x' y
    rw [sub_eq_add_neg, ← neg_one_smul ℂ x', hJ_add_l, hJ_smul_l, map_neg, map_one]
    ring
  have hsr : ∀ x y y' : Fin n → ℂ, hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
    intro x y y'
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y', hJ_add_r, hJ_smul_r]
    ring
  have hpe : ∀ a b, hJ ε (p a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_cj ε (p a) (e b), hep]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero]
  have hpz : ∀ a, hJ ε (p a) z = 0 := fun a => hJ_zero_of_cj ε (hzp a)
  have hze : ∀ a, hJ ε z (e a) = 0 := fun a => hJ_zero_of_cj ε (hez a)
  let Ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) × (Fin r → ℂ) × ℂ :=
    { toFun := fun y => (fun a => hJ ε (e a) y, fun a => hJ ε (p a) y, hJ ε z y)
      map_add' := fun y y' => by
        simp only [hJ_add_r]
        rfl
      map_smul' := fun c y => by
        simp only [hJ_smul_r, RingHom.id_apply]
        rfl }
  have hker : LinearMap.ker Ψ ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  obtain ⟨ξ, hξk, hξ0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hΨ : Ψ ξ = 0 := hξk
  have hξe : ∀ a, hJ ε (e a) ξ = 0 := fun a => congrFun (congrArg Prod.fst hΨ) a
  have hξp : ∀ a, hJ ε (p a) ξ = 0 := fun a => congrFun (congrArg (fun t => t.2.1) hΨ) a
  have hξz : hJ ε z ξ = 0 := congrArg (fun t => t.2.2) hΨ
  let nv : Fin (r + 1) → Fin n → ℂ := fun j =>
    if h : (j : ℕ) < r then e ⟨j, h⟩ - p ⟨j, h⟩ else z
  have horth : ∀ j k, j ≠ k → hJ ε (nv j) (nv k) = 0 := by
    intro j k hjk
    simp only [nv]
    split_ifs with h1 h2 h2
    · have hab : (⟨j, h1⟩ : Fin r) ≠ ⟨k, h2⟩ := fun h => hjk (Fin.ext (by simpa using congrArg Fin.val h))
      rw [hsl, hsr, hsr, hee, hep, hpe, hpp]
      simp [hab]
    · rw [hsl, hez, hpz, sub_zero]
    · rw [hsr, hze, hzp, sub_zero]
    · exact absurd (Fin.ext (by omega)) hjk
  have hneg : ∀ j, (hJ ε (nv j) (nv j)).re < 0 := by
    intro j
    simp only [nv]
    split_ifs with h1
    · rw [hsl, hsr, hsr, hee, hep, hpe, hpp]
      norm_num
    · rw [hzz, Complex.neg_re, Complex.ofReal_re]
      linarith
  have hnvξ : ∀ j, hJ ε (nv j) ξ = 0 := by
    intro j
    simp only [nv]
    split_ifs with h1
    · rw [hsl, hξe, hξp, sub_zero]
    · exact hξz
  have hpos : 0 < (hJ ε ξ ξ).re := by
    by_contra hle
    push_neg at hle
    have h := Formalism.L2.SG.PoincareInHH.Cut.card_le_of_orth' ε (r + 1) nv ξ horth hneg hnvξ hle hξ0
    rw [hsig] at h
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, hJ ε ξ ξ = ρ := ⟨_, (Complex.conj_eq_iff_re.1 (hJ_self_conj ε ξ)).symm⟩
  have hρ0 : 0 < ρ := by rw [hρ, Complex.ofReal_re] at hpos; exact hpos
  refine ⟨(((Real.sqrt ρ)⁻¹ : ℝ) : ℂ) • ξ, ?_, ?_, ?_, ?_⟩
  · rw [hJ_smul_l, hJ_smul_r, Complex.conj_ofReal, hρ, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_eq_one, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hρ0.le, inv_mul_cancel₀ hρ0.ne']
  · intro a
    rw [hJ_smul_r, hξe a, mul_zero]
  · intro a
    rw [hJ_smul_r, hξp a, mul_zero]
  · rw [hJ_smul_r, hξz, mul_zero]

end Frame

section Tvm

variable {n : ℕ} (ε : Fin n → Bool) {ι : Type} [Fintype ι] [DecidableEq ι]

def tvmL (u : ι → Fin n → ℂ) (ξ : ι → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := v - ∑ b, (ξ b * hJ ε (u b) v) • u b
  map_add' v w := by
    simp only [hJ_add_right, mul_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' a v := by
    rw [RingHom.id_apply, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJ_smul_right, smul_smul]
    congr 1
    ring

def tvm (u : ι → Fin n → ℂ) (ξ : ι → ℂ) : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (tvmL ε u ξ)

theorem tvm_apply (u : ι → Fin n → ℂ) (ξ : ι → ℂ) (v : Fin n → ℂ) :
    tvm ε u ξ *ᵥ v = v - ∑ b, (ξ b * hJ ε (u b) v) • u b := by
  show LinearMap.toMatrix' (tvmL ε u ξ) *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem tvm_fix (u : ι → Fin n → ℂ) (ξ : ι → ℂ) {v : Fin n → ℂ} (hv : ∀ b, hJ ε (u b) v = 0) :
    tvm ε u ξ *ᵥ v = v := by
  rw [tvm_apply]
  simp [hv]

theorem tvm_one (u : ι → Fin n → ℂ) (ξ : ι → ℂ) (j : ι) {v : Fin n → ℂ} (hj : ξ j * hJ ε (u j) v = 1)
    (hv : ∀ b, b ≠ j → hJ ε (u b) v = 0) : tvm ε u ξ *ᵥ v = v - u j := by
  rw [tvm_apply, Finset.sum_eq_single j, hj, one_smul]
  · intro b _ hb
    rw [hv b hb, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem tvm_isIsom (u : ι → Fin n → ℂ) (ξ : ι → ℂ) (horth : ∀ a b, a ≠ b → hJ ε (u a) (u b) = 0)
    (hξ : ∀ b, ξ b + conj (ξ b) = ξ b * conj (ξ b) * hJ ε (u b) (u b)) : IsIsom ε (tvm ε u ξ) := by
  intro x y
  have hsl : ∀ a a' b : Fin n → ℂ, hJ ε (a - a') b = hJ ε a b - hJ ε a' b := by
    intro a a' b
    rw [sub_eq_add_neg, ← neg_one_smul ℂ a', hJ_add_l, hJ_smul_l, map_neg, map_one]
    ring
  have hsr : ∀ a b b' : Fin n → ℂ, hJ ε a (b - b') = hJ ε a b - hJ ε a b' := by
    intro a b b'
    rw [sub_eq_add_neg, ← neg_one_smul ℂ b', hJ_add_r, hJ_smul_r]
    ring
  have h1 : hJ ε x (∑ b, (ξ b * hJ ε (u b) y) • u b) =
      ∑ b, (ξ b * hJ ε (u b) y) * conj (hJ ε (u b) x) := by
    rw [hJ_fsum_r]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJ_cj ε x (u b)]
  have h2 : hJ ε (∑ a, (ξ a * hJ ε (u a) x) • u a) y =
      ∑ a, conj (ξ a * hJ ε (u a) x) * hJ ε (u a) y := hJ_fsum_l ε _ _ _
  have h12 : hJ ε (∑ a, (ξ a * hJ ε (u a) x) • u a) (∑ b, (ξ b * hJ ε (u b) y) • u b) =
      ∑ a, conj (ξ a * hJ ε (u a) x) * ((ξ a * hJ ε (u a) y) * hJ ε (u a) (u a)) := by
    rw [hJ_fsum_l]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hJ_fsum_r, Finset.sum_eq_single a]
    · intro b _ hb
      rw [horth a b (Ne.symm hb), mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [tvm_apply, tvm_apply, hsl, hsr, hsr, h1, h2, h12]
  have hz : ∑ b, (ξ b * hJ ε (u b) y) * conj (hJ ε (u b) x) +
      ∑ a, conj (ξ a * hJ ε (u a) x) * hJ ε (u a) y -
      ∑ a, conj (ξ a * hJ ε (u a) x) * ((ξ a * hJ ε (u a) y) * hJ ε (u a) (u a)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [map_mul]
    linear_combination (conj (hJ ε (u b) x) * hJ ε (u b) y) * hξ b
  linear_combination -hz

end Tvm

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
