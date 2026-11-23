import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_conjTranspose {k r : ℕ} (A : Mat k r) : gN Aᴴ = gN A := by
  rw [gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]

theorem continuous_gN {k r : ℕ} : Continuous (fun g : Mat k r => gN g) := by
  have : (fun g : Mat k r => gN g) = fun g => ‖g‖ := funext gN_eq_frob
  rw [this]; exact continuous_norm

end frob

theorem gN_nonneg {k r : ℕ} (A : Mat k r) : 0 ≤ gN A := Real.sqrt_nonneg _

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

end hpk

def KH (k r : ℕ) : ℝ := gN (Hpk k r) ^ 2

theorem GV_inv_eq {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (UH_left_inv k r hg)

theorem GV_mul_inv {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 := by
  rw [GV_inv_eq hg]; exact mul_eq_one_comm.mp (UH_left_inv k r hg)

theorem gN_inv_le {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ KH k r * gN g := by
  rw [GV_inv_eq hg]
  have h0 := gN_nonneg (Hpk k r)
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) := by gcongr; exact gN_mul_le _ _
    _ = KH k r * gN g := by rw [gN_conjTranspose, KH]; ring

theorem inv_mem_G {k r : ℕ} (hCG : IsClosedSubgroup (GV k r)) {g : Mat k r} (hg : g ∈ GV k r) :
    g⁻¹ ∈ GV k r := hCG.inv_mem g hg

theorem inv_inv_G {k r : ℕ} (hCG : IsClosedSubgroup (GV k r)) {g : Mat k r} (hg : g ∈ GV k r) :
    g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv g (hCG.unit g hg)

theorem gN_le_inv {k r : ℕ} (hCG : IsClosedSubgroup (GV k r)) {g : Mat k r} (hg : g ∈ GV k r) :
    gN g ≤ KH k r * gN g⁻¹ := by
  have := gN_inv_le (inv_mem_G hCG hg)
  rwa [inv_inv_G hCG hg] at this

theorem KH_pos {k r : ℕ} (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g) : 0 < KH k r := by
  have h1 := hL 1 hCG.one_mem
  have h2 := gN_le_inv hCG hCG.one_mem
  have h3 := gN_nonneg ((1 : Mat k r)⁻¹)
  by_contra hK'
  have hK := not_lt.mp hK'
  have : KH k r * gN (1 : Mat k r)⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK h3
  linarith

theorem key_bound {A B X K a : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hX : 1 ≤ X) (hK : 0 < K) (ha : 0 ≤ a)
    (h : X ≤ K * (A * B)) :
    A ^ (-a) * B ^ (-a) ≤ K ^ (a / 2) * (A ^ (-(a / 2)) * X ^ (-(a / 2))) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hX0 : 0 < X := by linarith
  have eA : A ^ (-a) = A ^ (-(a / 2)) * A ^ (-(a / 2)) := by rw [← Real.rpow_add hA0]; ring_nf
  have eB : B ^ (-a) = B ^ (-(a / 2)) * B ^ (-(a / 2)) := by rw [← Real.rpow_add hB0]; ring_nf
  have eAB : (A * B) ^ (-(a / 2)) = A ^ (-(a / 2)) * B ^ (-(a / 2)) := Real.mul_rpow hA0.le hB0.le
  have h1 : B ^ (-(a / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hB (by linarith)
  have h2 : (A * B) ^ (-(a / 2)) ≤ (X / K) ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hX0 hK) (by rw [div_le_iff₀ hK]; linarith) (by linarith)
  have h3 : (X / K) ^ (-(a / 2)) = K ^ (a / 2) * X ^ (-(a / 2)) := by
    rw [Real.div_rpow hX0.le hK.le, Real.rpow_neg hK.le, div_inv_eq_mul, mul_comm]
  have hpA : 0 ≤ A ^ (-(a / 2)) := Real.rpow_nonneg hA0.le _
  have hpB : 0 ≤ B ^ (-(a / 2)) := Real.rpow_nonneg hB0.le _
  calc A ^ (-a) * B ^ (-a) = A ^ (-(a / 2)) * (A * B) ^ (-(a / 2)) * B ^ (-(a / 2)) := by
        rw [eA, eB, eAB]; ring
    _ ≤ A ^ (-(a / 2)) * (A * B) ^ (-(a / 2)) * 1 := by
        gcongr
    _ ≤ A ^ (-(a / 2)) * (X / K) ^ (-(a / 2)) := by rw [mul_one]; gcongr
    _ = K ^ (a / 2) * (A ^ (-(a / 2)) * X ^ (-(a / 2))) := by rw [h3]; ring

theorem AB_le_half (k r : ℕ) {a : ℝ} (ha : aM k r ≤ a) : AB k r ≤ a / 2 := by
  have hn : (1 : ℝ) ≤ nR k r := by
    simp only [nR]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have e : nR k r = 2 * (r : ℝ) + k + 1 := by simp [nR]
  have h1 : AB k r ≤ 2 * nR k r ^ 2 := by
    simp only [AB]; rw [e]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h2 : 2 * nR k r ^ 2 ≤ 2 * nR k r ^ 3 := by
    have : nR k r ^ 2 ≤ nR k r ^ 3 := by
      rw [pow_succ]; nlinarith [sq_nonneg (nR k r)]
    linarith
  simp only [aM] at ha
  linarith

open ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

section rep

variable {m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rep_inv_eq_adjoint {U : Set (Matrix (Fin m) (Fin m) ℂ)} {ρ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}
    (hrep : IsCRepOn U ρ) (hiso : ∀ g ∈ U, ∀ v, ‖ρ g v‖ = ‖v‖) {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ U) (hai : a⁻¹ ∈ U) (hmul : a * a⁻¹ = 1) :
    ρ a⁻¹ = ContinuousLinearMap.adjoint (ρ a) := by
  have h1 : ContinuousLinearMap.adjoint (ρ a) ∘L ρ a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (hiso a ha)
  have h2 : ρ a ∘L ρ a⁻¹ = 1 := by rw [← hrep.2 a ha _ hai, hmul, hrep.1]
  ext v
  have e1 := congrArg (fun T => T (ρ a⁻¹ v)) h1
  have e2 := congrArg (fun T => T v) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [← e1, e2]

theorem opNorm_le_one_of_iso {T : H →L[ℂ] H} (h : ∀ v, ‖T v‖ = ‖v‖) : ‖T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [h, one_mul]

end rep

variable {k r : ℕ}

theorem sig_inv (X : SigData k r) (hCG : IsClosedSubgroup (GV k r)) {x : Mat k r} (hx : x ∈ GV k r) :
    X.σ x⁻¹ = ContinuousLinearMap.adjoint (X.σ x) :=
  rep_inv_eq_adjoint X.rep.1 X.rep.2.1 hx (inv_mem_G hCG hx) (GV_mul_inv hx)

theorem rpow_inv_le {A B K a : ℝ} (hA : 0 < A) (hK : 0 < K) (ha : 0 ≤ a) (h : A ≤ K * B) :
    B ^ (-a) ≤ K ^ a * A ^ (-a) := by
  have hAK : 0 < A / K := div_pos hA hK
  have h1 : B ^ (-a) ≤ (A / K) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hAK (by rw [div_le_iff₀ hK]; linarith) (by linarith)
  rwa [Real.div_rpow hA.le hK.le, Real.rpow_neg hK.le, div_inv_eq_mul, mul_comm] at h1

theorem dec_adj (X : SigData k r) (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g)
    (ha : 0 ≤ X.a) {u : X.Hs} (hu : u ∈ Vfl X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GV k r, ‖⟪u, X.σ x X.w⟫_ℂ‖ ≤ C * gN x ^ (-X.a) := by
  obtain ⟨Cu, hCu⟩ := hu
  have hK := KH_pos hCG hL
  refine ⟨max Cu 0 * KH k r ^ X.a, mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hK.le _), fun x hx => ?_⟩
  have hxi := inv_mem_G hCG hx
  have e : ⟪u, X.σ x X.w⟫_ℂ = conj (mc X u X.w x⁻¹) := by
    rw [mc, sig_inv X hCG hx, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
  rw [e, RCLike.norm_conj]
  have h1 := hCu x⁻¹ hxi
  have h2 : gN x⁻¹ ^ (-X.a) ≤ KH k r ^ X.a * gN x ^ (-X.a) :=
    rpow_inv_le (by linarith [hL x hx]) hK ha (gN_le_inv hCG hx)
  have h3 : 0 ≤ gN x⁻¹ ^ (-X.a) := Real.rpow_nonneg (gN_nonneg _) _
  calc ‖mc X u X.w x⁻¹‖ ≤ Cu * gN x⁻¹ ^ (-X.a) := h1
    _ ≤ max Cu 0 * gN x⁻¹ ^ (-X.a) := by gcongr; exact le_max_left _ _
    _ ≤ max Cu 0 * (KH k r ^ X.a * gN x ^ (-X.a)) := by gcongr
    _ = max Cu 0 * KH k r ^ X.a * gN x ^ (-X.a) := by ring

theorem schur_pt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) {d : ℝ} (hd : IsFdegG D X d) (x u : X.Hs) :
    ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪x, X.σ (Matrix.of y) X.w⟫_ℂ ∂D.μG = ⟪x, u⟫_ℂ / (d : ℂ) := by
  have h := (hd.2 X.w x X.w u).2
  have hw : ⟪X.w, X.w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, X.w_norm]; simp
  rw [hw, one_mul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mc]
  rw [mul_comm]
  congr 1
  exact (inner_conj_symm _ _).symm

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous (psi k r z c) := by
  unfold psi ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finsetSum _ fun a _ => ?_
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]; fun_prop

theorem norm_psi_le (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ ≤ 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

theorem swap_smul {Y P E : Type*} [MeasurableSpace Y] [MeasurableSpace P] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (μ : Measure Y) (ν : Measure P) [SFinite μ] [SFinite ν]
    (f : Y → ℂ) (K : Y → P → E) (hint : Integrable (fun q : Y × P => f q.1 • K q.1 q.2) (μ.prod ν)) :
    ∫ y, f y • ∫ p, K y p ∂ν ∂μ = ∫ p, ∫ y, f y • K y p ∂μ ∂ν := by
  simp_rw [← integral_smul]
  exact integral_integral_swap hint

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula
