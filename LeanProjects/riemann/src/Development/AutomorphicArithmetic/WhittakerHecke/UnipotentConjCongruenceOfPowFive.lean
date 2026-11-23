import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.OrderAdditiveConjugation

variable {E : Type} [Field E] [NumberField E]

private theorem oh_zero : (0 : A E) ∈ Oh E := by
  refine ⟨rfl, fun v => ?_⟩
  have h : ((0 : A E).2 v) = 0 := rfl
  rw [h, map_zero]
  exact zero_le_one

private theorem oh_add {c d : A E} (hc : c ∈ Oh E) (hd : d ∈ Oh E) : c + d ∈ Oh E := by
  refine ⟨by show c.1 + d.1 = 0; rw [hc.1, hd.1, add_zero], fun v => ?_⟩
  have h : ((c + d).2 v) = c.2 v + d.2 v := rfl
  rw [h]
  exact (Valuation.map_add_le _ (hc.2 v) (hd.2 v))

private theorem oh_neg {c : A E} (hc : c ∈ Oh E) : -c ∈ Oh E := by
  refine ⟨by show -c.1 = 0; rw [hc.1, neg_zero], fun v => ?_⟩
  have h : ((-c).2 v) = -(c.2 v) := rfl
  rw [h, Valuation.map_neg]
  exact hc.2 v

private theorem oh_nat (n : ℕ) {c : A E} (hc : c ∈ Oh E) : (n : A E) * c ∈ Oh E := by
  induction n with
  | zero => simpa using oh_zero
  | succ n ih =>
    have : ((n + 1 : ℕ) : A E) * c = (n : A E) * c + c := by push_cast; ring
    rw [this]
    exact oh_add ih hc

private theorem oh_mul_of {T c : A E} (hT : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1) (hc : c ∈ Oh E) :
    T * c ∈ Oh E := by
  refine ⟨by show T.1 * c.1 = 0; rw [hc.1, mul_zero], fun v => ?_⟩
  have h : ((T * c).2 v) = H.cp v T * c.2 v := rfl
  rw [h, map_mul]
  exact mul_le_one' (hT v) (hc.2 v)

private theorem rt_mul_nat (L : ℕ) (θ : E) :
    (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt θ := by
  have : (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = algebraMap E (A E) ((L : E) * θ) := rfl
  rw [this, map_mul, map_natCast]

private theorem nat_mul_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = (0, 1) := by
  have hq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · show (L : A ℚ).1 * 0 = 0
    exact mul_zero _
  · show (L : A ℚ).2 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    have : (L : A ℚ).2 = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ) := by
      rw [map_natCast]; rfl
    rw [this, ← map_mul, mul_inv_cancel₀ hq, map_one]

private theorem unit_mul (L : ℕ) (hL : 0 < L) {r : A E} (hr : r ∈ Oh E) :
    ((L : A E) * am E (iota L)) * r = r := by
  have h1 : (L : A E) * am E (iota L) = am E ((L : A ℚ) * iota L) := by
    rw [map_mul, map_natCast]
  rw [h1, nat_mul_iota L hL]
  refine Prod.ext ?_ ?_
  · show (am E ((0, 1) : A ℚ)).1 * r.1 = r.1
    rw [hr.1, mul_zero]
  · show (am E ((0, 1) : A ℚ)).2 * r.2 = r.2
    have : (am E ((0, 1) : A ℚ)).2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, one_mul]

private theorem conj_entry {R : Type} [CommRing R] (O : Set R) (l t : R)
    (hadd : ∀ {c d : R}, c ∈ O → d ∈ O → c + d ∈ O) (hneg : ∀ {c : R}, c ∈ O → -c ∈ O)
    (P Q W : R → R) (hP : ∀ r ∈ O, P r ∈ O) (hQ : ∀ r ∈ O, Q r ∈ O) (hW : ∀ r ∈ O, W r ∈ O)
    (eP : ∀ r ∈ O, l ^ 5 * r = l * P r) (eQ : ∀ r ∈ O, t * (l ^ 5 * r) = l * Q r)
    (eW : ∀ r ∈ O, t * (t * (l ^ 5 * r)) = l * W r)
    (K : Matrix (Fin 2) (Fin 2) R)
    (hK : ∀ i j, ∃ c ∈ O, K i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l ^ 5 * c) :
    ∀ i j, ∃ c ∈ O, (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l * c := by
  obtain ⟨c00, m00, h00⟩ := hK 0 0
  obtain ⟨c01, m01, h01⟩ := hK 0 1
  obtain ⟨c10, m10, h10⟩ := hK 1 0
  obtain ⟨c11, m11, h11⟩ := hK 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
  have q00 := eQ c00 m00
  have q10 := eQ c10 m10
  have q11 := eQ c11 m11
  have p00 := eP c00 m00
  have p01 := eP c01 m01
  have p10 := eP c10 m10
  have p11 := eP c11 m11
  have w10 := eW c10 m10
  have a00 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 = K 0 0 - t * K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a01 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 = (K 0 0 - t * K 1 0) * t + (K 0 1 - t * K 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a10 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 = K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have a11 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 = K 1 0 * t + K 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  intro i j
  fin_cases i <;> fin_cases j
  · refine ⟨P c00 + -Q c10, hadd (hP _ m00) (hneg (hQ _ m10)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 - (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = _
    rw [a00, Matrix.one_apply_eq]
    linear_combination h00 - t * h10 + p00 - q10
  · refine ⟨Q c00 + P c01 + -W c10 + -Q c11, hadd (hadd (hadd (hQ _ m00) (hP _ m01)) (hneg (hW _ m10))) (hneg (hQ _ m11)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 - (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = _
    rw [a01, Matrix.one_apply_ne (by simp)]
    linear_combination t * h00 + h01 - t * t * h10 - t * h11 + q00 + p01 - w10 - q11
  · refine ⟨P c10, hP _ m10, ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 - (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = _
    rw [a10, Matrix.one_apply_ne (by simp)]
    linear_combination h10 + p10
  · refine ⟨Q c10 + P c11, hadd (hQ _ m10) (hP _ m11), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 - (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = _
    rw [a11, Matrix.one_apply_eq]
    linear_combination t * h10 + h11 + q10 + p11

end UpperTheory.OrderAdditiveConjugation

open UpperTheory.OrderAdditiveConjugation in
theorem UpperTheory.unipotent_conj_congruence_of_pow_five :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ), 0 < L → (∀ w : H.P E, Valued.v (H.cp w (rt ((L : E) * D.θ))) ≤ 1) → ∀ κ : GL (Fin 2) (A E), CongE (L ^ 5) κ → CongE L ((nu D ((a : A ℚ) * iota L))⁻¹ * κ * nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a hL hT κ hκ
  obtain ⟨t, htd⟩ : ∃ t, t = D.mkE 0 ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  obtain ⟨ν, hνd⟩ : ∃ ν, ν = nu D ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  rw [← hνd]
  have hν : (ν : Matrix (Fin 2) (Fin 2) (A E)) = !![1, t; 0, 1] := by rw [hνd, htd]; rfl
  have hνi : ((ν⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, -t; 0, 1] := by
    rw [Matrix.coe_units_inv, hν]
    apply Matrix.inv_eq_right_inv
    simp [Matrix.one_fin_two]
  have ht : t = (a : A E) * am E (iota L) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by
    rw [htd, Dat.mkE_def, map_zero, map_mul, map_natCast, zero_add]
  obtain ⟨T, hTd⟩ : ∃ T : A E, T = UpperTheory.ConvolutionTheory.R2.rt ((L : E) * D.θ) := ⟨_, rfl⟩
  have hT' : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1 := by rw [hTd]; exact hT
  have hTe : T = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by rw [hTd, rt_mul_nat]
  have key : ∀ r ∈ Oh E, (L : A E) ^ 2 * t * r = (a : A E) * (T * r) := by
    intro r hr
    have hu := unit_mul L hL hr
    rw [ht, hTe]
    linear_combination ((a : A E) * ((L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ)) * hu
  have main := conj_entry (Oh E) (L : A E) t oh_add oh_neg
    (fun r => ((L ^ 4 : ℕ) : A E) * r)
    (fun r => ((L ^ 2 * a : ℕ) : A E) * (T * r))
    (fun r => ((a ^ 2 : ℕ) : A E) * (T * (T * r)))
    (fun r hr => oh_nat _ hr)
    (fun r hr => oh_nat _ (oh_mul_of hT' hr))
    (fun r hr => oh_nat _ (oh_mul_of hT' (oh_mul_of hT' hr)))
    (fun r _ => by push_cast; ring)
    (fun r hr => by
      have := key r hr
      push_cast
      linear_combination (L : A E) ^ 3 * this)
    (fun r hr => by
      have h1 := key r hr
      have h2 := key (T * r) (oh_mul_of hT' hr)
      push_cast
      linear_combination ((L : A E) ^ 3 * t) * h1 + ((L : A E) * (a : A E)) * h2)
  have cast5 : ∀ {x : A E} {c : A E}, x = ((L ^ 5 : ℕ) : A E) * c → x = (L : A E) ^ 5 * c := by
    intro x c h; rw [h, Nat.cast_pow]
  have hinv : (ν⁻¹ * κ * ν)⁻¹ = ν⁻¹ * κ⁻¹ * ν := by group
  intro i j
  constructor
  · obtain ⟨c, hc, e⟩ := main (κ : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).1
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, Units.val_mul, Units.val_mul, hν, hνi]
  · obtain ⟨c, hc, e⟩ := main ((κ⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).2
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, hinv, Units.val_mul, Units.val_mul, hν, hνi]
