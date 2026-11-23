import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.Frame

variable {g : ℕ}

theorem hf_sum_left {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ i, z i • x i) w = ∑ i, z i * hf Hm (x i) w := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem hf_sum_right {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * hf Hm w (x i) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_sum_left {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ i, z i • x i) w = ∑ i, z i * beta d Hm (x i) w := by
  simp only [beta, hf_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem beta_sum_right {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * beta d Hm w (x i) := by
  simp only [beta, hf_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section
variable {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → Fin g → ℂ} {a : Fin g → ℕ}

theorem beta_coord (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z : Fin g → ℂ) (j : Fin g) :
    beta d Hm (∑ i, z i • x i) (x j) = z j * a j := by
  simp [beta_sum_left, hx]

theorem beta_frame (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * (z i * conj (w i)) := by
  rw [beta_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring

theorem hf_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 d (z i) (w i) := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt d ≠ 0 := by positivity
    exact_mod_cast this
  have h := beta_frame hx z w
  have e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) =
      ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) := by
    rw [beta]; push_cast; field_simp
  rw [e, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem expand (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, 0 < a i)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ x
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective L := by
    intro z w h
    funext j
    have h1 := beta_coord hx z j
    have h2 := beta_coord hx w j
    rw [← hL] at h1 h2
    rw [h, h2] at h1
    exact (mul_right_cancel₀ (ha' j) h1).symm
  obtain ⟨z, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]

theorem opU_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opU Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 d (t i) (f j i) (z i) ^ a i := by
  have e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

theorem opW_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opW d Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 d (t i) (f j i) (z i) ^ a i := by
  have e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) =
      ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ) := by
    rw [beta_frame hx]
    simp only [Complex.mul_conj]
    have : (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]
  rw [mul_left_comm]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

end

theorem jetV_frame (x : Fin g → Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) :
    jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L := by
    funext z; simp [hL]
  rw [e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]
  simp only [hL]

theorem coord : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys :=
  fun _ _ x _ hd hx ha =>
    ⟨expand hx ha, hf_frame hd hx,
      fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩,
      jetV_frame x⟩

end GlobalTheory.MomOne.Frame
