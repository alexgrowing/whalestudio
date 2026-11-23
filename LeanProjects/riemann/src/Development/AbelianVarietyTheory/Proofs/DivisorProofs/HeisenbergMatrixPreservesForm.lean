import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipMass.Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem bar_add (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_sub (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_smul (a : AE F E) (w : Fin n → AE F E) :
    (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) := by
  funext i; simp

theorem hA_add_left (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_sub_left (v v' w : Fin n → AE F E) : hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp [hA, sub_dotProduct]

theorem hA_smul_left (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_right (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, bar_add, Matrix.mulVec_add, dotProduct_add]

theorem hA_sub_right (v w w' : Fin n → AE F E) : hA σ J v (w - w') = hA σ J v w - hA σ J v w' := by
  simp only [hA, bar_sub, Matrix.mulVec_sub, dotProduct_sub]

theorem hA_smul_right (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, bar_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hA_swap (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_invol σ hσ, incM, Matrix.map_apply, cA_inclR, hJ,
    map_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x x_1 => (cA σ) (v x) * (-(inclR (F := F) (AF F)) (J x_1 x) * w x_1))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {σ J}

theorem hA_nmat (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c - cA σ c = -hA σ J u u) (v w : Fin n → AE F E) :
    hA σ J (nmat σ J x u c *ᵥ v) (nmat σ J x u c *ᵥ w) = hA σ J v w := by
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ J hσ hJ u x, hux, map_zero, neg_zero]
  have hxw : hA σ J x w = -cA σ (hA σ J w x) := hA_swap σ J hσ hJ w x
  have huw : hA σ J u w = -cA σ (hA σ J w u) := hA_swap σ J hσ hJ w u
  rw [nmat_mulVec, nmat_mulVec]
  simp only [hA_sub_left, hA_sub_right, hA_smul_left, hA_smul_right, hA_add_left, hA_add_right, hxx, hux, hxu,
    hxw, huw]
  linear_combination (hA σ J v x * cA σ (hA σ J w x)) * hc

theorem entry_eq (T : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) :
    (Tᵀ * incM F J * T.map (cA σ)) i j = hA σ J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hs : ∀ m : Fin n, T *ᵥ Pi.single m 1 = fun k => T k m := fun m => by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hs, hs]
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem entry_J (hσ : ∀ a, σ (σ a) = a) (i j : Fin n) :
    incM F J i j = hA σ J (Pi.single i 1) (Pi.single j 1) := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, single_one_dotProduct, Matrix.mulVec_single_one]
  simp

end GlobalTheory.UnipMass.Unitary

namespace GlobalTheory.UnipMass

theorem nmat_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → AE F E) (c : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u c hxx hux hc
  ext i j
  rw [Unitary.entry_eq, Unitary.hA_nmat hσ hJ x u c hxx hux hc, ← Unitary.entry_J hσ]

end GlobalTheory.UnipMass
