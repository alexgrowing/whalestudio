import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [Zero R]

def hAd (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → AE F E) : AE F E :=
  z ⬝ᵥ (incM F J *ᵥ fun i => cA σ (y i))

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact congrArg (a ⊗ₜ[F] ·) (hσ e)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (F E) in

def vecAt (m : ℕ) (ev : AF F → R) : AddSubgroup (Fin m → AE F E) where
  carrier := {w | At ev w}
  zero_mem' := fun u _ => smul_zero u
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  neg_mem' := fun {a} ha u hu => by rw [smul_neg, ha u hu, neg_zero]

def skewAt (σ : E →ₐ[F] E) (ev : AF F → R) : AddSubgroup (AE F E) where
  carrier := {c | At ev c ∧ cA σ c = -c}
  zero_mem' := ⟨fun u _ => smul_zero u, by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero], by rw [map_add, ha.2, hb.2, neg_add]⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by rw [map_neg, ha.2]⟩

def vecAtSmul {m : ℕ} {ev : AF F → R} (s : AE F E) : vecAt F E m ev →+ vecAt F E m ev where
  toFun w := ⟨s • w.1, fun u hu => by rw [smul_comm, w.2 u hu, smul_zero]⟩
  map_zero' := Subtype.ext (smul_zero s)
  map_add' a b := Subtype.ext (smul_add s a.1 b.1)

def normSmul {σ : E →ₐ[F] E} {ev : AF F → R} (hσ : ∀ e, σ (σ e) = e) (s : AE F E) : skewAt σ ev →+ skewAt σ ev where
  toFun c := ⟨(s * cA σ s) * c.1, fun u hu => by rw [← mul_smul_comm, c.2.1 u hu, mul_zero], by
    rw [map_mul, map_mul, cA_cA hσ, c.2.2]; ring⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' a b := Subtype.ext (mul_add _ a.1 b.1)

variable (σ) in

def stabAtPair {n : ℕ} (X : Spc F E n) (ev : AF F → R) (x y : Fin n → E) : Subgroup (stabAt σ X ev x) where
  carrier := {q | mat q.1.1 *ᵥ incV F y = incV F y}
  one_mem' := by
    show mat (1 : UA σ X.J) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh
    show mat (g.1.1 * h.1.1) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec]
    rw [show mat h.1.1 *ᵥ incV F y = incV F y from hh]
    exact hg
  inv_mem' := by
    intro g hg
    show mat g.1.1⁻¹ *ᵥ incV F y = incV F y
    have hg' : mat g.1.1 *ᵥ incV F y = incV F y := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]

variable (σ) in

def nMat {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (w : Fin m → AE F E) (c : AE F E) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + Matrix.vecMulVec (incM F ι *ᵥ w + c • incV F x) (incM F J *ᵥ fun i => cA σ (incV F x i)) -
    Matrix.vecMulVec (incV F x) (incM F J *ᵥ fun i => cA σ ((incM F ι *ᵥ w) i))

theorem nMat_mulVec (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (w : Fin m → AE F E) (c : AE F E) (z : Fin n → AE F E) :
    nMat σ J x ι w c *ᵥ z = z + hAd σ J z (incV F x) • (incM F ι *ᵥ w + c • incV F x) -
      hAd σ J z (incM F ι *ᵥ w) • incV F x := by
  have key : ∀ (p r : Fin n → AE F E), Matrix.vecMulVec p r *ᵥ z = (z ⬝ᵥ r) • p := fun p r => by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [nMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, hAd]

end GlobalTheory.ThK.LemF.QuotInv

end
