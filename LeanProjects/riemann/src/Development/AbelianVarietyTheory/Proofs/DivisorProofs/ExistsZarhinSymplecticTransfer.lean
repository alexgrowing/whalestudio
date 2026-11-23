import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open Matrix

namespace GlobalTheory.ZarhinFam.KappaEx

def omegaB (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem omegaB_apply (h : ℕ) (a b : Fin h ⊕ Fin h → ℤ) : omegaB h a b = omegaStd a b := rfl

def emb (h : ℕ) (l : Fin 8) : Fin h ⊕ Fin h → Fin (8 * h) ⊕ Fin (8 * h) :=
  Sum.map (fun i => finProdFinEquiv (l, i)) (fun i => finProdFinEquiv (l, i))

def blk (h : ℕ) (l : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) where
  toFun a := a ∘ emb h l
  map_zero' := rfl
  map_add' _ _ := rfl

theorem omegaStd_eq_sum_blk (h : ℕ) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    omegaStd a b = ∑ l, omegaStd (blk h l a) (blk h l b) := by
  simp only [omegaStd]
  rw [← (finProdFinEquiv (m := 8) (n := h)).sum_comp, Fintype.sum_prod_type]
  rfl

def vMat (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (-(quat d)ᵀ) 0 1

theorem vMat_transpose_mul_form_mul {d : ℕ} (hd : 0 < d) : (vMat d)ᵀ * form d * vMat d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [vMat, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, quat_mul_transpose, h1, sub_smul]

theorem sum_sig {β : Type} [AddCommMonoid β] (g : Fin 4 ⊕ Fin 4 → β) : ∑ k, g (sig k) = ∑ s, g s := by
  simp [Fin.sum_univ_succ, Fintype.sum_sum_type, sig, add_assoc]

theorem sig_injective : Function.Injective sig := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [sig]

def kap (h d : ℕ) (k : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) :=
  ∑ l, vMat d (sig k) (sig l) • blk h l

theorem kap_apply (h d : ℕ) (k : Fin 8) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    kap h d k a = ∑ l, vMat d (sig k) (sig l) • blk h l a := by
  unfold kap
  rw [AddMonoidHom.finset_sum_apply]
  rfl

theorem inner_sum (d : ℕ) (m n : Fin 8) :
    ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) := by
  have e1 : ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ∑ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) :=
    sum_sig (fun p => ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n))
  have e2 : ∀ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) =
      ∑ q, vMat d p (sig m) * form d p q * vMat d q (sig n) :=
    fun p => sum_sig (fun q => vMat d p (sig m) * form d p q * vMat d q (sig n))
  rw [e1, Finset.sum_congr rfl fun p _ => e2 p]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem formZ_kap {h d : ℕ} (hd : 0 < d) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    formZ d h (fun k => kap h d k a) (fun k => kap h d k b) = omegaStd a b := by
  have e2 : ∀ k l, omegaStd (kap h d k a) (kap h d l b) =
      ∑ m, ∑ n, vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro k l
    rw [← omegaB_apply, kap_apply, kap_apply]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      omegaB_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [formZ, e2, Finset.mul_sum]
  have e3 : ∀ m n, ∑ k, ∑ l, form d (sig k) (sig l) *
      (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro m n
    rw [← inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ k, ∑ l, ∑ m, ∑ n, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b))
      = ∑ k, ∑ m, ∑ n, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
        simp only [e3]
    _ = omegaStd a b := by
        rw [vMat_transpose_mul_form_mul hd, omegaStd_eq_sum_blk]
        simp [Matrix.one_apply, sig_injective.eq_iff]

theorem blk_jlMap (h : ℕ) (l : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    blk h l (jlMap h a) = if l = 0 then a else 0 := by
  funext x
  split_ifs with hl
  · subst hl
    rcases x with i | i <;> simp [blk, emb, jlMap]
  · have hl1 : 1 ≤ (l : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hl (Fin.ext h0)
    rcases x with i | i <;> simp only [blk, emb, jlMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Sum.map_inl, Sum.map_inr, Pi.zero_apply] <;> rw [dif_neg] <;> simp only [finProdFinEquiv_apply_val, not_lt] <;>
      nlinarith [i.2]

theorem kap_jlMap (h d : ℕ) (k : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    kap h d k (jlMap h a) = if k = 0 then a else 0 := by
  rw [kap_apply]
  simp only [blk_jlMap, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases k <;> simp [vMat, sig]

end GlobalTheory.ZarhinFam.KappaEx

namespace GlobalTheory.ZarhinFam

open KappaEx in

theorem exists_kappaOK : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  intro h M d _ _ _ hd _
  refine ⟨kap h d, fun a b => ?_, fun a => ?_, fun k hk a => ?_⟩
  · rw [formZ_kap hd]
  · rw [kap_jlMap, if_pos rfl]
  · rw [kap_jlMap, if_neg hk]

end GlobalTheory.ZarhinFam
