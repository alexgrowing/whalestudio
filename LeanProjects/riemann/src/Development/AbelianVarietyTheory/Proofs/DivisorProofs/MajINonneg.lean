import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def tAd (s : ℝ) : AF F := 1 + realAd F (s - 1)

def blkScale {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (s : Fin q → ℝ) (z : κ → AF F) : κ → AF F :=
  fun j => (∏ i, if j ∈ blk i then tAd F (s i) else 1) * z j

def IsFrameCo (σ : E →ₐ[F] E) {n d q : ℕ} (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x y : Fin q → Fin n → E) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW)) (Fin n × Fin d))
    (blk : Fin q → Finset (Fin n × Fin d)) : Prop :=
  (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
  ∀ (t : Fin q → ℝ) (a : UA σ J), (∀ i, 0 < t i) → IsTorusU x y t a → ∀ z : Fin n × Fin d → AF F,
    co.e (mat a * co.e.symm (z, 0)) = (blkScale blk (fun i => (t i)⁻¹) z, 0) ∧
    co.e (mat a * co.e.symm (0, z)) = (0, blkScale blk t z)

def majW {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  (∏ i, t i) ^ A * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
    (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹

open Classical in

def majI {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  if ∀ j, IsIntegral ℤ ((m : F) * ξ j) then majW blk A N t ξ else 0

open Classical in

def latG {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  if ∀ i, ∃ j ∈ blk i, ξ j ≠ 0 then majI blk A N m t ξ else 0

theorem majW_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ majW blk A N t ξ := by
  unfold majW
  refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun i _ => ht i) _) (inv_nonneg.2 (mul_nonneg ?_ ?_))
  · exact Finset.prod_nonneg fun i _ => pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (ht i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => (apply_nonneg w _)))) _
  · exact pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => (apply_nonneg w _))) _

theorem majI_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ majI blk A N m t ξ := by
  unfold majI; split_ifs
  · exact majW_nonneg blk A N t ξ ht
  · exact le_rfl

theorem latG_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ latG blk A N m t ξ := by
  unfold latG; split_ifs
  · exact majI_nonneg blk A N m t ξ ht
  · exact le_rfl

end GlobalTheory.ThKTorus
