import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlocksEvaluationStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorus.Scale
variable {F : Type} [Field F] [NumberField F]

theorem realAd_add (u v : ℝ) : realAd F u + realAd F v = realAd F (u + v) := by
  simp only [realAd, map_add]
  rfl

theorem realAd_mul (u v : ℝ) : realAd F u * realAd F v = realAd F (u * v) := by
  simp only [realAd, map_mul]
  exact Prod.ext rfl (mul_zero _)

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem tAd_mul (u v : ℝ) : tAd F u * tAd F v = tAd F (u * v) := by
  simp only [tAd]
  have : realAd F (u * v - 1) = realAd F (u - 1) + realAd F (v - 1) + realAd F (u - 1) * realAd F (v - 1) := by
    rw [realAd_mul, realAd_add, realAd_add]; congr 1; ring
  rw [this]; ring

theorem tAd_one : tAd F 1 = 1 := by
  simp [tAd, realAd_zero]

theorem tAd_inv_mul {s : ℝ} (hs : s ≠ 0) : tAd F s⁻¹ * tAd F s = 1 := by
  rw [tAd_mul, inv_mul_cancel₀ hs, tAd_one]

section GlobalTheory
variable {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ)

theorem prod_inv_mul (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (j : κ) :
    (∏ i, if j ∈ blk i then tAd F (t i)⁻¹ else 1) * (∏ i, if j ∈ blk i then tAd F (t i) else 1) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · exact tAd_inv_mul (ht i)
  · exact one_mul 1

theorem blkScale_inv_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (z : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) (blkScale blk t z) = z := by
  funext j
  simp only [blkScale]
  rw [← mul_assoc, prod_inv_mul blk t ht j, one_mul]

theorem blkScale_add (s : Fin q → ℝ) (z w : κ → AF F) :
    blkScale blk s (z + w) = blkScale blk s z + blkScale blk s w := by
  funext j
  simp only [blkScale, Pi.add_apply, mul_add]

theorem dot_blkScale (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (x y : κ → AF F) :
    blkScale blk (fun i => (t i)⁻¹) x ⬝ᵥ blkScale blk t y = x ⬝ᵥ y := by
  simp only [dotProduct, blkScale]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, prod_inv_mul blk t ht j, one_mul]

theorem schr_blkScale (ψ : AddChar (AF F) ℂ) (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (p r : κ → AF F)
    (g : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (blkScale blk (fun i => (t i)⁻¹) p, blkScale blk t r) g (blkScale blk (fun i => (t i)⁻¹) x) =
      schr ψ (p, r) (fun z => g (blkScale blk (fun i => (t i)⁻¹) z)) x := by
  simp only [schr, dot_blkScale blk t ht, blkScale_add]

end GlobalTheory

section Main
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem co_mat_mul {σ : E →ₐ[F] E} {n d q : ℕ} {J : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    {x y : Fin q → Fin n → E} {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW)) (Fin n × Fin d)}
    {blk : Fin q → Finset (Fin n × Fin d)} (hco : IsFrameCo σ J JW x y co blk) {t : Fin q → ℝ} {a : UA σ J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    co.e (mat a * w) = (blkScale blk (fun i => (t i)⁻¹) (co.e w).1, blkScale blk t (co.e w).2) := by
  have hw : w = co.e.symm ((co.e w).1, 0) + co.e.symm (0, (co.e w).2) := by
    rw [← map_add]; simp
  conv_lhs => rw [hw]
  rw [Matrix.mul_add, map_add, ((hco.2 t a ht hta) _).1, ((hco.2 t a ht hta) _).2]
  simp

def twist {n d : ℕ} {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} (e : Fn F n d →ₗ[ℂ] Fn F n d) (om : Rep σ X W)
    (a : UA σ X.J) {q : ℕ} (blk : Fin q → Finset (Fin n × Fin d)) (t : Fin q → ℝ) : Fn F n d →ₗ[ℂ] Fn F n d :=
  LinearMap.funLeft ℂ ℂ (blkScale blk (fun i => (t i)⁻¹)) ∘ₗ e ∘ₗ om (a, 1)

theorem incM_one (n : ℕ) : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [incM]

theorem twist_heis {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hpair : IsPair B M χX χW om r s r' s') {q : ℕ}
    {x y : Fin q → Fin n → E} {M₁ : Model σ X W} {blk : Fin q → Finset (Fin n × Fin d)} {e : Fn F n d →ₗ[ℂ] Fn F n d}
    (hco : IsFrameCo σ X.J W.J x y M₁.co blk) (hev : IsEv B M M₁ 1 1 ∅ e) {t : Fin q → ℝ} {a : UA σ X.J}
    (ht : ∀ i, 0 < t i) (hta : IsTorusU x y t a) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ Ψ ∈ schA F (Fin n × Fin d), twist e om a blk t (M.co.rho B.ψ w Ψ) = M₁.co.rho B.ψ w (twist e om a blk t Ψ) := by
  intro Ψ hΨ
  have hs := hpair.weil.isUSplitting
  have hΨ' : om (a, 1) Ψ ∈ schA F (Fin n × Fin d) := hs.pres (a, 1) Ψ hΨ
  have h1 : om (a, 1) (M.co.rho B.ψ w Ψ) = M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ) := by
    rw [hs.impl (a, 1) w Ψ hΨ]
    congr 2
    simp [actAB, mat]
  have h2 : e (M.co.rho B.ψ (mat a * w) (om (a, 1) Ψ)) = M₁.co.rho B.ψ (mat a * w) (e (om (a, 1) Ψ)) := by
    simpa [incM_one] using hev.Heisenberg₂ (mat a * w) _ hΨ'
  funext z
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  simp only [twist, LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [h1, h2]
  simp only [Darboux.rho, co_mat_mul hco ht hta w]
  exact schr_blkScale blk B.ψ t hne _ _ _ z

end Main

theorem norm_eval_torus_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J), (∀ i, 0 < t i) → IsTorusU x y t a →
      ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
        ‖e (om (a * κ, h) (pureA F f φ)) z‖ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_blocks_evaluation hK F E σ B n d X W M χX χW om r s r' s' hpair q x y hxy M₁ blk e hM₁ hco hev
  refine ⟨ex, fun t a ht hta f κ h z => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_evaluation_self_linear hK F E σ B n d X W M χX χW om r s r' s' hpair M₁ e hM₁ hev (twist e om a blk t)
    (fun w => twist_heis hpair hco hev ht hta w)
  have hne : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have key : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z) := by
    intro Ψ hΨ z
    have := congrFun (hc Ψ hΨ) (blkScale blk t z)
    simpa [twist, blkScale_inv_blkScale blk t hne] using this
  have hc' := hex t a c ht hta key
  have hs := hpair.weil.isUSplitting
  have hΨ0 : om (κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) :=
    hs.pres (κ, h) _ (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
  rw [show ((a * κ, h) : UA σ X.J × UA σ W.J) = (a, 1) * (κ, h) by simp, map_mul, Module.End.mul_apply,
    key _ hΨ0, norm_mul]
  exact mul_le_mul_of_nonneg_right hc' (norm_nonneg _)

end GlobalTheory.ThKTorus.Scale
