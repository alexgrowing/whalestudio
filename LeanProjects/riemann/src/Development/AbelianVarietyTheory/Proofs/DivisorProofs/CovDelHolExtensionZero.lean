import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.CurvSubQuotTautPairGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotDelHol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_flat {n : Type*} [Fintype n] [DecidableEq n] {H : V → Matrix n n ℂ} {z : V}
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ₁ ξ₂ : V) :
    mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * conn H z ξ₂ - conn H z ξ₂ * conn H z ξ₁ = 0 := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have e : ∀ ζ ζ', mdel (fun x => conn H x ζ) z ζ' =
      (H z)ᵀ⁻¹ * (mdel (fun x => mdel H x ζ) z ζ')ᵀ +
        -((H z)ᵀ⁻¹ * (mdel H z ζ')ᵀ * (H z)ᵀ⁻¹) * (mdel H z ζ)ᵀ := by
    intro ζ ζ'
    simp only [conn]
    rw [mdel_mul (h1.transpose.inv hu') (h2.mdel (by norm_num) ζ).transpose,
      mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ζ), mdel_transpose]
  rw [e, e, mdel_mdel_comm h2 ξ₁ ξ₂]
  simp only [conn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  abel

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem covDelHol_extFormAdj_eq_zero {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}
    (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V) :
    covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hγ : ∀ ζ, (fun x => extFormAdj H x ζ) =ᶠ[𝓝 z]
      fun x => -(quotMap m l * conn H x ζ * incl m l) := fun ζ => by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [extFormAdj_eq_neg_secondForm (h.one hx) (h.eventually_herm hx) (h.isUnit x hx) (hs x hx),
      secondForm, blockQS]
  have hc : ∀ ζ, MContDiffAt 1 (fun x => conn H x ζ) z := fun ζ => h2.conn hu (by norm_num) ζ
  have hd : ∀ ζ ζ', mdel (fun x => extFormAdj H x ζ) z ζ' =
      -(quotMap m l * mdel (fun x => conn H x ζ) z ζ' * incl m l) := by
    intro ζ ζ'
    rw [mdel_congr (hγ ζ), mdel_neg, mdel_mul ((mContDiffAt_const _).mul (hc ζ))
      (mContDiffAt_const _), mdel_mul (mContDiffAt_const _) (hc ζ)]
    simp
  have hv : ∀ ζ, extFormAdj H z ζ = -(quotMap m l * conn H z ζ * incl m l) :=
    fun ζ => (hγ ζ).self_of_nhds
  have hS : ∀ ζ, conn (gramS H) z ζ = orthProj (H z) * conn H z ζ * incl m l :=
    fun ζ => Model.conn_sub hu hsz ζ
  have hQ : ∀ ζ, conn (gramQ H) z ζ = quotMap m l * conn H z ζ * orthLift (H z) :=
    fun ζ => Model.conn_quot h1 hu hsz ζ
  have hF := conn_flat h2 hu ξ₁ ξ₂
  have key : quotMap m l * (mdel (fun x => conn H x ξ₂) z ξ₁ - mdel (fun x => conn H x ξ₁) z ξ₂ +
      conn H z ξ₁ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₂ -
      conn H z ξ₂ * (incl m l * orthProj (H z) + orthLift (H z) * quotMap m l) * conn H z ξ₁) *
      incl m l = 0 := by
    rw [incl_mul_orthProj_add, Matrix.mul_one, Matrix.mul_one, hF]; simp
  simp only [covDelHol, homDel, hd, hv, hS, hQ]
  rw [← neg_eq_zero, ← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc, neg_neg, neg_sub, neg_add]
  abel

end GlobalTheory.SubQuotDelHol
