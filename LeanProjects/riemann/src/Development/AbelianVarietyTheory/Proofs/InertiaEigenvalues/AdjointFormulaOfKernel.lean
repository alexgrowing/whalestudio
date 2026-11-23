import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.AdjUp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) : GA D (Vc D i) → (R.cV i).W :=
  fun h => ∑ k, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h • b k

theorem inner_upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (k : Fin n) (h : GA D (Vc D i)) :
    ⟪b k, upVec R i t v b y h⟫_ℂ = upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h :=
  b.orthonormal.inner_right_fintype _ k

theorem val_zero (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    val R i v 0 = 0 := by
  funext g
  simp [val]

theorem upLift_zero {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (h : GA D V) : upLift om ν 𝓖 f 0 h = 0 := by
  simp [upLift]

end GlobalTheory.AdjUp

end

namespace GlobalTheory.AdjUp

theorem adjoint_formula_of_kernel {H₁ H₂ W Gv Gw : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [FiniteDimensional ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace Gv] [MeasurableSpace Gw]
    (th : H₁ →ₗ[ℂ] H₂) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ W) (μW : Measure Gw) (μV : Measure Gv)
    (φ : H₂ → Gw → ℂ) (ψ : H₁ → Gw → ℂ) (ext : H₁ →ₗ[ℂ] (Gv → W)) (K : Fin n → H₂ → Gv → ℂ) (P c : ℝ)
    (hP0 : 0 ≤ P) (hc : 0 < c)
    (hPW : ∀ y z, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g, star (φ y g) * φ z g ∂μW)
    (hφ : ∀ u, φ (th u) = ψ u) (hφ0 : φ 0 = 0) (hK0 : ∀ k h, K k 0 h = 0)
    (hcV : ∀ u u', ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h, ⟪ext u h, ext u' h⟫_ℂ ∂μV ∧
      ∀ a a' : W, Integrable (fun h => star ⟪a, ext u h⟫_ℂ * ⟪a', ext u' h⟫_ℂ) μV)
    (h3 : ∀ y u, ∫ g, star (φ y g) * ψ u g ∂μW = ∫ h, ⟪∑ k, K k y h • b k, ext u h⟫_ℂ ∂μV)
    (h4 : ∀ y, ∃ u, ext u = fun h => ∑ k, K k y h • b k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
  choose U hU using h4
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hcoord : ∀ y k h, ⟪b k, ext (U y) h⟫_ℂ = K k y h := fun y k h => by
    rw [hU y]; exact b.orthonormal.inner_right_fintype _ k
  have hadj : ∀ y u, ⟪LinearMap.adjoint th y, u⟫_ℂ = (((P / c : ℝ)) : ℂ) * ⟪U y, u⟫_ℂ := by
    intro y u
    rw [LinearMap.adjoint_inner_left, hPW, hφ, h3, (hcV (U y) u).1, hU y, Complex.ofReal_div]
    field_simp
  have hsum : ∀ x y h, ⟪ext (U x) h, ext (U y) h⟫_ℂ = ∑ k, star (K k x h) * K k y h := by
    intro x y h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord, ← hcoord, ← inner_conj_symm]
    rfl
  by_cases hzero : P = 0
  · refine ⟨1, one_pos, fun x y => ?_⟩
    have h0 : ∀ z : H₂, z = 0 := fun z => by
      have := hPW z z
      rw [hzero, Complex.ofReal_zero, zero_mul] at this
      exact inner_self_eq_zero.1 this
    rw [h0 x, h0 y, map_zero, inner_zero_left]
    simp [hK0]
  · have hpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hzero)
    refine ⟨P ^ 2 / c, by positivity, fun x y => ?_⟩
    have hint : ∀ k ∈ Finset.univ, Integrable (fun h => star (K k x h) * K k y h) μV := by
      intro k _
      have := (hcV (U x) (U y)).2 (b k) (b k)
      simpa only [hcoord] using this
    have e1 : ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
        (((P / c : ℝ)) : ℂ) * (((P / c : ℝ)) : ℂ) * ⟪U x, U y⟫_ℂ := by
      rw [hadj x, ← inner_conj_symm, hadj y, map_mul, Complex.conj_ofReal, inner_conj_symm, mul_assoc]
    have e2 : ⟪U x, U y⟫_ℂ = (c : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
      rw [(hcV (U x) (U y)).1, ← integral_finset_sum _ hint]
      simp only [hsum]
    rw [e1, e2]
    push_cast
    field_simp

end GlobalTheory.AdjUp
