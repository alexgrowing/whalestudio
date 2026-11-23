import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagMapChernRootsX
import Formalism.DegreeFormula.PointDegree.PowSum
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop.RelVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rho_eq_flagMap (H : Host E) (Dw : Datum H) : rho H Dw = GlobalTheory.Schubert.flagMap Dw := by
  unfold rho GlobalTheory.Schubert.flagMap
  congr 1

noncomputable def numLin (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  GlobalTheory.Schubert.flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (GlobalTheory.Schubert.flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (rootDiscr Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem numLin_apply (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    numLin H Dw Q = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (GlobalTheory.Schubert.flagMap Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) := by
  simp [numLin, GlobalTheory.Schubert.flagLin_apply]

theorem numLin_of_chernRoots_eq_zero (H : Host E) (Dw : Datum H) (g : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hg : chernRoots Dw.mult g = 0) (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (g * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), hg, zero_mul, zero_mul, map_zero, ← GlobalTheory.Schubert.flagLin_apply, map_zero]

theorem chernRoots_X_zero_sub_one (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) :
    chernRoots Dw.mult (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  simp [chernRoots, esymm_zero]

theorem chernRoots_X_of_lt (H : Host E) (Dw : Datum H) (τ : E →+* ℂ) (k : ℕ) (hk : Dw.mult τ < k) :
    chernRoots Dw.mult (X (τ, k) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) = 0 := by
  have h0 : esymm (Fin (Dw.mult τ)) ℝ k = 0 := by
    unfold esymm
    rw [Finset.powersetCard_eq_empty.mpr (by simpa using hk)]
    simp
  simp [chernRoots, h0]

theorem numLin_relPoly (H : Host E) (Dw : Datum H) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (hk : 1 ≤ k)
    (a : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : numLin H Dw (GlobalTheory.PointChern.relPoly τ k * a) = 0 := by
  rw [numLin_apply, map_mul (chernRoots Dw.mult), mul_assoc, map_mul, GlobalTheory.Schubert.RelKill.flagMap_relPoly]
  exact Formalism.DegreeFormula.degreeEsymmMulEqZero _ _ τ k _ hk

theorem numLin_mul_eq_zero (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)
    (hQ : Q ∈ relIdeal H Dw) : ∀ a, numLin H Dw (Q * a) = 0 := by
  unfold relIdeal at hQ
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    intro a
    rcases hx with (⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_zero_sub_one H Dw τ) a
    · exact numLin_of_chernRoots_eq_zero H Dw _ (chernRoots_X_of_lt H Dw τ k hk) a
    · exact numLin_relPoly H Dw τ k hk a
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [add_mul, map_add, hx, hy, add_zero]
  | smul r x _ hx => intro a; rw [smul_eq_mul, mul_assoc, mul_comm r, mul_assoc]; exact hx _

end GlobalTheory.GrassTop.RelVanish

namespace GlobalTheory.GrassTop

theorem intGr_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  intro E _ _ _ H Dw Q hQ
  have h := RelVanish.numLin_mul_eq_zero H Dw Q hQ 1
  rw [mul_one, RelVanish.numLin_apply, ← RelVanish.rho_eq_flagMap] at h
  rw [intGr, h, zero_div]

end GlobalTheory.GrassTop
