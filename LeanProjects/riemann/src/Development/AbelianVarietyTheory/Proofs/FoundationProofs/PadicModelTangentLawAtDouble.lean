import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ModelDouble

open WeierstrassCurve

theorem weierstrassP_two_mul (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) (h2 : 2 * P ∉ L.lattice) :
    L.derivWeierstrassP P ≠ 0 ∧
      L.weierstrassP (2 * P) =
        ((3 * L.weierstrassP P ^ 2 - L.g₂ / 4) / L.derivWeierstrassP P) ^ 2 - 2 * L.weierstrassP P := by
  have hPP : P + P ∉ L.lattice := by rwa [← two_mul]
  have hd : L.derivWeierstrassP P ≠ 0 := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hP).not.mpr hPP
  refine ⟨hd, ?_⟩
  have h := GlobalTheory.latticePoint_add L P P
  have hy : L.derivWeierstrassP P / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP P) (L.derivWeierstrassP P / 2) := by
    simp only [Affine.negY, GlobalTheory.latticeCurve]
    intro e; apply hd; linear_combination e
  rw [GlobalTheory.latticePoint_of_notMem L hP, GlobalTheory.latticePoint_of_notMem L hPP,
    Affine.Point.add_of_Y_ne hy, Affine.Point.some.injEq] at h
  rw [two_mul, h.1, Affine.slope_of_Y_ne rfl hy]
  simp only [Affine.addX, Affine.negY, GlobalTheory.latticeCurve]
  rw [show L.derivWeierstrassP P / 2 - (-(L.derivWeierstrassP P / 2) - 0 * L.weierstrassP P - 0) = L.derivWeierstrassP P by ring]
  field_simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : Qbar} (hx : x ≠ 0) : lam x ≠ 0 :=
  (map_ne_zero lam).mpr hx

theorem tangent_law : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  intro p _ g P hlat hg2 _ hP h2P hwF hwD
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair _ hlat
  obtain ⟨hd, hdup⟩ := weierstrassP_two_mul L ((hL P).not.mp hP) ((hL _).not.mp h2P)
  simp only [← GlobalTheory.LatticeInvariants.wpF_eq hL, ← GlobalTheory.LatticeInvariants.wpD_eq hL,
    ← GlobalTheory.LatticeInvariants.g2_eq hL] at hd hdup
  set a : Qbar := ⟨wpF g.abelian₂ P, hwF⟩ with ha
  set d : Qbar := ⟨wpD g.abelian₂ P, hwD⟩ with hd'
  set G : Qbar := ⟨g2 g.abelian₂, hg2⟩ with hG
  have hd0 : d ≠ 0 := fun h => hd (congrArg Subtype.val h)
  have he : wpF g.abelian₂ (2 * P) = (((((3 * a ^ 2 - G / 4) / d) ^ 2 - 2 * a : Qbar)) : ℂ) := by
    rw [hdup]; simp [a, d, G]; norm_cast
  have lX : lamC g.lam (wpF g.abelian₂ P) = g.lam a := lamC_coe _ a
  have lD : lamC g.lam (wpD g.abelian₂ P) = g.lam d := lamC_coe _ d
  have l2 : lamC g.lam (wpF g.abelian₂ (2 * P)) = ((3 * g.lam a ^ 2 - g.lam G / 4) / g.lam d) ^ 2 - 2 * g.lam a := by
    rw [he, lamC_coe]; simp [map_div₀, map_ofNat]
  have lA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam G) / 4 := by
    rw [show -(g2 g.abelian₂) / 4 = ((-G / 4 : Qbar) : ℂ) by simp [G]; norm_cast, lamC_coe]; simp [map_div₀, map_ofNat]
  have lD0 : g.lam d ≠ 0 := lamC_ne_zero _ hd0
  have ε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  simp only [GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt, GL3Theta.G1.W, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, wModel, lX, lD, l2, lA]
  set ε := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  set X := g.lam a
  set D := g.lam d
  have hden : 2 * (ε ^ 3 * (D / 2 - g.C.s * (X - g.C.r) - g.C.t)) + ε * (0 + 2 * g.C.s) * (ε ^ 2 * (X - g.C.r)) +
      ε ^ 3 * (0 + g.C.r * 0 + 2 * g.C.t) = ε ^ 3 * D := by ring
  rw [hden]
  refine ⟨mul_ne_zero (pow_ne_zero _ ε0) lD0, ?_⟩
  field_simp
  ring

end GlobalTheory.ModelDouble
