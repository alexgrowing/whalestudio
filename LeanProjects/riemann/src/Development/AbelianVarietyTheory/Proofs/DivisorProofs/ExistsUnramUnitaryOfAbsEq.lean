import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.LocalDetChar
open ValuativeRel GlobalTheory.SplitFlip

noncomputable section

def apowUnits {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (z : ℂ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (apow x z) (apow_ne_zero x z)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [apow_mul])

theorem exists_unram_unitary_of_abs_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (2 : k) ≠ 0 →
    ∀ (d m : ℕ) (κ : GL (Fin d) k →* ℂ),
    (∀ g, ‖κ g‖ = ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((m : ℂ) / 2)‖) →
    (∀ g : GL (Fin d) k, (∀ i j, ValuativeRel.valuation k (g.1 i j) ≤ 1) → ValuativeRel.valuation k g.1.det = 1 → κ g = 1) →
    ∃ ν : kˣ →* ℂˣ, IsUnram ν ∧ (∀ y, ‖((ν y : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ g, κ g = (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((m : ℂ) / 2) := by
  intro k _ _ _ _ h2 d m κ hnorm hint
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, fun _ _ => rfl, fun _ => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero h2 κ.toHomUnits
  have hκχ : ∀ g, κ g = (χ (gdet g) : ℂ) := fun g => by
    have := congrArg Units.val (hχ g)
    simpa using this

  let i0 : Fin d := ⟨0, hd⟩
  let D : kˣ → GL (Fin d) k := fun x => diagGL (fun i => if i = i0 then x else 1)
  have hD : ∀ x, gdet (D x) = x := fun x => by
    simp only [gdet, D, det_diagGL]
    rw [Finset.prod_eq_single i0 (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have hχx : ∀ x, (χ x : ℂ) = κ (D x) := fun x => by rw [hκχ, hD]
  refine ⟨χ * apowUnits (-((m : ℂ) / 2)), ?_, ?_, ?_⟩
  · intro x hx
    have hint' : κ (D x) = 1 := by
      apply hint
      · intro i j
        simp only [D, diagGL_val, Matrix.diagonal_apply]
        split_ifs with h1 h3
        · rw [hx]
        · simp
        · simp
      · have := congrArg Units.val (hD x)
        simp only [gdet, Matrix.GeneralLinearGroup.val_det_apply] at this
        rw [this, hx]
    apply Units.ext
    simp only [MonoidHom.mul_apply, Units.val_mul, apowUnits, MonoidHom.coe_mk, OneHom.coe_mk,
      Units.val_mk0, Units.val_one]
    rw [hχx, hint', apow_of_valuation_eq_one hx]
    simp
  · intro y
    simp only [MonoidHom.mul_apply, Units.val_mul, apowUnits, MonoidHom.coe_mk, OneHom.coe_mk,
      Units.val_mk0, norm_mul]
    rw [hχx, hnorm, hD, ← norm_mul, ← apow_add]
    simp
  · intro g
    simp only [MonoidHom.mul_apply, Units.val_mul, apowUnits, MonoidHom.coe_mk, OneHom.coe_mk,
      Units.val_mk0]
    rw [hκχ, mul_assoc, ← apow_add]
    simp

end
end GlobalTheory.LocalDetChar
