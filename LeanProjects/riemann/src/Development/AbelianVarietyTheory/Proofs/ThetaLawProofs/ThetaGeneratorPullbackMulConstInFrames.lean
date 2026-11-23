import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AutSimilitudeAndMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMulStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFramesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

namespace GlobalTheory.SimilTheta

theorem ex_nsmul_eq_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex ((m : ℤ) • z) = u.ex z ^ m := by
  rw [natCast_zsmul]
  induction m with
  | zero => simpa using GlobalTheory.CubeValues.ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_comp_id_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex z ≫ (𝟙 A) ^ m = u.ex ((m : ℤ) • z) := by
  rw [ex_nsmul_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem generator_mul_const_in_frames : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = C * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := by
  intro g m x h u τ a b al hab hW hm hal mu hmu
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB x.P.A.left (Fin 2)
    ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2] mu hmu (Fin g → ℂ) (fun z => (u.ex z).left)
    ![fun z => (m : ℤ) • z, fun z => z] u.hol
    (Fin.forall_fin_two.2 ⟨differentiable_id.const_smul (m : ℤ), differentiable_id⟩)
    (fun e => Fin.forall_fin_two.2 ⟨congrArg (fun q => q.left) (ex_comp_id_pow u m e), Category.comp_id _⟩)
  have hv : ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) →
      valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val =
        T z * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := fun z j h0 h1 => by
    refine (hTv z j (Fin.forall_fin_two.2 ⟨h0, h1⟩)).trans ?_
    rw [Fin.prod_univ_two]
    exact congrArg (fun t => T z * (t * u.fr (j 1) z ^ (-(m : ℤ) ^ 2))) (zpow_one _)
  have hper : ∀ z, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), T (z + l) = T z := by
    intro z l hl
    obtain ⟨k, n, hkn⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k n := hkn
    obtain ⟨i0, h0⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex ((m : ℤ) • z)).left
    obtain ⟨i1, h1⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex z).left
    have e1 : u.ex (z + lat τ k n) = u.ex z := GlobalTheory.CubeValues.ex_add_period u z _ hl
    have e0 : u.ex ((m : ℤ) • (z + lat τ k n)) = u.ex ((m : ℤ) • z) := by
      rw [ex_nsmul_eq_pow, e1, ex_nsmul_eq_pow]
    have A1 := hv z ![i0, i1] h0 h1
    have A2 := hv (z + lat τ k n) ![i0, i1] (by rw [e0]; exact h0) (by rw [e1]; exact h1)
    rw [e1, A1] at A2
    have n0 := u.fr_ne i0 ((m : ℤ) • (z + lat τ k n)) (by rw [e0]; exact h0)
    have n1 := u.fr_ne i1 (z + lat τ k n) (by rw [e1]; exact h1)
    have f0 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW ((m : ℤ) • k) ((m : ℤ) • n) i0 _ h0
    have f1 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW k n i1 _ h1
    rw [lat_zsmul, ← smul_add, (GlobalTheory.SimilTheta.aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).2] at f0
    change T z * (u.fr i0 _ * u.fr i1 _ ^ _) = T _ * (u.fr i0 _ * u.fr i1 _ ^ _) at A2
    rw [f0, f1] at A2
    have na := aut_ne_zero τ a b k n z
    have hp : (-(m : ℤ) ^ 2) = -((m ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow] at A2
    field_simp at A2
    exact A2.symm
  refine ⟨T 0, hT0 0, fun z j h0 h1 => ?_⟩
  rw [hv z j h0 h1, GlobalTheory.entire_apply_eq_of_periodic_of_span_real hT u.full hper z 0]

end GlobalTheory.SimilTheta
