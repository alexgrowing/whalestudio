import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AnyAppellHumbert

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.eq, Matrix.dotProduct_mulVec]

theorem semicharacter_add {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) (n : ℤ)
    (hn : (n : ℝ) = (hermForm Hm l m).im) : χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have hi'' : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 m i _ hi'
  have h3 := h.2.2.2 (l + m) i 0 hi
  have hs := hermForm_swap h.1 (l : Fin g → ℂ) m
  have hne := u.fr_ne i _ hi''
  rw [h2, h3] at h1
  simp only [zero_add, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    zero_dotProduct, mul_zero] at h1 hne
  unfold hermForm at hs hn
  rw [hs] at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h1
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h1 hn
  have hc : c = star c + 2 * n * Complex.I := by
    have := Complex.sub_conj c
    rw [← hn] at this
    push_cast at this
    rw [Complex.star_def]
    linear_combination this
  have he : Complex.exp (Real.pi / 2 * a) * Complex.exp (Real.pi * c + Real.pi / 2 * b) =
      (-1) ^ n * Complex.exp (Real.pi / 2 * (a + star c + (c + b))) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * hc
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (Real.pi / 2 * (a + star c + (c + b)))) hne) ?_
  linear_combination h1 + χ l * χ m * u.fr i (l + m) * he

theorem isAH_properties :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  intro hlaw _ _ hU P u Hm χ hA
  obtain ⟨ht1, ht2, hE⟩ := AnyUnif.tangent_and_unimodular hU P u
  obtain ⟨Ef, hEf, hb⟩ := hE Hm χ hA
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hholprod := @holFamily_lift hval
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hlaw.weil hval hvalext hsmred hthg
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hlaw.globalSectionsRank
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  have h7 := hsecfn P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩
  refine ⟨Ef, hEf, hb, fun l => sq_eq_one_iff.1 (semicharacter_sq_eq_one_of_symmetric P u Hm χ hA l), fun l m => semicharacter_add P.isLB u hA l m _ (hEf l m),
    ht1, ht2, fun n => ⟨(h7 n).1, fun θ hθ => ?_⟩, hweil P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩⟩
  obtain ⟨s, hs⟩ := hseconto P u Hm χ Ef hA ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩ hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 n).2 θ s' s hs' hs⟩

end GlobalTheory.AnyAppellHumbert
