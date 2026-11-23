import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDiagonalMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAppellHumbertFormOfMumfordBundleLbIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLineBundleIsoOfAppellHumbertAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvNatSmulMemDiscreteSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairOfLambdaBundleIsoStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiFormAdj

theorem real_eq_of_exp {p : ℤ} {r : ℝ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / n)) : (p : ℝ) = r := by
  have h1 := h 1 one_pos
  simp only [Nat.cast_one, div_one] at h1
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hr : (r : ℂ) = ((p + m : ℤ) : ℂ) := by
    have := Complex.two_pi_I_ne_zero
    push_cast
    apply mul_left_cancel₀ this
    linear_combination hm
  have hr' : r = ((p + m : ℤ) : ℝ) := by exact_mod_cast hr
  have := GlobalTheory.HermAdjoint.int_eq_of_exp (p := p) (q := p + m) (fun n hn => by rw [h n hn, hr])
  rw [hr', ← this]

theorem lbIso_pull_iff_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF he hQ hker hW f f' u u' hf hf' hu hu'
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  obtain ⟨v, Hm, χ, hve, hAH⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_exponential A g hA hg e he M hM
  have hN : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hND := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM A (𝟙 A) (𝟙 A)
  have hmem : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => (v.ker z).symm.trans (by rw [hve]; exact hker z)
  have hEF : ∀ a b, (EF a b : ℝ) = 2 * (hermForm Hm (Q a) (Q b)).im := by
    intro a b
    apply real_eq_of_exp
    intro k hk
    have hc := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)
    have hc' := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm (Q a) (Q b)).im : ℝ)) : ℂ) / k)
    have w1 := hW k a b (Units.mk0 _ hc) hk rfl
    have w2 := GlobalTheory.T.commutator_pairing_diagonal_mumford_bundle A g hA hg M v Hm χ hM hAH _ hN hND hamp k (Q a) (Q b) (Units.mk0 _ hc') hk
      ((hmem _).2 ⟨a, rfl⟩) ((hmem _).2 ⟨b, rfl⟩) rfl
    rw [hve, hve] at w2
    exact congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ hN (𝟙 (Sp ℂ)) k _ _ _ _ w1 w2)
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f he he hf
  obtain ⟨F', hF', -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f' he he hf'
  have hlift : ∀ (G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (w : La →+ La), (∀ z, e (G z) = e z ≫ φ) →
      (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (w x)) = e ((k : ℂ)⁻¹ • Q x) ≫ φ) → ∀ x, G (Q x) = Q (w x) := by
    intro G φ w hG hw x
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_inv_nat_smul_mem_discrete_submodule g v.Λ v.discrete (G (Q x) - Q (w x)) fun k hk => ?_)
    refine (hmem _).2 ((hker _).1 ?_)
    have e1 : e ((k : ℂ)⁻¹ • G (Q x)) = e ((k : ℂ)⁻¹ • Q (w x)) := by
      rw [← map_smul, hG, hw k x hk]
    have e2 := he.1 ((k : ℂ)⁻¹ • (G (Q x) - Q (w x))) ((k : ℂ)⁻¹ • Q (w x))
    rw [← smul_add, sub_add_cancel, e1] at e2
    exact mul_eq_right.1 e2.symm
  have hFQ := hlift F f u hF hu
  have hFQ' := hlift F' f' u' hF' hu'
  have hvF : ∀ z, v.ex (F z) = v.ex z ≫ f := fun z => by rw [hve, hve]; exact hF z
  have hvF' : ∀ z, v.ex (F' z) = v.ex z ≫ f' := fun z => by rw [hve, hve]; exact hF' z
  have hisoL := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A ≫ f) (snd A A)
  have hisoR := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A) (snd A A ≫ f')
  have hcl : ∀ (a b : A ⊗ A ⟶ A), (cubeLB A ![a, b] M).IsLB := fun a b => LB.isLB_linComb hM _ _
  have key : LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔
      LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
    constructor
    · intro h
      exact LBIso.trans (hcl _ _) (pull_isLB hP _) (hcl _ _) hisoL.symm
        (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (hcl _ _) h hisoR)
    · intro h
      exact LBIso.trans (pull_isLB hP _) (hcl _ _) (pull_isLB hP _) hisoL
        (LBIso.trans (hcl _ _) (hcl _ _) (pull_isLB hP _) h hisoR.symm)
  rw [key]
  constructor
  · intro h x y
    have := GlobalTheory.T.adjoint_appellHumbertForm_of_mumfordBundle_lbIso A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF' h (Q x) (Q y)
    have hh : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by
      rw [hEF, hEF, ← hFQ, ← hFQ', this]
    exact_mod_cast hh
  · intro h
    apply GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF'
    refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ v.full fun a ha b hb => ?_
    obtain ⟨x, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, rfl⟩ := (hmem b).1 hb
    have h1 := hEF (u x) y
    have h2 := hEF x (u' y)
    have h3 : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by rw [h x y]
    rw [hFQ, hFQ']
    linarith

end GlobalTheory.RosatiFormAdj
