import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionCharacterValueConstantTermOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDualCharValuesMulCubeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueComplexPointsEqFrameAlternatingProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueEqFirstJetAlternatingProductStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetGen

theorem mul_dot_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f : X →+ ℂ) {c : ℂ}
    (hc : c ≠ 0) (χ : X) : c * (co bX χ ⬝ᵥ fun l => f (bX l) / c) = f χ := by
  conv_rhs => rw [← bX.sum_repr χ]
  rw [map_sum, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  simp only [co]
  field_simp

theorem dual_alg (A : DualNumber ℂ) {c d c0 d0 l : ℂ} (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hA : A.fst = 1)
    (hl : l = A.snd + d / c - d0 / c0) :
    A * (TrivSqZeroExt.inl c + TrivSqZeroExt.inr d) * TrivSqZeroExt.inl c0 =
      (1 + TrivSqZeroExt.inr l) * TrivSqZeroExt.inl c * (TrivSqZeroExt.inl c0 + TrivSqZeroExt.inr d0) := by
  ext
  · simp [hA]
  · simp [hA, hl]
    field_simp
    ring

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ χ' : X) :
    co bX (χ + χ') = co bX χ + co bX χ' := by
  ext l; simp [co]

theorem tangent_generators : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
    (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b →
    ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ →
      vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) +
        TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) =
      (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) *
        (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) +
          TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  intro R _ _ _ _ D _ _ _ N ν g r bX d G gm W h0 hD

  set cf : (Fin g → ℂ) → ℂ := fun w => G.frG (ν.J (ν.eA (d.ex w)).left) w with hcf
  set df : (Fin g → ℂ) → ℂ := fun w => fderiv ℂ (G.frG (ν.J (ν.eA (d.ex w)).left)) w W with hdf
  have hc : ∀ w, cf w ≠ 0 := fun w => by
    simp only [hcf, ← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  set Dl : (Fin g → ℂ) → ℂ := fun w => df w / cf w with hDl
  set A : N.X → DualNumber ℂ := fun χ => vE (gm.s (ν.eX χ)) (𝟙 _) ν.J with hA
  have hA1 : ∀ χ, (A χ).fst = 1 := fun χ => GlobalTheory.T.torusExtension_characterValue_constantTerm_one ν gm h0 (ν.eX χ)
  set ct : N.X → (Fin g → ℂ) := fun χ => d.t12 *ᵥ co bX χ with hct
  have hct_add : ∀ χ χ', ct (χ + χ') = ct χ + ct χ' := fun χ χ' => by
    simp only [hct, co_add, Matrix.mulVec_add]
  have hx : ∀ χ, ν.eA (d.ex (ct χ)) = DegPre.cF D ℂ (ν.eX χ) := fun χ => by
    rw [← d.c_eq]; exact ν.c_eq χ
  have hprod := fun x y z j hj => GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct ν d.toAB d.cub G x y z j hj

  have hsnd : ∀ χ χ', (A (χ + χ')).snd + (Dl (ct χ + ct χ') + Dl 0 - Dl (ct χ) - Dl (ct χ')) =
      (A χ).snd + (A χ').snd := fun χ χ' => by
    have hm := GlobalTheory.T.torusExtension_dualCharValues_mul_cube ν gm (ν.eX χ) (ν.eX χ')
    rw [GlobalTheory.T.cube_value_eq_first_jet_alternating_product ν d.toAB G hprod W gm h0 hD _ _ (ct χ) (ct χ') (hx χ) (hx χ'), ← map_add] at hm
    have e := congrArg TrivSqZeroExt.snd hm
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at e
    have e1 := hA1 (χ + χ'); have e2 := hA1 χ; have e3 := hA1 χ'
    simp only [hA] at e1 e2 e3 ⊢
    rw [e1, e2, e3] at e
    linear_combination e
  clear hprod
  set ℓ : N.X → ℂ := fun χ => (A χ).snd + Dl (ct χ) - Dl 0 with hℓ
  have hℓ_add : ∀ χ χ', ℓ (χ + χ') = ℓ χ + ℓ χ' := fun χ χ' => by
    have := hsnd χ χ'
    simp only [hℓ, hct_add]
    linear_combination this
  let ℓh : N.X →+ ℂ := AddMonoidHom.mk' ℓ hℓ_add
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l => ℓ (bX l) / (2 * Real.pi * Complex.I), fun χ ct' hct' => ?_⟩
  have hT : (2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ fun l => ℓ (bX l) / (2 * Real.pi * Complex.I)) = ℓ χ :=
    mul_dot_basis bX ℓh h2pi χ
  rw [hT, hct']
  exact dual_alg (A χ) (hc _) (hc 0) (hA1 χ) rfl

end GlobalTheory.MBLow.Cl.JetGen

end
