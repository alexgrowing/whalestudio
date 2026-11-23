import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentGeneratorsHolomorphicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetFam

open TrivSqZeroExt in
theorem dual_unit {a a' : ℂ} (ha : a ≠ 0) : IsUnit (inl a + inr a' : DualNumber ℂ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using ha

open TrivSqZeroExt in
theorem dual_mul {S V : DualNumber ℂ} {a a' r r' p p' e : ℂ} {k : ℕ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h1 : S * inl a * (inl r + inr r') = (inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r)
    (h2 : V * (inl a + inr a') * inl r = (1 + inr e) * inl a * (inl r + inr r')) :
    (S * V).fst / r ^ k = p ∧ (S * V).snd / r ^ k = p' + e * p + k * (r' / r) * p := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  have hu := ((ua.mul (dual_unit (a' := r') hr)).mul (dual_unit (a' := a') ha)).mul ur
  have key : S * V = (inl p + inr p') * (inl r + inr r') ^ k * (1 + inr e) := by
    apply hu.mul_right_cancel
    linear_combination (V * (inl a + inr a') * inl r) * h1 +
      ((inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r) * h2
  rw [key]
  constructor
  · simp [hr]
  · rcases k with _ | k
    · simp; ring
    · simp [TrivSqZeroExt.snd_pow]
      field_simp
      ring

open TrivSqZeroExt in
theorem dual_zero {V : DualNumber ℂ} {a r e : ℂ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h2 : V * (inl a + inr 0) * inl r = (1 + inr e) * inl a * (inl r + inr 0)) : V = 1 + inr e := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  apply (ua.mul ur).mul_right_cancel
  rw [inr_zero, add_zero, add_zero] at h2
  linear_combination h2

variable {g' r g : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r)

def join (z : Fin g' → ℂ) (t : Fin r → ℂ) : Fin g → ℂ := fun j => Sum.elim z t (σ j)

theorem leftComponent_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : zP σ (join σ z t) = z := by
  funext i; simp [zP, join]

theorem secondBlock_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : tP σ (join σ z t) = t := by
  funext i; simp [tP, join]

theorem join_zero : join σ 0 0 = 0 := by
  funext j; simp only [join]; rcases σ j with i | i <;> simp

theorem diff_join : Differentiable ℂ fun z : Fin g' → ℂ => join σ z 0 := by
  refine differentiable_pi.2 fun j => ?_
  simp only [join]
  rcases σ j with i | i
  · simp only [Sum.elim_inl]; fun_prop
  · simp

def zL : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ.symm (Sum.inl i))

def tL (c : ℂ) (v : Fin r → ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  c • ∑ l, v l • ContinuousLinearMap.proj (σ.symm (Sum.inr l))

theorem zL_apply (Y : Fin g → ℂ) : zL σ Y = zP σ Y := rfl

theorem tL_apply (c : ℂ) (v : Fin r → ℂ) (Y : Fin g → ℂ) : tL σ c v Y = c * (v ⬝ᵥ tP σ Y) := by
  simp [tL, tP, dotProduct]

theorem fderiv_eq (c : ℂ) (v : Fin r → ℂ) {F : (Fin g → ℂ) → ℂ} {φ : (Fin g' → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ Y, F Y = Complex.exp (c * (v ⬝ᵥ tP σ Y)) * φ (zP σ Y)) (Z : Fin g → ℂ) :
    fderiv ℂ F 0 Z = fderiv ℂ φ 0 (zP σ Z) + c * (v ⬝ᵥ tP σ Z) * φ 0 := by
  have e : F = fun Y => Complex.exp (tL σ c v Y) * φ (zL σ Y) := by
    funext Y; rw [h, tL_apply, zL_apply]
  have h1 : HasFDerivAt (fun Y => Complex.exp (tL σ c v Y)) _ (0 : Fin g → ℂ) := (tL σ c v).hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun Y => φ (zL σ Y)) _ (0 : Fin g → ℂ) :=
    (hφ (zL σ 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (zL σ).hasFDerivAt
  have h3 := (h1.mul h2).fderiv
  rw [e]
  refine (congrArg (fun L => L Z) h3).trans ?_
  rw [map_zero, map_zero]
  simp [tL_apply, zL_apply, mul_comm]

end GlobalTheory.MBLow.Cl.JetFam

namespace GlobalTheory.MBLow.Cl

open JetFam

theorem jet_family_deriv : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (_ : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g' → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ (Z : Fin g → ℂ) (c₀ : ℂ), zP σ Z = W ∧ (W = 0 → ∀ χ, vE (gm.s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ tP σ Z))) ∧ ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F → (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) → (jc ν s gm α).fst / ν.rg ^ k = F 0 ∧ (jc ν s gm α).snd / ν.rg ^ k = fderiv ℂ F 0 Z + k * c₀ * F 0 := by
  intro R _ _ _ _ D hE hT _ N ν g' r g bX d σ G gm W ho hW
  obtain ⟨T, hT'⟩ := GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame R D hE hT N ν g' r bX d G gm W ho hW
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.FamVal.rg_ne ν
  have hne : ∀ z, G.frG (ν.J (ν.eA (d.ex z)).left) z ≠ 0 := fun z => by
    rw [← G.fr_eq]; exact mul_ne_zero (Units.ne_zero _) hrg
  have h0 : G.frG (ν.J (ν.eA (d.ex 0)).left) 0 = ν.rg := by
    rw [← G.fr_eq, d.fr_zero]; simp
  refine ⟨join σ W T, fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / ν.rg, leftComponent_join σ W T, ?_, ?_⟩
  · intro hW0 χ
    have := hT' χ _ rfl
    subst hW0
    rw [map_zero, map_zero] at this
    rw [secondBlock_join]
    exact dual_zero (hne _) (hne _) this
  · intro k s f α F hs hF hf
    obtain ⟨o, hz, hp⟩ := ho
    have hb : redE ℂ ≫ gm.b.left = (DegPre.zeroF D ℂ).left := by
      rw [← hz.1]; exact hp.1.symm
    have hpt := fun Y => ((GlobalTheory.MBLow.Cl.exp_onto_torusExt N g' r g bX d σ).1 Y).exists
    have hφ : Differentiable ℂ fun z => F (join σ z 0) := hF.comp (diff_join σ)
    have hA : ∀ z, f α (d.ex z) * d.fr (d.t12 *ᵥ co bX α) * d.fr z =
        F (join σ z 0) * (d.fr z : ℂ) ^ k * d.fr (d.t12 *ᵥ co bX α + z) := fun z => by
      obtain ⟨h, hh⟩ := hpt (join σ z 0)
      have e1 := hf _ h hh
      have e2 := hh.2 α
      rw [hh.1] at e1
      rw [leftComponent_join] at e1 e2
      rw [secondBlock_join] at e2
      simp only [dotProduct_zero, mul_zero, Complex.exp_zero, one_mul] at e2
      linear_combination (d.fr (d.t12 *ᵥ co bX α + z) : ℂ) * e1 - f α (d.ex z) * e2
    have hB : ∀ Y, F Y = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * F (join σ (zP σ Y) 0) :=
      fun Y => by
      obtain ⟨h, hh⟩ := hpt Y
      have e1 := hf _ h hh
      have e2 := hh.2 α
      have e3 := hA (zP σ Y)
      rw [hh.1] at e1
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k (d.fr (zP σ Y)).ne_zero)
        (d.fr (d.t12 *ᵥ co bX α + zP σ Y)).ne_zero)
      linear_combination (-(d.fr (d.t12 *ᵥ co bX α + zP σ Y) : ℂ)) * e1 + f α (d.ex (zP σ Y)) * e2 +
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * e3
    have h1 := GlobalTheory.T.familyMember_tangentValue_eq_firstJet R D hE hT N ν g' d.toAB G gm.b W hb hW k s f α _ _ hs (d.c_eq α) hφ hA
    have h2 := dual_mul (hne _) (hne _) h1 (hT' α _ rfl)
    rw [h0, join_zero] at h2
    rw [fderiv_eq σ _ _ hφ hB, leftComponent_join, secondBlock_join, join_zero]
    exact h2

end GlobalTheory.MBLow.Cl

end
