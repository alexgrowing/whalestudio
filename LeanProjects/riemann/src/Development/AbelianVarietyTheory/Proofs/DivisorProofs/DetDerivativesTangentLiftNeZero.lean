import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongKodairaSpencerDeformationLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesDivJacobianIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

noncomputable section

theorem _root_.GlobalTheory.CompHS.det_tanLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho Q hz v hv zv hl i O hO g hzO hzv hJ
  obtain ⟨O₁, hzO₁, x, w, hw, hdx⟩ := GlobalTheory.T.exists_tangentVectors_functions_invertible_derivs M.str (dimFlag Dw) z
  have hzi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => hO (hzO hs)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun s hs => ⟨hzO₁ hs, hzi hs⟩
  let x' : Fin (dimFlag Dw) → Γ(M.X, O₁ ⊓ M.K.bundle.U i) := fun a => resG M.X inf_le_left (x a)
  have hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO)
  have hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO')
  have hwO₁ : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O₁ := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO₁)
  have e1 : (Matrix.of fun a b => (evalPt (w b) (O₁ ⊓ M.K.bundle.U i) (hwO' b) (x' a)).snd) =
      Matrix.of fun a b => (evalPt (w b) O₁ (hwO₁ b) (x a)).snd := by
    ext a b
    simp only [Matrix.of_apply, x']
    rw [evalPt_res (w b) inf_le_left (hwO₁ b) (hwO' b)]
  have hjc := GlobalTheory.T.det_derivatives_div_jacobian_independent M z i w hw O (O₁ ⊓ M.K.bundle.U i) hO inf_le_right g x' hzO hzO' hwO hwO'
  rw [e1] at hjc
  have hdg : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjc
    exact mul_ne_zero (hdx hwO₁) hJ hjc.symm
  have hQ := hKS K Q
  have hspan : ∀ c0 : Fin (dimFlag Dw), ∃ C : TIx Dw (psiSet H) → K, ∀ a,
      (evalPt (w c0) O (hwO c0) (g a)).snd = ∑ t, C t * (evalPt (zv t) O (hzv t) (g a)).snd := by
    intro c0
    obtain ⟨wf, hdef, hlw⟩ := GlobalTheory.T.exists_dualNumber_deformation_lift_modification M z ho hz (w c0) (hw c0)
    obtain ⟨Mx, hMx, -⟩ := hQ.existsUnique hdef.isTanX
    obtain ⟨C, hC⟩ := GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho hQ hz hv hl hdef hMx hlw
    refine ⟨Sum.elim Mx C, fun a => ?_⟩
    rw [hC O (g a) (hwO c0) hzv, Fintype.sum_sum_type]
    rfl
  choose C hC using hspan
  have hmat : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) *
        Matrix.of (fun b c0 => C c0 (tanOrd Dw b)) := by
    ext a c0
    rw [Matrix.mul_apply, Matrix.of_apply, hC c0 a, ← Equiv.sum_comp (tanOrd Dw)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.of_apply]
    ring
  intro h0
  apply hdg
  rw [hmat, Matrix.det_mul, h0, zero_mul]

end
