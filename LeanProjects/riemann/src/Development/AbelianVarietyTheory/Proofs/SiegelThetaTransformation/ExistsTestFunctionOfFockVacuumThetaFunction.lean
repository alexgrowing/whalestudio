import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsThetaEqOfTranslationInvariantMultipleStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOnto

theorem differentiable_of_fderiv_I {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Φ : V → ℂ}
    (h : Differentiable ℝ Φ) (hI : ∀ z u, fderiv ℝ Φ z (I • u) = I * fderiv ℝ Φ z u) : Differentiable ℂ Φ := by
  intro z
  have hs : ∀ (c : ℂ) (u : V), fderiv ℝ Φ z (c • u) = c * fderiv ℝ Φ z u := by
    intro c u
    have e : c • u = c.re • u + c.im • (I • u) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    rw [e, map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul, ← mul_assoc, ← add_mul,
      Complex.re_add_im]
  let A : V →L[ℂ] ℂ :=
    { toFun := fderiv ℝ Φ z
      map_add' := map_add _
      map_smul' := hs
      cont := (fderiv ℝ Φ z).continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := A) (h z).hasFDerivAt (by ext; rfl)).differentiableAt

variable {D : D7} {S T : HSp D}

theorem differentiable_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (R : V →+ WO S T)
    (hR : Continuous R) (hr : ∀ v, IsRealPt (R v)) : Differentiable ℝ fun v => f (R v) := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  have h1 := hf.smooth _ (R.comp e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom) (hR.comp e.symm.continuous)
    (fun t => hr _) 0
  have h2 := (h1.differentiable (by simp)).comp e.differentiable
  refine (funext fun v => ?_ : (fun v => f (R v)) = _) ▸ h2
  change f (R v) = f (0 + R (e.symm (e v)))
  rw [zero_add, e.symm_apply_apply]

theorem finW_neg_nsmul (N : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (-(N • y)) = N • finW S T (-y) := by
  have key : ∀ {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] (p : A) (x : E),
      p ⊗ₜ[F] (-(N • x)) = N • (p ⊗ₜ[F] (-x)) := by
    intro F A E _ _ _ _ _ p x
    rw [← smul_neg]
    exact map_nsmul (TensorProduct.mk F A E p) N (-x)
  funext a k
  exact key (pairA D.host.F 0 1) (y k a)

theorem finW_mem_hatA {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    {y : Matrix (Fin S.rank) (Fin T.rank) D.host.E} (hy : y ∈ A) : finW S T y ∈ hatA S T A :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, y, hy, rfl⟩

theorem isRealPt_sub (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    IsRealPt (S := S) (T := T) (ratW T S yᵀ - finW S T y) := by
  ext a k
  change finPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (C : Ctx S T) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
  funext σ k a
  change conj (C.θ (C.m.e.symm σ) (infPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a))) =
    σ.1 (y k a)
  have h0 : infPart D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0 := by
    have : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
    rw [this, TensorProduct.zero_tmul]
  have h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
  have h2 := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at h2
  rw [RingHom.map_sub, h0, h1, sub_zero, (C.inf _).1, h2, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.Ker.FockOnto

open GlobalTheory.Ker.FockOnto in

theorem GlobalTheory.Ker.exists_test_of_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ := by
  intro D S T C B hB f hf hF
  obtain ⟨R, hRc, -, hadd, hR, hR', -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx
  have hg0 : ∀ z : Fin S.rank → Fin C.g → ℂ, gaussR C.X C.bas C.idx (C.xB B) z ≠ 0 := fun z => Complex.exp_ne_zero _
  set Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ := fun z => (gaussR C.X C.bas C.idx (C.xB B) z)⁻¹ * f (R (L.symm z))
    with hΦ
  have hd : Differentiable ℝ Φ :=
    (((RealHeis.contDiff_gaussR C.X C.bas C.idx (C.xB B)).differentiable (by simp)).inv hg0).mul
      ((differentiable_comp hf R hRc fun v => (hR v).1).comp L.symm.differentiable)
  have hv : ∀ v, f (R v) = gaussR C.X C.bas C.idx (C.xB B) (zR C.X C.idx (C.xB B) v) *
      Φ (zR C.X C.idx (C.xB B) v) := by
    intro v
    simp only [hΦ]
    rw [mul_inv_cancel_left₀ (hg0 _), ← hL, L.symm_apply_apply]
  have hw : ∀ w, IsRealPt w → f w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w) := by
    intro w hw
    rw [Ctx.zOf, ← hv, hR' w hw]
  have hone : ∀ ζ (σ : C.X.Ψ) (c : Fin S.rank → Fin T.rank → ℂ),
      fderiv ℝ Φ ζ (I • L (Pi.single σ c)) = I * fderiv ℝ Φ ζ (L (Pi.single σ c)) := by
    intro ζ σ c
    have h1 := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB f Φ hd hw (C.m.e.symm σ) (Matrix.of fun a k => conj (c k a))
      (L (Pi.single σ c)) (by simp [hL]) (R (L.symm ζ)) (hR _).1).1
    have h2 : C.zOf (C.xB B) (R (L.symm ζ)) = ζ := by rw [Ctx.zOf, (hR _).2, ← hL, L.apply_symm_apply]
    rw [hF, h2, Pi.zero_apply] at h1
    have h3 := (mul_eq_zero.1 h1.symm).resolve_left (hg0 _)
    linear_combination (-I) * h3 + (fderiv ℝ Φ ζ (I • L (Pi.single σ c))) * Complex.I_mul_I
  have hC : Differentiable ℂ Φ := by
    refine differentiable_of_fderiv_I hd fun ζ u => ?_
    obtain ⟨v, rfl⟩ := L.surjective u
    rw [← Finset.univ_sum_single v, map_sum, Finset.smul_sum, map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => hone ζ σ _
  obtain ⟨-, hext, hth⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  obtain ⟨-, -, -, hfin, -, N, hN, hlev⟩ := hth f hf
  obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.T.exists_theta_eq_of_translation_invariant_multiple D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx N hN
    Φ hC (by
      intro y hy v
      have h1 := hfin (-(N • y)) (R v) (hR v).1
      have h2 : embR C.X (-(N • y)) = -(N • embR C.X y) := by
        funext σ k a
        simp [embR]
      have h3 : ratW T S (-(N • y))ᵀ - finW S T (-(N • y)) = R (-(N • embR C.X y)) := by
        rw [← hR' _ (isRealPt_sub _), realPt_sub, h2]
      have h4 : EFR C.X v (-(N • embR C.X y)) = -EFR C.X v (N • embR C.X y) := by
        generalize N • embR C.X y = a
        simp only [EFR, hermC, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re, neg_mul,
          neg_neg]
      rw [h3, finW_neg_nsmul, hlev _ (finW_mem_hatA (neg_mem ((TensLat.mem_tens_stdL _ _).2 hy))), (hR v).2, h2,
        ← map_sub, sub_neg_eq_add, h4, hv, hv] at h1
      rw [h1]
      simp)
  refine ⟨φ, hφ, (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).2 f ⟨hf, fun w hw' => ?_⟩⟩
  rw [hw w hw', thR, hθ, Ctx.zOf]
