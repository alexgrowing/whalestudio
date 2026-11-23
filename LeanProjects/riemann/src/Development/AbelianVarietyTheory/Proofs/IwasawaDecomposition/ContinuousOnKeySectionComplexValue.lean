import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAtScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchEqOneOfWchar
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {M : ModelsOf F r}

theorem exists_isThetaPt_of_adapted {k : Fin F.n} (T : ThetaData e F M k) (x : Fin T.m → ℂ)
    (hx : x ∈ T.co ⁻¹' (M.X k).dom) (y : FrPt Xo c (CAt σ)) (h₁ : y.x = F.u k (T.Pf (T.co x)))
    (h₂ : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co x)) z).left)
      (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) :
    ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt T x a y := by
  obtain ⟨hu, hsym, hpos, -⟩ := T.norm x hx
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨t, ht⟩ := T.fr_sec x hx
  obtain ⟨a, ha, hv⟩ := GlobalTheory.GenFactor.exists_factor GlobalTheory.abelianSchemeLaws_all.2.secTwist y.x _ h₁ y.s y.gen
    (F.ex k (T.Pf (T.co x))) (fun z => thetaChar (T.ta x) T.c₁ T.c₂ (T.h x *ᵥ z)) (fun j z => T.fr j (x, z))
    ⟨(T.h x)⁻¹ *ᵥ w, by
      show thetaChar _ _ _ (T.h x *ᵥ ((T.h x)⁻¹ *ᵥ w)) ≠ 0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩
    (fun j z hz => T.fr_ne j x z hx hz) t ht
  exact ⟨a, ha, h₁, h₂, hv⟩

theorem rootVal_of_isThetaPt {k : Fin F.n} (T : ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : IsNormUn T (un k)) (x : Fin T.m → ℂ) (hx : x ∈ T.co ⁻¹' (M.X k).dom) (a : ℂ) (ha : a ≠ 0)
    (y : FrPt Xo c (CAt σ)) (hy : IsThetaPt T x a y) :
    RootVal (unfOf e F M un) y
      ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h x).det / a ^ 2) := by
  obtain ⟨κ, hκ, hθ⟩ := hun ⟨T.co x, hx⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hκ hθ
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC (T.norm _ hx).1.ne_zero (by rw [← hκ, h0]; simp)
  let t₀ : ℂˣ := Units.mk0 (a / κ) (div_ne_zero ha k1)
  have hb := GlobalTheory.frBor_of_isThetaPt GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ g e F r M k T x hx κ
    (show (CAt σ)ˣ from t₀) (un k ⟨T.co x, hx⟩) y hθ (by
      have : a / κ * κ = a := div_mul_cancel₀ a k1
      show IsThetaPt T x (a / κ * κ) y
      rwa [this])
  refine ⟨k, ⟨T.co x, hx⟩, _, hb, ?_⟩
  have hk : kch (Dw := Dw) (S := ℂ) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ ^ 2)⁻¹ := by
    rw [kch_eq]
    simp
  refine Eq.trans ?_ (congrArg Units.val hk).symm
  rw [← hκ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  field_simp

end

theorem continuousOn_rootVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M T un hσ hM hξ hun hok A _ _ yA m B φ y ρ hB hφ hy hρ b₀ hb₀
  obtain ⟨B', k, P, hB', hb', hsub, hP, hd⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨x, hx, hxc⟩ :=
    GlobalTheory.FrameLiftAt.exists_frame_lift E H Dw l Xo c σ g e F r M k (T k) hσ hM hξ m B' P hB' hP b₀ hb'
  have h₁ : ∀ b ∈ B', ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt (T k) (x b) a (y b) := fun b hb =>
    exists_isThetaPt_of_adapted (T k) (x b) (hx b hb).1 (y b) (by rw [(hx b hb).2]; exact (hd b hb).1)
      (by rw [(hx b hb).2]; exact (hd b hb).2)
  choose! a ha hθ using h₁
  have hac : ContinuousAt a b₀ :=
    GlobalTheory.ThetaScalar.continuousAt_scalar E H Dw l Xo c σ g e F r M k (T k) A yA m B' φ y P x a hB'
      (fun t => (hφ t).mono hsub) (fun b hb => hy b (hsub hb)) hP
      (fun b hb => ⟨(hx b hb).1, (hx b hb).2, hθ b hb⟩) b₀ hb' hxc
  have hO : IsOpen ((T k).co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom _).preimage (T k).co.continuous
  have hh : ContinuousAt (T k).h (x b₀) := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    ((T k).hol i j).1.continuousOn.continuousAt (hO.mem_nhds (hx b₀ hb').1)
  have hdet : ContinuousAt (fun b => ((T k).h (x b)).det) b₀ :=
    (continuous_id.matrix_det.continuousAt).comp (ContinuousAt.comp hh hxc)
  have hq : ContinuousAt (fun b => (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      ((T k).h (x b)).det / a b ^ 2) b₀ :=
    (continuousAt_const.mul hdet).div (hac.pow 2) (pow_ne_zero 2 (ha b₀ hb'))
  refine (hq.congr ?_).continuousWithinAt
  filter_upwards [hB'.mem_nhds hb'] with b hb
  exact rootVal_unique E H Dw l Xo c σ g e F r M un hσ hM hξ hok (y b) _ _
    (rootVal_of_isThetaPt (T k) un (hun k) (x b) (hx b hb).1 (a b) (ha b hb) (y b) (hθ b hb)) (hρ b (hsub hb))

end GlobalTheory.KeyFourth
