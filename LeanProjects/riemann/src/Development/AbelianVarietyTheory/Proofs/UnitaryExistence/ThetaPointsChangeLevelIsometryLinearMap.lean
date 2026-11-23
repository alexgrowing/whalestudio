import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFrameDetMulSqInvariantUncond
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaPtChg

theorem exists_chart_point {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hq : p q ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
  refine ⟨j, fun q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact hj

theorem val_of_secBC (hS : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    (x x' : Sp ℂ ⟶ Xo.X) (hx : x' = x) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ)
    (h : SecBC (RingHom.id ℂ) a x x' s s') (p : Over.mk x ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι) (v v' : ℂ)
    (hv : ∀ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = p.left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = v)
    (hv' : ∀ pt : Sp ℂ ⟶ Gx x', pt ≫ gxFst x' = p.left → pt ≫ gxSnd x' = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) = v') : v' = a * v := by
  subst hx
  have hid : x' = spMap (RingHom.id ℂ) ≫ x' := by
    simp [spMap]
  have h2 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x' x' x' hid hid).2.1
    a s s').1 h
  let pt : Sp ℂ ⟶ Gx x' := (CartesianMonoidalCategory.lift (𝟙 (Over.mk x')) p).left
  have e1 : pt ≫ gxFst x' = p.left := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk x')) p)
    exact this
  have e2 : pt ≫ gxSnd x' = 𝟙 (Sp ℂ) := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk x')) p)
    exact this
  rw [← hv pt e1 e2, ← hv' pt e1 e2]
  exact (congrArg (valAt' pt ((PPx x').U (fun _ => j))) (h2 (fun _ => j))).trans
    ((GlobalTheory.sec_values_complex_fibre hS E H Dw l Xo x' s).1 a _ pt e2)

theorem thetaPt_change : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y y' gam h₀ hy hy' hgam hP
  obtain ⟨hg1, hg2, hg3⟩ := hgam
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k
    (T.Pf (T.co b)) (T.Pf (T.co b')) gam h₀ hp hp' hg1 hg2 hg3 hP
  have hx : y'.x = y.x := hy'.1.trans (hu.symm.trans hy.1.symm)
  refine ⟨hx, fun τ i => ?_, ?_⟩
  · refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k (T.Pf (T.co b)) hp k (T.Pf (T.co b')) (Matrix.mulVecLin h₀) hp'
      hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy'.2.1 τ i
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  refine ⟨a, hbc, ?_⟩
  obtain ⟨hhd, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨z, hz⟩ : ∃ z, T.h b *ᵥ z = w :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hhd, Matrix.one_mulVec]⟩
  obtain ⟨j, hj⟩ := exists_chart_point Xo.univ.t.PP.isLB (F.ex k (T.Pf (T.co b)) z).left
  have hmult := GlobalTheory.thetaFrame_det_mul_sq_invariant_uncond E H Dw l Xo _ g _ F k T.m (T.co ⁻¹' (M.X k).dom)
    (fun b => T.Pf (T.co b)) T.bas T.h T.ta T.c₁ T.c₂ T.fr (fun b hb => T.isPer _ hb) T.sympl T.adapt
    (fun b hb => (T.norm b hb).2.2.2) T.half₁ T.half₂ T.fr_hol T.fr_ne T.fr_coc T.fr_rig T.fr_sec
    b hb b' hb' gam h₀ hg1 hg2 hg3 hP j z hj
  have hne : thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) ≠ 0 :=
    mul_ne_zero (by rw [hz]; exact hw) (T.fr_ne j b z hb hj)
  have hw0 : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) :=
    (Over.w (F.ex k (T.Pf (T.co b)) z)).trans hy.1.symm
  have hval := val_of_secBC hS (Xo := Xo) y.x y'.x hx y.s y'.s (toC (a : CAt σ)) hbc
    (Over.homMk (F.ex k (T.Pf (T.co b)) z).left hw0) j _ _
    (fun pt h1 h2 => hy.2.2 j z pt h1 h2 hj)
    (fun pt h1 h2 => hy'.2.2 j (h₀ *ᵥ z) pt (h1.trans (hex z).symm) h2 (by rw [hex z]; exact hj))
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [mul_assoc κ', mul_assoc κ] at hval
  generalize thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) = S at *
  generalize thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ (h₀ *ᵥ z)) * T.fr j (b', h₀ *ᵥ z) = S' at *
  linear_combination (-κ' ^ 2) * hmult - (T.h b').det * h₀.det * (κ' * S' + toC (a : CAt σ) * (κ * S)) * hval

end GlobalTheory.ThetaPtChg
