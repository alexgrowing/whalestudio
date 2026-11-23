import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

open AlgebraicGeometry CategoryTheory in

theorem GlobalTheory.OneMapRef.exists_scalar_of_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y') (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ th th', A.Reads 1 y.s th → A'.Reads 1 y'.s th' → ∃ lam : ℂ, lam ≠ 0 ∧ th' = lam • th ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L hs hx hL hA y y' A A' mk hmk hm hm' th th' hr hr'
  have he := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm'
  have hfr := GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL he
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have hu : y'.u = y.u := funext fun τ => funext fun i => by
    have d := A'.der ⟨τ, i⟩
    simp only [he] at d
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique d (A.der ⟨τ, i⟩)
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hyx hu
  subst hyx hu
  obtain ⟨a, ha⟩ := GlobalTheory.Frames.ChgOf.gen_unit' y.s s' y.gen gen'
  refine ⟨a, a.ne_zero, ?_, fun w n f hf => ?_⟩
  · refine (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L _ A' hs hx hL 1 s').1.unique hr' ?_
    intro j z pt h1 h2 hj
    rw [he] at h1 hj
    have h3 := hr j z pt h1 h2 hj
    have h4 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1
      a (fun _ => j) pt h2
    refine ((congrArg (Geo.Tor.valAt' pt _) (ha fun _ => j)).trans h4).trans ?_
    rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact congrArg _ h3
  · let t : Formalism.L2.Pj.Ix Dw → ℂˣ := fun i => match i with
      | none => a
      | some _ => 1
    refine (GlobalTheory.LamT.evR_frChg_tri (inferInstance) hf t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) (y := y)
      (y' := ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩)
      ⟨rfl, ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c ℂ y y y).1).2.1,
        (GlobalTheory.Frames.ChgOf.secBC_id_iff y.x _ y.s s').2 ha⟩).trans ?_
    congr 1
    simp [wchar, Fintype.prod_option, t, Formalism.L2.Pj.ex]
