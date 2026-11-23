import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries
open CategoryTheory

noncomputable section

namespace GlobalTheory.CoverFibScalar

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.Dict.Lift
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem anFib_of_eq_marked (σ : c.F →+* ℂ) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ), y'.x = y.x → y'.u = y.u → ∃ t : ℂ, t ≠ 0 ∧
      (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = t ^ n * evR Xo c f y) ∧
      ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
        (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (A' : AnFib X bas idx e x L y'),
        ∃ A : AnFib X bas idx e x L y, (∀ mk, A'.Marked mk → A.Marked mk) ∧
          ∀ θ, A'.Reads 1 y'.s θ → A.Reads 1 y.s (fun z => t⁻¹ * θ z) := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' hx hu
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  subst hu
  obtain ⟨u0, hu0⟩ := GlobalTheory.CongrOrbit.exists_unit_of_generators (x := y.x) y.s s' y.gen gen'
  refine ⟨u0, u0.ne_zero, fun a n f hf => ?_, fun r g X bas idx e x L A => ⟨⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker,
    A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm, A.fr_per⟩, fun mk h => h,
    fun θ hθ j z pt h1 h2 h => ?_⟩⟩
  · obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo ℂ y.x
    have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
    choose b hb using hb
    have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
    have hB : FrBor (fun o : Ix Dw => o.elim u0 fun _ => 1) y ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩ := by
      refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩,
        𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
      · dsimp only
        rw [hu τ, hcomb]
        simp [Pi.single_apply]
      · intro i h
        simp only
        rw [hu0 i]
        simp only [Scheme.Hom.appLE]
        have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
        rw [e]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        rfl
    rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 ℂ inferInstance a n f hf _ _ _ hB]
    congr 1
    simp [wchar, Fintype.prod_option, ex]
  · have v1 := hθ j z pt h1 h2 h
    have v2 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1 (u0 : ℂ)
      (fun _ => j) pt h2
    have v3 := (congrArg (valAt' pt ((PPx y.x).U (fun _ => j))) (hu0 (fun _ => j))).trans v2
    have v4 := v1.symm.trans v3
    change valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f fun _ => j) = _
    rw [_root_.mul_assoc, v4, inv_mul_cancel_left₀ u0.ne_zero]

end Geo

end GlobalTheory.CoverFibScalar

namespace GlobalTheory.CoverFibScalar

open GlobalTheory.CoverFrameMod (midEmb)

set_option maxHeartbeats 1600000 in

theorem exists_scalar_fib : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.d.IsLev → C.σ₂.comp C.inc = σ → ∀ (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂)), (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X) → (∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ = (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) → ∃ t : ℂ, t ≠ 0 ∧ (∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂, C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y)) ∧ ∀ (r g : ℕ) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 (T.Q.Dw j)) (x : Frame X.Ψ r) (L : Lt D.host.E r) (mk : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ ϑ : (Fin g → ℂ) → ℂ, (letI : Algebra T.Q.c.F ℂ := σ.toAlgebra; ∃ A : AnFib X bas idx e x L y, A.Marked mk ∧ A.Reads 1 y.s ϑ) → (letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra; ∃ A₂ : AnFib X bas idx e x L y₂, A₂.Reads 1 y₂.s (fun z => t * ϑ z)) := by
  intro D T j σ C hlev hσ y y₂ hx hu
  letI a₂ : Algebra C.d.c₂.F (CAt (midEmb C)) := RingHom.toAlgebra (R := C.d.c₂.F) (S := CAt (midEmb C)) C.σ₂
  letI a₀ : Algebra T.Q.c.F (CAt (midEmb C)) := RingHom.toAlgebra (R := T.Q.c.F) (S := CAt (midEmb C)) σ
  have hov : AlgOver T.Q.c C.c' C.hle (CAt (midEmb C)) := fun a => DFunLike.congr_fun hσ a
  have hc : ∀ a : C.c'.F, algebraMap C.d.c₂.F (CAt (midEmb C)) (C.d.eF a) = algebraMap C.c'.F (CAt (midEmb C)) a :=
    fun _ => rfl
  let y₀ : FrPt (T.Q.Xo j) T.Q.c (CAt (midEmb C)) := y
  let z : FrPt (T.Q.Xo j) C.c' (CAt (midEmb C)) := FrPt.ext C.hle hov y₀
  let w : FrPt C.d.Xo₂ C.d.c₂ (CAt (midEmb C)) := y₂
  obtain ⟨y', hy'⟩ := GlobalTheory.CoverSec.exists_frOver_below C.d hc w
    ((CategoryTheory.Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (T.Q.Xo j).s) hx).trans z.x_over))
  have ex' : y₀.x = (y'.res C.hle hov).x := (hy'.1.symm.trans hx).symm
  have eu' : y₀.u = (y'.res C.hle hov).u :=
    (funext fun τ => funext fun i => (hy'.2.1 τ i).symm.trans (hu τ i)).symm
  let y₁ : FrPt (T.Q.Xo j) T.Q.c (CAt (midEmb C)) := y'.res C.hle hov
  obtain ⟨u, hu0, hval, hfib⟩ := anFib_of_eq_marked σ y₁ y₀ ex' eu'
  refine ⟨u⁻¹, inv_ne_zero hu0, fun n a f hf f₂ hp => ?_, fun r g X bas idx e x L mk hsym hxd hL ϑ hA => ?_⟩
  · have h1 := @hp (CAt (midEmb C)) (inferInstanceAs (Field ℂ)) a₀
      (inferInstanceAs (Algebra C.c'.F (CAt (midEmb C)))) a₂ hov hc w y' hy'
    have h2 := hval a n f hf
    refine (congrArg toC h1).trans ?_
    have e2 : toC (evR (T.Q.Xo j) T.Q.c f y) = u ^ n * toC (evR (T.Q.Xo j) T.Q.c f y₁) := h2
    rw [e2, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu0, one_pow, one_mul]
    rfl
  · letI : Algebra T.Q.c.F ℂ := σ.toAlgebra
    obtain ⟨A, hmk, hr⟩ := hA
    obtain ⟨A₁, hm₁, hr₁⟩ := hfib r g X bas idx e x L A
    letI : Algebra C.c'.F ℂ := (midEmb C).toAlgebra
    letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra
    let A₁' : AnFib X bas idx e x L (y' : FrPt (T.Q.Xo j) C.c' ℂ) :=
      ⟨A₁.ex, A₁.ex_add, A₁.ex_onto, A₁.ex_ker, A₁.ex_lin, A₁.hol, A₁.der, A₁.fr, A₁.fr_hol, A₁.fr_ne, A₁.fr_g,
        A₁.fr_0, A₁.χ, A₁.χ_norm, A₁.fr_per⟩
    obtain ⟨A₂, hr₂, -⟩ := GlobalTheory.Dict.Lift.anFib_lift _ _ _ _ (T.Q.Xo j) C.c' 0 C.d (fun _ => rfl) hlev r g X bas idx e x
      L (y' : FrPt (T.Q.Xo j) C.c' ℂ) A₁' hsym hxd hL (w : FrPt C.d.Xo₂ C.d.c₂ ℂ) hy' mk (hm₁ mk hmk)
    exact ⟨A₂, hr₂ _ (hr₁ ϑ hr)⟩

end GlobalTheory.CoverFibScalar
