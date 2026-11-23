import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

theorem frBor_genDiag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s' : LB.Sec (PPx y.x)) (hs' : GlobalTheory.Frames.SecGen y.x s') (a : Sˣ)
    (h : ∀ i, s'.f i = scal y.x (a : S) i * y.s.f i) :
    FrBor (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag Dw a) y { y with s := s', gen := hs' } := by
  refine ⟨rfl, fun τ i => ⟨(1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i, Matrix.one_apply_eq i,
    fun j hij => Matrix.one_apply_ne hij.ne, (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y y).1.2.1 τ i⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i hi => ?_⟩
  refine Eq.trans ?_ (h i).symm
  exact congrArg (fun m => CommRingCat.Hom.hom m (scal y.x (a : S) i * y.s.f i))
    ((Gx y.x).presheaf.map_id (Opposite.op ((PPx y.x).U i)))

set_option maxHeartbeats 1000000 in

theorem evR_eq_of_reads_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → (∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z) → ∀ (θ : (Fin g → ℂ) → ℂ) (t : ℂ), A.Reads 1 y.s θ → A'.Reads 1 y'.s (t • θ) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = t ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' _ _ _ hex hfr θ t hR hR' a n f hf
  have hx : y'.x = y.x := (Over.w (A'.ex 0)).symm.trans
    ((congrArg (· ≫ Xo.univ.t.G.hom) (hex 0)).trans (Over.w (A.ex 0)))
  have hu : y'.u = y.u := funext fun τ => funext fun i =>
    GlobalTheory.PointUnif.deriv_unique (by simpa only [hex] using A'.der ⟨τ, i⟩) (A.der ⟨τ, i⟩)
  obtain ⟨x', ho', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hu
  subst hx hu
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have V := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo y.x
  have key : ∀ i (pt : Sp ℂ ⟶ Gx y.x), pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ →
      valAt' pt ((PPx y.x).U i) (s'.f i) = t * valAt' pt ((PPx y.x).U i) (y.s.f i) := by
    intro i pt hp
    by_cases hi : ⊤ ≤ pt ⁻¹ᵁ (PPx y.x).U i
    · have hw : (pt ≫ Formalism.L2.PjFree.gxFst y.x) ≫ Xo.univ.t.G.hom = y.x := by
        have h1 := Over.w (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G)
        have h2 := Over.w (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G)
        refine (Category.assoc _ _ _).trans ((congrArg (pt ≫ ·) (h1.trans h2.symm)).trans ?_)
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) hp).trans (Category.id_comp _))
      obtain ⟨z, hz⟩ := A.ex_onto (Over.homMk (pt ≫ Formalism.L2.PjFree.gxFst y.x) hw)
      have hz' : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left := (congrArg (·.left) hz).symm
      obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => congrArg i (Fin.fin_one_eq_zero q)⟩
      have hj : ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
        rw [← hz']
        exact fun q hq => Set.mem_iInter.1 (hi hq) 0
      have e1 := hR j z pt hz' hp hj
      have e2 := hR' j z pt (hz'.trans (hex z).symm) hp (by rw [hex]; exact hj)
      rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc] at e2
      exact e2.trans (congrArg (t * ·) e1.symm)
    · rw [ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, mul_zero]
  have ht : t ≠ 0 := by
    obtain ⟨i, pt, hp, hv⟩ := (V s').2.1.1 gen'
    exact fun h0 => hv (by rw [key i pt hp, h0, zero_mul])
  obtain ⟨b, hb, -⟩ := y.gen s'
  have hbt : b = t := by
    obtain ⟨i, pt, hp, hv⟩ := (V y.s).2.1.1 y.gen
    refine mul_right_cancel₀ hv ?_
    rw [← key i pt hp, hb i, (V y.s).1 b i pt hp]
  subst hbt
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hw := (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 a n f hf ℂ _ y _ (hA ℂ y) (hA ℂ _)
    (frBor_genDiag y s' gen' (Units.mk0 b ht) hb)
  refine hw.trans (congrArg (· * evR Xo c f y) ?_)
  unfold wchar
  rw [Fintype.prod_option]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag, ex]

end GlobalTheory.FrameEquiv
