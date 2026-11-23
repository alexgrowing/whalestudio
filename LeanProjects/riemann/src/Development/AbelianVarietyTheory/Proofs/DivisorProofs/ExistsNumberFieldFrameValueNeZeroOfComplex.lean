import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameDenseZ

open Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT in

theorem exists_poly_div_det_secZ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    (e : Ix Dw → ℤ) (F : Rul Xo c) (hF : F ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S)
      (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)),
      (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := GlobalTheory.LamT.RatFn.exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.FrameDenseZ

namespace GlobalTheory.FrameDenseZ

open Formalism.L2.LamCM in

theorem exists_frame_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] (m : B → ℕ)
    (P : MvPolynomial (FrVar m) K) (hP : P ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr P Y ≠ 0 := by
  classical
  have hD : ∀ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 := by
    intro b h
    have := GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly (K := K) m b (fun _ => 1)
    rw [h] at this
    simp [evalFr] at this
  have hQ : P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 :=
    mul_ne_zero hP (Finset.prod_ne_zero_iff.2 fun b _ => hD b)
  obtain ⟨v, hv⟩ : ∃ v : FrVar m → K,
      MvPolynomial.eval v (P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ (MvPolynomial.funext fun x => by simp only [h x, map_zero])
  let Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => v ⟨b, (j, i)⟩
  have hY : ∀ R : MvPolynomial (FrVar m) K, evalFr R Y = MvPolynomial.eval v R := fun R => rfl
  rw [map_mul, map_prod] at hv
  refine ⟨Y, fun b => ?_, ?_⟩
  · rw [← GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly m b Y, hY]
    exact (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hv)) b (Finset.mem_univ b)
  · rw [hY]
    exact left_ne_zero_of_mul hv

theorem exists_frame_evR_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y e F hF σ σ₁ w hw hne
  classical
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_secZ E H Dw l Xo c K y e F hF
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hP0 : P ≠ 0 := by
    intro hP0
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ :=
      (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e' : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e'
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
      ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
    have hv := hP _ σ₁ z z1 (fun b => (g b).transpose)
      (fun b => by rw [Matrix.det_transpose]; exact hg b) hz
      (by simpa only [Matrix.transpose_transpose] using h1)
    rw [hP0, map_zero] at hv
    have hz1 : evR Xo c F z1 = 0 := by
      have hdet : (∏ b, ((g b).transpose).det) ^ N ≠ 0 :=
        pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun b _ => by
          rw [Matrix.det_transpose]; exact (hg b).ne_zero)
      have h00 : Formalism.L2.LamCM.evalFr (0 : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) (CAt σ))
          (fun b => (g b).transpose) = 0 := by simp [Formalism.L2.LamCM.evalFr]
      rw [h00] at hv
      exact (mul_eq_zero.1 hv).resolve_left hdet
    apply hne
    rw [GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF (CAt σ) t z1 z2 hb, hz1, mul_zero]
  obtain ⟨Y, hYd, hYv⟩ := exists_frame_evalFr_ne_zero Dw.mult P hP0
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hYd b).isUnit)
  refine ⟨y', hy'.1, fun h0 => hYv ?_⟩
  have hv := hP K (AlgHom.id c.F K) y y' Y (fun b => (hYd b).isUnit)
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y).2.1 hy'
  rw [h0, mul_zero, show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at hv
  exact hv.symm

end GlobalTheory.FrameDenseZ
