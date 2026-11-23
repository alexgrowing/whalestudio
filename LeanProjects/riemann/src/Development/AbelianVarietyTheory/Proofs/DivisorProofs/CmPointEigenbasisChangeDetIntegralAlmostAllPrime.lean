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
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDivLeOneCofiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLettersIntegralLieBasisEigenframeRelationStatement
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
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

theorem GlobalTheory.DetInt.det_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S, ∀ (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
        (∏ b, (g b).det) ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_valuation_div_le_one_of_isLocGen z.K z.LamL.I z.U.det
  refine ⟨S, fun p hp T iK _hfin hval M => ?_⟩
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨A, hA, hloc⟩ := hz.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  obtain ⟨nu, mu, C, hCint, hU, hAmu, hC⟩ :=
    GlobalTheory.T.tangent_letters_integralLieBasis_eigenframe_relation E H Dw l Xo c z f La hz p T iK M hval A hA φ yT y' g a hφ hmap hchg hg hint
  let Cv : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) T.V := Matrix.of fun i k => (hCint (z.e.symm i) k).choose
  have hCv : Cv.map (algebraMap T.V T.Fr) = Matrix.of fun i k => C (z.e.symm i) k := by
    ext i k; exact (hCint (z.e.symm i) k).choose_spec
  obtain ⟨hUdet, hdet⟩ := GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit Dw.mult z.e (fullB yT) (ReciprocityTheory.ChartRestriction.G.PullbackSections.fullB_basis yT) nu mu
    (z.U.map iK) (A.map iK) C g (by simpa using hU) (by simpa using hAmu) hC
  have e1 : (z.U.map iK).det = iK z.U.det := (RingHom.map_det iK z.U).symm
  have e2 : (A.map iK).det = iK A.det := (RingHom.map_det iK A).symm
  have e3 : (Cv.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr Cv.det := (RingHom.map_det _ Cv).symm
  rw [e1] at hUdet hdet
  rw [e2] at hdet
  have hU0 : z.U.det ≠ 0 := fun h => hUdet (by rw [h, map_zero])
  obtain ⟨r, hr⟩ := (hval _).2 (hS p hp A.det hloc hU0)
  refine ⟨Cv.det * r, ?_⟩
  rw [map_mul, ← e3, hCv, hr, map_div₀, ← mul_div_assoc, div_eq_iff hUdet, hdet]
