import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.HeightsOfFormMix
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.CombLineSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimClosureGenericPt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VertEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombinationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOnStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsFurther
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmoothStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine isSmoothHerm_powLine isSmoothHerm_constLine)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.ArithmeticHeightTower.FormZc

open ReciprocityTheory.ChartRestriction.G.Geo.ResK (ResKStatement) in

theorem formZ_direct :
    Geo.ArithIntersectionSystemStatement → ResKStatement → GlobalTheory.ArithmeticHeightTower.FormZ := by
  rintro ⟨II, hII⟩ hK m n X _ i _ D hX ι _ M tM
  have h₈ := GlobalTheory.T.archimedean_integrable_on hK
  have h₇ := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable h₈
  have hR := GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK hK
  have h₃ := GlobalTheory.CompanionTheory.MixZ.ptDict
  choose A sA RA cA using fun j => GlobalTheory.CompanionTheory.MixZ.existsRead m n (M j) (tM j)
  have hc := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n X i (D + 1) hX.dim_eq
  have hhor : IsHorizontal (ptIdeal (i (genericPoint X))) := hp₃.2 hc
  have hP := hp₄ hhor
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.CompanionTheory.Polarisation.exists_form ι D
    (fun f => II (Fin (m + 1)) (Bk n) (ptIdeal (i (genericPoint X))) (D + 1) (A ∘ f))
    (fun f s => (hII.1 _ _).1 _ _ (A ∘ f) s hP fun _ => sA _)
  refine ⟨Φ, fun a => ?_, h0⟩
  have Rc := GlobalTheory.CompanionTheory.MixZ.readComb m n ι M A RA a
  have sC := isSmoothHerm_combLine sA a
  have H := exists_height h₃ codimOne_holds GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational h₇ h₈ GlobalTheory.CompanionTheory.MixZ.Vert.vertEq GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen curveInt hR II hII
    (comb M a) (combLine A a) Rc sC
  refine ⟨_, (isometric_comb_pull M a i rfl).symm.isArithHeight hX (H.restrict (mp_var m n) i rfl), ?_⟩
  rw [htFn_eq II _ ((dim_of_generic i).trans hX.dim_eq), cycVal, if_pos hhor, hΦ]
  refine (expand_comb A sA cA (D + 1) (II (Fin (m + 1)) (Bk n) (ptIdeal (i (genericPoint X))) (D + 1))
    (fun L j B C hL hB hC => hII.2.1 _ _ _ _ L j B C hP hL hB hC) a)

end GlobalTheory.ArithmeticHeightTower.FormZc

namespace GlobalTheory.CompanionTheory.MixZ

theorem mixZ_direct :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.ArithmeticHeightTower.MixZ := by
  rintro ⟨II, hII⟩ hK
  have hR := GlobalTheory.T.rationality_of_resolution_statement hK
  have hI := GlobalTheory.T.archimedean_integrable_on hK
  have hE := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable hI
  exact mixZ_of GlobalTheory.T.mixed_cycle_read_exists GlobalTheory.T.mixed_cycle_read_combination GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE hI GlobalTheory.T.mixed_polarization_identity hR II hII
    (GlobalTheory.T.height_eq_of_full_intersection_system GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE GlobalTheory.CompanionTheory.MixZ.Vert.vertEq GlobalTheory.T.mixed_point_length_formula GlobalTheory.T.mixed_curve_intersection_formula hR II hII)

end GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem height_eq_direct : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (II : Geo.IntersectionSystem), Geo.IsFullIntersectionSystem II → ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → ∀ h : MP ℤ m n → ℝ, M.IsArithHeight h → ∀ (x : MP ℤ m n) (d : ℕ), Geo.IsArithVar (ptIdeal x) d → h x = II (Fin (m + 1)) (Bk n) (ptIdeal x) d (fun _ => A) := by
  intro hK II hII m n M A hA h H x d hd
  have hI := GlobalTheory.T.archimedean_integrable_on hK
  have hE := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable hI
  have hH : GlobalTheory.CompanionTheory.MixZ.HeightEq II := GlobalTheory.T.height_eq_of_full_intersection_system GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE GlobalTheory.CompanionTheory.MixZ.Vert.vertEq
    GlobalTheory.T.mixed_point_length_formula GlobalTheory.T.mixed_curve_intersection_formula (GlobalTheory.T.rationality_of_resolution_statement hK) II hII
  have hX := isArithVar_mpStr m n
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  haveI : IsNoetherian Z := hX.isNoetherian_sub i
  have e := hH m n M A hA (GlobalTheory.T.hermitian_line_bundle_smooth m n M A hA) Z i _ (H.restrict hX i rfl) (genericPoint Z) d
    ((GlobalTheory.CompanionTheory.MixZ.dim_closure_generic Z).trans (dim_of_isArithVar GlobalTheory.T.mixed_cycle_point_dictionary i hd))
  refine e.trans ?_
  rw [GlobalTheory.CompanionTheory.MixZ.cycVal]
  exact if_pos hd.2.2.1

theorem projQ_direct (hAIS : Geo.ArithIntersectionSystemStatement)
    (hK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : ProjQ := by
  obtain ⟨II, hII⟩ := hAIS
  intro n' m n Y _ j' _ e hvar hdim hdeg M hM h h' hh hh'
  let j : Y ⟶ MP ℤ (m + 1) (consN n' n) := j'
  haveI : IsClosedImmersion j := ‹IsClosedImmersion j'›
  obtain ⟨A, hA⟩ := GlobalTheory.CompanionTheory.MPDict.HermRep.exists_isHermRep m n M hM
  have hA' := GlobalTheory.CompanionTheory.MPDict.isHermRep_pull n' m n M A hA
  have hS := GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep m n M A hA
  haveI hc : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := charZero_genericPt hvar
  haveI hc' : CharZero ((MP ℤ m n).residueField (qpSnd n' m n (j (genericPoint Y)))) := charZero_image _ _ _ _
  have hP' : Geo.IsArithVar (ptIdeal (j (genericPoint Y))) (e + 1) :=
    GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal (m + 1) (consN n' n) _ _ hc (dim_closure_genericPt hvar)
  have hP : Geo.IsArithVar (ptIdeal (qpSnd n' m n (j (genericPoint Y)))) (e + 1) := GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal m n _ _ hc' hdim
  have e₁ := height_eq_direct hK II hII (m + 1) (consN n' n) _ _ hA' h' hh' _ _ hP'
  have e₂ := height_eq_direct hK II hII m n M A hA h hh _ _ hP
  have hi := GlobalTheory.CompanionTheory.MPDict.ProjImage.imageZ_ptIdeal n' m n (j (genericPoint Y))
  have pf := hII.2.2.1 (Fin (m + 1)) (Bk n) (Fin (m + 2)) (Bk (consN n' n)) Fin.succ (sv n' n)
    ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) (ptCoord (j (genericPoint Y))) (e + 1)
    (fun _ => A) (fun _ => pullLine n' A) (isBlockMap_sv n' n) hP' (by
      change Geo.IsArithVar (imageZ (sv n' n) (ptIdeal (j (genericPoint Y)))) (e + 1)
      rw [hi]; exact hP) (fun _ => hS)
    (fun _ => isPullHerm_pullLine n' A)
  have hd := GlobalTheory.CompanionTheory.MPDict.FnDeg.relfinrank_blockFnField_sv n' m n (j (genericPoint Y))
  have hd' : (IntermediateField.relfinrank (blockFnField (ptCoord (j (genericPoint Y)) ∘ sv n' n)) (blockFnField (ptCoord (j (genericPoint Y)))) : ℝ) = ((qpSnd n' m n).residueDegree (j (genericPoint Y)) : ℝ) := by
    exact_mod_cast hd
  rw [hd'] at pf
  change II _ _ (ptIdeal (j (genericPoint Y))) _ _ = _ * II _ _ (imageZ (sv n' n) (ptIdeal (j (genericPoint Y)))) _ _ at pf
  rw [hi] at pf
  refine e₁.trans (pf.trans ?_)
  exact congrArg (fun t => (((qpSnd n' m n).residueDegree (j (genericPoint Y)) : ℕ) : ℝ) * t) e₂.symm

end GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights

theorem arCalc_direct (hP : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong) (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : GlobalTheory.Published.ArCalc :=
  have H := GlobalTheory.T.arith_intersection_system_of_poincare_lelong hP hR
  have P := GlobalTheory.ArithmeticHeightTower.Read1.bridge3 (GlobalTheory.ArithmeticHeightTower.FormZc.formZ_direct H hR) (GlobalTheory.CompanionTheory.MixZ.mixZ_direct H hR)
    (GlobalTheory.CompanionTheory.MPDict.projQ_direct H hR)
  GlobalTheory.T.arithIntersectionCalculus_of_form_mixed_projection P.1 P.2.1 P.2.2

theorem cycleHeights_direct (hP : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : GlobalTheory.Published.CycleHeights :=
  GlobalTheory.Published.cycleHeights_of_arCalc (arCalc_direct hP hR)

end GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights
