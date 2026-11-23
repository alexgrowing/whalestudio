import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLeStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DimLogTop
theorem log_top_dimension_le : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  intro hP hSz
  obtain ⟨Cb, -, hB⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  have hG := _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain hP
  have hQ := GlobalTheory.QuoWt.weights_at_point hSz
  have hS := GlobalTheory.CovTop.CovSz.size_rows hSz
  have hW := GlobalTheory.HSApp.wtBig_run
  refine Closed.imp (Closed.and (Closed.and hQ hS) hW) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max (max x1 x2) x3) ((max Cb 1) ^ eps⁻¹), ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hle1 : max (max x1 x2) x3 ≤ x := (le_max_left _ _).trans hle
  have hq := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi
  have hs := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi Y hY
  have hwb := h3 x hx ((le_max_right _ _).trans hle1) ι p hp i hi
  obtain ⟨hp1, hq1, hE, -, hstr, -, -⟩ := hq
  obtain ⟨hLJ, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, -, hkap, hZ12, -, -, -, -, hwt⟩ := hs
  set PP := (Fm.parT x hx ι).PP with hPP
  have hx1 : Fm.x1 < x := hx
  have hLx : (Fm.L x ι).sc.L = x ^ eps := by
    unfold Scale.L; rw [Fm.L_x x ι hx1, Fm.L_eps x ι]
  have hLC : max Cb 1 ≤ (Fm.L x ι).sc.L := by
    rw [hLx]
    have h0 : (0 : ℝ) ≤ (max Cb 1) ^ eps⁻¹ := Real.rpow_nonneg (by positivity) _
    calc max Cb 1 = ((max Cb 1) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow (by positivity) heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow h0 ((le_max_right _ _).trans hle) heps.le
  have hT2 : 2 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) + lenT p i PP := by
    have hT1 := hwb.le_T
    have hD1 := hwb.one_le
    change 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) at hD1
    change GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i PP at hT1
    omega
  have hanti := GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i)
    (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) (lenT p i PP)
    (fun τ => (hstr τ).1) hT2 hp1 hq1
  have hsum := hwt (lenT p i PP) le_rfl
  have hsize : Real.log (∑ τ, ∑ k, |(((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) τ k : ℝ)|) ≤ 20 * (Fm.L x ι).sc.L := by
    refine GlobalTheory.CovTop.DimLogTop.log_size_le ((Fm.D x ι).R.f : ℝ) ((Fm.D x ι).R.r : ℝ) (Fm.L x ι).sc.L (kap p i) _
      (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)) (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r))
      hL1 (sizeK_nonneg _ _ _) hkap hfr (by positivity) ?_
    have : (0 : ℝ) ≤ 6 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 := by positivity
    have e : zBase (Fm.L x ι) = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) * (Fm.L x ι).sc.L := by unfold zBase; ring
    rw [← e]; linarith
  have hBr := (hB (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr (by unfold zBase; exact le_rfl)
    _ (fun τ => (hanti τ).1) hsize Z).2.2
  have hGd := (hG (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 _ (fun τ => (hanti τ).1) (fun τ => (hanti τ).2)).2 Z
  have hrk : Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) Z = (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i)
      ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt
      (lenT p i PP)) 0)) : ℝ) := by
    show ((rankOn Y.U Z _ : ℕ) : ℝ) = _
    unfold rankOn
    rw [rkK_eq_finrank_of_span_top _ hGd.2.2]
  rw [← hrk]
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) := by
    have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase; nlinarith
  have hcube := GlobalTheory.CovTop.DimLogTop.cube_le Cb (Fm.L x ι).sc.L (zBase (Fm.L x ι)) ((le_max_left _ _).trans hLC) hL1 hLZ
  have h2 : Cb * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 = Cb * zBase (Fm.L x ι) ^ 3 := by
    unfold zBase; ring
  linarith
end GlobalTheory.CovTop.DimLogTop
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_top_dimension_bound_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le | exact _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le | (intros; apply _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le <;> assumption)
end
