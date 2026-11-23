import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDescentMapsCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepLatticeEqLevelLatticeOfCovers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

set_option synthInstance.maxHeartbeats 200000

section
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
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.CovTop.DescentMaps
end GlobalTheory.CovTop.DescentMaps
namespace GlobalTheory.CovTop.DescentMaps
set_option maxHeartbeats 1000000 in
theorem covering_descent_maps_compatible_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.MapsCondition := by
  intro hP hGD hQ hSI hTF hSN hGram hDG hSz hFD
  obtain ⟨C, hC0, hub⟩ := _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound hP hGD hQ hSI hTF hSN
  have hT := _root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN hP hGram hDG
  have hS := _root_.GlobalTheory.T.size_bounds_for_family_alt hSz
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt (2 * C + 200)
  unfold _root_.GlobalTheory.CovTop.MapsCondition _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.DeepGoodness at hDG
  unfold _root_.GlobalTheory.CovTop.FlatDegreeCondition at hFD
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hT hS hDG hFD
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hH
  refine Closed.imp ((((hT.and hS).and hH).and hDG).and hFD) ?_
  intro eps Fm CH _ hall0
  obtain ⟨⟨⟨⟨⟨C1, -, hT'⟩, ⟨C2, -, hS'⟩⟩, ⟨A, -, hH'⟩⟩, ⟨C4, -, hDG'⟩⟩, ⟨C5, -, hFD'⟩⟩ := hall0
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hall⟩ := (((hT'.and hS').and hH').and hDG').and hFD'
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hall x hx hle ι p hp
  obtain ⟨fr, ψ, -, hl, hlat, hcard⟩ := a1 i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hE, hfr, hexp, hg, hf8, hr100, hflat, -⟩ := a2 i hi Y hY
  have hN := a3 i
  have hDGY := a4 i hi Y hY
  have hFDY := a5 i hi Y hY
  obtain ⟨-, hpq, hq, h2q⟩ := GlobalTheory.Member.exists_iotaOK (Fm.D x ι) p.T.Q hLaws.pins ((i : ℕ) + 1) hInR
  have hq1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [hq]; simp only [Formalism.MainNotions.WeightFamilies.rho, Formalism.BasicNotions.Ranks.sigW]; omega
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by omega
  have hfin : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by rw [hN.deg]; omega
  obtain ⟨u, hu, hdet, hB⟩ := hub (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1
    hM hE hfr (le_of_eq rfl) _ hFDY (by rw [abs_neg]; exact hflat) hexp hg hf8 hr100 fr
  have hK := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1
  have hGk : Even (Gk p i).2 := (p.κ i).n_even.natCast
  have hW : Even (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0).2 :=
    GlobalTheory.AllWt.even_wtOf _ _
  have hGm : Even (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))).2 := hGk.add (GlobalTheory.AllWt.even_wtOf _ _)
  have hGW : Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 = Gk p i := by
    simp only [Gs, shiftG, add_assoc, ← GlobalTheory.AllWt.wtOf_add, neg_smul, neg_add_cancel, add_zero, GlobalTheory.AllWt.wtOf_zero]
  set z := zBase (Fm.L x ι) with hz
  have hzL : (Fm.L x ι).sc.L ≤ z := by
    have h8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have h100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have h0 : (0 : ℝ) ≤ (Fm.L x ι).sc.L := by linarith
    rw [hz, zBase]
    nlinarith [mul_le_mul h8 h100 (by norm_num) (by linarith)]
  have hz1 : 2 * C + 200 ≤ z := hN.big.1.trans hzL
  have hPP : z ^ 12 ≤ (Fm.L x ι).sc.b := by
    have h1 := hN.ppLow
    obtain ⟨hA1, hA2, -⟩ := hN.poly
    have h3 := hN.room
    have hz0 : 1 ≤ z := by linarith
    have hx1 : 1 ≤ (Fm.L x ι).sc.x ^ A := le_trans (one_le_pow₀ hz0) (h1.trans hA2)
    have h4 : (Fm.L x ι).sc.x ^ A ≤ ((Fm.L x ι).sc.x ^ A) ^ (2 * C + 200) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ 2 * C + 200 by linarith)
    linarith
  have hb : (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (C * ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 9) ^ 2 ≤
      Real.exp (2 * (Fm.L x ι).sc.b) := by
    have hz9 : ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L : ℝ) = z := by rw [hz, zBase]
    rw [hz9]
    rw [Nat.card_eq_fintype_card] at hcard
    have hn0 : (0 : ℝ) < Fintype.card (grpHR fr) := by exact_mod_cast Fintype.card_pos
    have hz0 : 1 ≤ z := by linarith
    have hn3 : (Fintype.card (grpHR fr) : ℝ) ^ 3 ≤ Real.exp (135 * z ^ 2) := by
      rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have he : Real.exp (C * z ^ 9) ^ 2 = Real.exp (2 * C * z ^ 9) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]
    calc (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (2 * C * z ^ 9)
        ≤ Real.exp (135 * z ^ 2) * Real.exp (2 * C * z ^ 9) :=
          mul_le_mul_of_nonneg_right hn3 (Real.exp_pos _).le
      _ = Real.exp (135 * z ^ 2 + 2 * C * z ^ 9) := by rw [← Real.exp_add]
      _ ≤ Real.exp (2 * (Fm.L x ι).sc.b) := by
          refine Real.exp_le_exp.2 ?_
          have a1 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz0 (by norm_num)
          have a2 : z ^ 10 ≤ z ^ 12 := pow_le_pow_right₀ hz0 (by norm_num)
          have a3 : (135 + 2 * C) * z ^ 9 ≤ z * z ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have a4 : z * z ^ 9 = z ^ 10 := by ring
          nlinarith
  have e2 : Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1)) = Gk p i +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 := by
    unfold Gs Gk shiftG; rfl
  obtain ⟨n, φ, h1, h2, h3, h4⟩ := mapsCore (grpHR fr) (Nat.le_add_right_of_le hp1) hl.coprime
    (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))))
    (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0) (Gk p i) hGW
    hGm hW (hK _ hGk).1 (hK _ hW).1 (fun γ f g hg => ((hK _ hGk).2 γ f g hg).1)
    (fun γ f g hg => ((hK _ hW).2 γ f g hg).1) (fun γ f g hg => ((hK _ hGk).2 γ f g hg).2)
    hDGY.1 hDGY.2.2.1 (GlobalTheory.LevDesc.chiHR fr ψ) u hu hdet _ (Real.exp_pos _).le
    (fun γ f g hg σ => hB γ _ f g hGm hg σ) _ hb (latDeep p i Y) hlat
    (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1))) e2.symm
  exact ⟨n, φ, h1, h2, h3, h4⟩
end GlobalTheory.CovTop.DescentMaps
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
theorem _root_.GlobalTheory.T.covering_maps_of_gram_deep_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.MapsCondition := by
  first | exact @_root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt | exact _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt | (intros; apply _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt <;> assumption)
end
end
