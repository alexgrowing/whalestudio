import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortVectorsSpanCuspLattice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun

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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.ShortSpanUnitCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
end GlobalTheory.CovTop.ShortSpanUnitCover
namespace GlobalTheory.CovTop.ShortSpanUnitCover
set_option maxHeartbeats 1000000 in
theorem short_vectors_span_uc_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  intro hP2 _hDG hSz hFD
  obtain ⟨C, hC0, hH3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  have hGd := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine ((((((_root_.GlobalTheory.T.size_bounds_for_family_alt hSz).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz)).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt (4 * C + 1))).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).and
    _root_.GlobalTheory.HSApp.wtBig_run_alt).and hFD).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩⟩, ⟨C4, -, a4, h4⟩⟩, ⟨C5, -, a5, h5⟩⟩, ⟨C6, -, a6, h6⟩⟩ := hh
  refine ⟨0, le_rfl, max a1 (max a2 (max a3 (max a4 (max a5 a6)))), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have s1 := h1 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  have s2 := h2 x hx (le_trans (by simp) hle) ι p hp i hi
  have s3 := h3 x hx (le_trans (by simp) hle) ι p hp i
  have s4 := h4 x hx (le_trans (by simp) hle) ι p hp i
  have s5 := h5 x hx (le_trans (by simp) hle) ι p hp i hi
  have s6 := h6 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, hkap, hPP, -, -, -, hu12, hwt⟩ := s1
  obtain ⟨hp1, hq1, hfin, -, hsa, -⟩ := s2
  intro Z
  set P : WtPar (dat p i) := (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ :
    WtPar (dat p i)) with hP
  have hpq : (dat p i).p + (dat p i).q = (Fm.D x ι).R.r := s4.sig.2.2
  have hr2 : 0 < (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
  have hDf : (Fm.D x ι).R.f ≤ FlagTan.dimFlag (dat p i) := by
    rw [← GlobalTheory.CompHS.dimFlag_eq, s4.dim]; exact Nat.le_mul_of_pos_right _ hr2
  have hD2 : 2 ≤ FlagTan.dimFlag (dat p i) + 0 := by omega
  have hAnt := fun τ => GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P 0 (fun τ => (hsa τ).1) hD2 hp1 hq1 τ
  have hgap : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.wt 0 τ) ((dat p i).p - 1) := by
    intro τ
    have hk : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
    obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (FlagTan.dimFlag (dat p i) + 3) * ((FlagTan.dimFlag (dat p i) + 1).choose 2 +
        4 * ((dat p i).p + (dat p i).q) + FlagTan.dimFlag (dat p i) + 3) := ⟨_, rfl⟩
    have hg : (G : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := hG ▸ s5.gaps τ _ hk
    have h1 := consecutiveGap_weightZero_ge (dat p i) P τ hk _ hg
    have hG12 : 12 * (Fm.D x ι).R.r ≤ G := by
      rw [hG, hpq]
      have := Nat.mul_le_mul (show 3 ≤ FlagTan.dimFlag (dat p i) + 3 by omega)
        (show 4 * (Fm.D x ι).R.r ≤ (FlagTan.dimFlag (dat p i) + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          FlagTan.dimFlag (dat p i) + 3 by omega)
      omega
    have hN : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 ≤ (FlagTan.dimFlag (dat p i) + 1) * G := by
      have := Nat.mul_le_mul (show (Fm.D x ι).R.f + 1 ≤ FlagTan.dimFlag (dat p i) + 1 by omega) hG12
      nlinarith
    have hN' : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 : ℕ) : ℤ) ≤ (((FlagTan.dimFlag (dat p i) + 1) * G : ℕ) : ℤ) := by
      exact_mod_cast hN
    push_cast at hN' ⊢
    linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hfr1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| := by positivity
  have hw0 := hwt 0 (Nat.zero_le _)
  have hlog := log_sum_le hS0 hw0 hkap hfr hL1 hfr1
  obtain ⟨n, w, abelian₂, hSG, hLam, -⟩ := hH3 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 _ hL1 hM hfs
    hfr le_rfl _ s6 (by rw [abs_neg]; exact hflat) (P.wt 0) (fun τ => (hAnt τ).1) hgap hlog Z
  refine ⟨n, w, fun q => (hSG.gen _).2 (Submodule.subset_span ⟨q, rfl⟩), ?_, fun q σ => ?_⟩
  · have hGO := ((hGd (Fm.D x ι) p.T hLaws _ hp1 hq1 hfin hInR Y _ _ hY.1 (P.wt 0) (fun τ => (hAnt τ).1)
      (fun τ => (hAnt τ).2)).2 Z).2.2
    rw [eq_top_iff, ← hGO]
    exact Submodule.span_le.2 fun y hy => Submodule.span_le_restrictScalars ℤ _ _ ((hSG.gen y).1 hy)
  · refine (hSG.le q σ).trans ?_
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hSG.one_le), GlobalTheory.CompHS.dimFlag_eq]
    refine Real.exp_le_exp.2 ?_
    have hZ : 0 < zBase (Fm.L x ι) := by unfold zBase; positivity
    have hkap0 : 0 ≤ kap p i := by
      have : 0 ≤ zBase (Fm.L x ι) ^ 2 * kap p i := hS0.trans hw0
      exact (mul_nonneg_iff_of_pos_left (by positivity)).1 this
    have hX : 1 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
      have := div_nonneg hkap0 (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP)); linarith
    have hW : 0 ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by positivity
    have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := by rw [← Nat.card_eq_fintype_card]; exact s4.card
    have hK : ∑ τ, ∑ k, |(FlagTan.kap (dat p i) τ k : ℝ)| ≤
        zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
      refine (sum_abs_kap_le (dat p i)).trans ?_
      rw [hcard, hpq]
      have a : 1 ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2 := by nlinarith
      have b : ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 ≤ zBase (Fm.L x ι) ^ 2 := by
        unfold zBase
        calc ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * 1 :=
              (mul_one _).symm
          _ ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * (((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2) :=
              mul_le_mul_of_nonneg_left a (by positivity)
          _ = _ := by ring
      calc _ ≤ zBase (Fm.L x ι) ^ 2 := by push_cast; exact b
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hX
    have hDc : (1 : ℝ) ≤ (FlagTan.dimFlag (dat p i) : ℝ) := by exact_mod_cast (by omega : 1 ≤ FlagTan.dimFlag (dat p i))
    have hSs := sum_le (sum_abs_weightZero_le_components (dat p i) P) hK (hu12 _ (Set.mem_insert _ _))
      (hu12 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDc hW
    have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := le_mul_of_one_le_left (by linarith) hfr1
    exact final_le hC0 s3.big.1 hZL hPP hDc hX (by linarith) hLam
end GlobalTheory.CovTop.ShortSpanUnitCover
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
theorem _root_.GlobalTheory.T.short_vectors_span_cusp_lattice_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  first | exact @_root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | exact _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt | (intros; apply _root_.GlobalTheory.CovTop.ShortSpanUnitCover.short_vectors_span_uc_alt <;> assumption)
end
end
