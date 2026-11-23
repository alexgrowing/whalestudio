import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HilbertSamuelBergmanFrameBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
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
noncomputable section
namespace GlobalTheory.FrameBerg
end GlobalTheory.FrameBerg
namespace GlobalTheory.FrameBerg
set_option maxHeartbeats 2000000 in
theorem bergman_frames_of_short_range_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  intro hP2 _hDG hS hFD
  obtain ⟨C1, hC1, H1⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP2
  obtain ⟨C2, hC2, H2⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP2
  have H0 := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP2
  refine (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and (_root_.GlobalTheory.HSApp.wtBig_run_alt.and hFD)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩ := hh
  obtain ⟨e, he⟩ := GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)
  refine ⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hA := ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi
  have hB := hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY
  have hW := hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi
  have hF := hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY
  have hLM := (he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1
  clear ha hb hc hd he
  obtain ⟨h1p, h1q, hfin, -, hanti, -⟩ := hA
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩ := hB
  obtain ⟨hr, hdim, -⟩ := GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi
  intro Zc
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef
  have hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
  have hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1) := fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq
  have ha1 : ∀ τ, Antitone (P.u₁ τ) := fun τ => (hanti τ).1.antitone
  have hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k := by
    intro τ k hk
    have e : P.u₂ τ = P.u₁ τ + P.rem τ := rfl
    rw [e, gap_add]
    have := one_le_gap_of_strictAnti (hanti τ).1 hk
    have := (P.gap_rem τ k).1
    omega
  have ha2 : ∀ τ, Antitone (P.u₂ τ) := fun τ =>
    antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)
  have hG := H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
  refine ⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩
  have hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := by
    intro τ
    refine le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)
    have h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le two_pos).2
      have : 100 ≤ (Fm.D x ι).R.r := h100r
      have : 99 ≤ (Fm.D x ι).R.r - 1 := by omega
      nlinarith
    rw [hdim, hr]
    generalize (Fm.D x ι).R.r.choose 2 = c at h9 ⊢
    generalize ((Fm.D x ι).R.f * c + 1).choose 2 = B
    have h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c := by
      rw [mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]; exact Nat.mul_le_mul_left _ h9
    have h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤
        ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 8 ≤ (Fm.D x ι).R.f := h8f
    have h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r := by
      have : 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    exact_mod_cast (h4.trans (h1.trans (by omega))).trans h2
  have hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L := hL1
  have hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι) := rfl
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast h8f
  have hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast h100r
  have hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by positivity
  have hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L := by
    have := Real.exp_le_exp.2 hfr
    rwa [Real.exp_log (by exact_mod_cast hfrpos)] at this
  have hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rw [← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le
  have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    rw [← hZdef]
    have : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := hL1'.trans hZL
  have hkap0 : 0 ≤ kap p i := by unfold CovTop.kap sizeK; positivity
  have hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rcases hkap0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have := Real.exp_le_exp.2 hkap
      rw [Real.exp_log h0] at this
      rw [← Real.exp_nat_mul]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
    have : 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP := div_nonneg hkap0 (Nat.cast_nonneg _)
    linarith
  have hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i := by
    rcases Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0
    · rw [h0]; simp [hkap0]
    · exact div_le_self hkap0 (by exact_mod_cast h0)
  have hS := hsum P.u₁ (by simp)
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by positivity
  have hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L) := by
    have e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e7]
    refine hS.trans ?_
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4 := by
      calc zBase (Fm.L x ι) ^ 2 ≤ (Real.exp (Fm.L x ι).sc.L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hZE 2
        _ = _ := by ring
    have hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3 := by
      nlinarith
    calc zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)
        ≤ Real.exp (Fm.L x ι).sc.L ^ 4 * Real.exp (Fm.L x ι).sc.L ^ 3 :=
          mul_le_mul hZ2 hK3 (by linarith) (by positivity)
      _ = _ := by ring
  have hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h0).2 hSE
  have ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2 := by
    rw [hZdef]
  have hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by rw [abs_neg]; exact hflat
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc
  obtain ⟨f, hfn, -, hfN⟩ := exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂
    (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg
  have hb := (H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1
  rw [hZdef] at hLam hn hb
  have hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι) := hLM.trans hZL
  have hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5 := by positivity
  have hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12 := by
    have : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) hZ5
    nlinarith
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ12
  have hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  have hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  refine ⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _,
    Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩
  · rw [hfn]; exact hn.trans hC1Z
  · rw [Real.log_exp]; exact hC2Z
  · rcases le_total abelian₂ 1 with hl | hl
    · rw [max_eq_right hl, Real.log_one]; positivity
    · rw [max_eq_left hl]
      refine hLam.trans ?_
      have h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤
          zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)
        nlinarith
      have h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤
          (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have h6 := mul_le_mul_of_nonneg_left h3 hC1
        have h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) :=
          le_mul_of_one_le_right (by positivity) hK1
        linarith [h6, h5]
      refine h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      nlinarith
end GlobalTheory.FrameBerg
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
theorem _root_.GlobalTheory.T.hilbertSamuel_bergman_frame_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  first | exact @_root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | exact _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt | (intros; apply _root_.GlobalTheory.FrameBerg.bergman_frames_of_short_range_alt <;> assumption)
end
end
