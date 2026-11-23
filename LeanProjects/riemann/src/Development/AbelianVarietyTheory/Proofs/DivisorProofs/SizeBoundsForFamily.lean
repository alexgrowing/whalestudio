import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBoundsStatement
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

namespace GlobalTheory.CovTop.CovSz

theorem pow_five_add_one_lt {y : ℝ} (hy : 16 ≤ y) : y ^ (5 : ℕ) + 1 < y ^ (6 : ℕ) := by
  have h1 : (1 : ℝ) ≤ y ^ (5 : ℕ) := one_le_pow₀ (by linarith)
  have h2 := mul_le_mul_of_nonneg_right hy (zero_le_one.trans h1)
  have e : y ^ (6 : ℕ) = y * y ^ (5 : ℕ) := by ring
  rw [e]
  linarith

theorem sizes_of_cover : Covers fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ zBase (Fm.L x ι) ^ 12 ≤ PP := by
  refine covers_of_lifts (GlobalTheory.CovTop.Sizes.hostN 6) ?_
  intro eps Fm x hx ι p i C _ hN hi Y hY
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hx1 := (Fm.L x ι).sc.one_lt_alt
  have he0 := (Fm.L x ι).sc.eps_pos
  have he1 := (Fm.L x ι).sc.eps_lt

  have hx16 : (16 : ℝ) ≤ (Fm.L x ι).sc.x := by
    have h1 : (Fm.L x ι).sc.L ≤ (Fm.L x ι).sc.x ^ ((1 : ℝ) / 52) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le he1.le
    have h2 : ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) = (Fm.L x ι).sc.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h3 : (10 : ℝ) ^ (52 : ℕ) ≤ ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (hL10.trans h1) _
    rw [h2] at h3
    linarith [show (16 : ℝ) ≤ 10 ^ (52 : ℕ) by norm_num]
  have hrec := fun j => GlobalTheory.sizes_record_at (Fm.L x ι) (Fm.sizes x hx ι) 5 (by norm_num) hx16 j
  obtain ⟨-, -, -, -, h100, hr5, -⟩ := hrec 0
  have hg : ∀ k, Real.exp (8 * (Fm.L x ι).sc.L) ≤ ((Fm.D x ι).host.g k : ℝ) := fun k => by
    have := (hrec k).1; unfold Formalism.BasicNotions.Scale.L; exact this
  have hgpos : ∀ k, (0 : ℝ) < ((Fm.D x ι).host.g k : ℝ) := fun k => lt_of_lt_of_le (Real.exp_pos _) (hg k)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hN.f8
  have hfpos : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
  have hr2 : (2 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 2 ≤ (Fm.D x ι).R.r)
  refine ⟨p.fw.laws, ⟨by omega, by omega⟩, by linarith, ?_, ?_, hN.logfr.1, ?_, ?_, hN.f8, h100, hN.ppLow⟩
  ·
    have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
      rw [hY.1.lev.1.2.1, hY.1.pd]
      congr 1
      exact p.fw.laws.toLawsM.pins.2.1.1
    have he : (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 ≤ 3 * (Fm.L x ι).sc.L := by
      have := Nat.floor_le (show 0 ≤ 3 * (Fm.L x ι).sc.L / Real.log 3 by positivity)
      unfold expL
      rwa [le_div_iff₀ hlog3p] at this
    have h15 : Real.log 15 ≤ 5 / 2 * Real.log 3 := by
      have : Real.log ((15 : ℝ) ^ 2) ≤ Real.log ((3 : ℝ) ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have he0 : (0 : ℝ) ≤ expL (Fm.L x ι).sc.L := Nat.cast_nonneg _
    rw [hM]
    push_cast
    rw [Real.log_mul (mul_pos (hgpos 0) (hgpos 1)).ne' (by positivity : (0 : ℝ) < 15 ^ expL (Fm.L x ι).sc.L).ne',
      Real.log_mul (hgpos 0).ne' (hgpos 1).ne', Real.log_pow]
    have g0 := hN.logg 0
    have g1 := hN.logg 1
    nlinarith
  ·
    unfold fieldSz
    rw [hN.deg]
    have hd := hN.disc
    have h2f : Real.log ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤ (Fm.L x ι).sc.L := by
      refine le_trans ?_ hN.logfr.1
      push_cast
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hq : Real.log |(NumberField.discr (Fm.D x ι).host.E : ℝ)| / ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤
        2 * (Fm.L x ι).sc.L := by
      rw [div_le_iff₀ (by push_cast; positivity)]
      push_cast
      nlinarith
    linarith
  ·
    exact le_expL (by push_cast; nlinarith)
  · intro k
    have hA := hN.poly.1
    have hxA : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ C := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ C := Real.rpow_le_rpow_of_exponent_le hx1.le hA
    have hroom : ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) ≤ (Fm.L x ι).sc.b := by
      have := hN.room
      rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h6 : (Fm.L x ι).sc.x ^ (6 : ℕ) ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := pow_le_pow_left₀ (by linarith) hxA 6
    have h5 : (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 < (Fm.L x ι).sc.x ^ (6 : ℕ) := pow_five_add_one_lt hx16
    have hb : (Fm.L x ι).sc.b ≤ Real.exp (8 * (Fm.L x ι).sc.L) := by
      unfold Formalism.BasicNotions.Scale.b; exact Real.exp_le_exp.2 (by linarith)
    have hr5' : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) := by
      have e : (Fm.L x ι).sc.x ^ (5 : ℕ) = (Fm.L x ι).sc.x ^ (5 : ℝ) := by exact_mod_cast (Real.rpow_natCast _ 5).symm
      first | exact hr5 | (rw [e]; exact hr5)
    have : ((Fm.D x ι).R.r : ℝ) + 1 < (Fm.D x ι).host.g k :=
      calc ((Fm.D x ι).R.r : ℝ) + 1 ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 := add_le_add hr5' le_rfl
        _ < (Fm.L x ι).sc.x ^ (6 : ℕ) := h5
        _ ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := h6
        _ ≤ (Fm.L x ι).sc.b := hroom
        _ ≤ Real.exp (8 * (Fm.L x ι).sc.L) := hb
        _ ≤ (Fm.D x ι).host.g k := hg k
    exact_mod_cast this

theorem size_rows : Size → Covers fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L ∧ Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ zBase (Fm.L x ι) ^ 12 ≤ PP ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1)) ∧ ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  refine covers_imp (covers_and sizes_of_cover (covers_and (GlobalTheory.T.flat_degree_log_form_abs_le hS) (covers_and (GlobalTheory.T.log_kappa_length_bounds hS)
    (covers_and (GlobalTheory.T.weight_parameter_size_bounds hS) (covers_and (GlobalTheory.T.weight_param_coeff_sum_bound hS) (GlobalTheory.T.weight_param_coeff_sum_le_at_index hS)))))) ?_
  intro eps Fm x hx ι p i Y PP h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a13⟩, b11, ⟨b12, b14⟩, ⟨b15, b16⟩, b17, b18⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, b11, b12, a13, b14, b15, b16, b17, b18⟩

end GlobalTheory.CovTop.CovSz

end
