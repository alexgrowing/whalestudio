import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
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

theorem abs_kap_le (Dw : Datum H) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(FlagTan.kap Dw τ k : ℝ)| ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
  have hk := k.2
  have h : |FlagTan.kap Dw τ k| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
    simp only [FlagTan.kap]
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> omega
  rw [← Int.cast_abs]; exact_mod_cast h

theorem sum_abs_kap_le (Dw : Datum H) :
    ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
  calc ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ ∑ _τ : Psi H, ∑ _k : Fin (Dw.p + Dw.q), ((Dw.p + Dw.q : ℕ) : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => abs_kap_le Dw τ k
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sum_abs_weightZero_le_components (Dw : Datum H) (P : WtPar Dw) :
    ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| ≤ ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| + ∑ τ, ∑ k, |(P.u₂ τ k : ℝ)| +
      (FlagTan.dimFlag Dw : ℝ) * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => ?_
  have e : (P.wt 0 τ k : ℝ) = (FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ) + (FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ) := by
    simp only [WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [e]
  calc _ ≤ |(FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ)| + |(FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, Nat.abs_cast]
      linarith [abs_add_le (FlagTan.kap Dw τ k : ℝ) (P.u₂ τ k : ℝ)]

theorem consecutiveGap_weightZero_ge (Dw : Datum H) (P : WtPar Dw) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) (g : ℤ)
    (hg : g ≤ gap (P.u₁ τ) k) : ((FlagTan.dimFlag Dw : ℤ) + 1) * g - 2 ≤ gap (P.wt 0 τ) k := by
  have hr := (P.gap_rem τ k).1
  have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
    simp only [FlagTan.kap, Fin.val_mk]
    split_ifs <;> push_cast <;> omega
  rw [gap, dif_pos h] at hr hg ⊢
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply] at hr ⊢
  simp only [nsmul_eq_mul] at hr ⊢
  have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

theorem final_le {C Zr S Dc PP X abelian₂ L : ℝ} (hC : 0 ≤ C) (hL : 4 * C + 1 ≤ L) (hZL : L ≤ Zr) (hPP : Zr ^ 12 ≤ PP)
    (hDc : 1 ≤ Dc) (hX : 1 ≤ X) (hS : S ≤ 3 * Dc * Zr ^ 2 * X) (hLam : Real.log abelian₂ ≤ C * (Zr ^ 3 * S + Zr ^ 5)) :
    Real.log abelian₂ ≤ Dc * PP * X := by
  have hZ1 : 1 ≤ Zr := by linarith
  have hZ0 : 0 ≤ Zr := by linarith
  have hZ5 : 0 ≤ Zr ^ 5 := by positivity
  have hDX : 1 ≤ Dc * X := by nlinarith
  have h1 : Zr ^ 3 * S ≤ 3 * (Dc * X) * Zr ^ 5 := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ Zr ^ 3)
    nlinarith
  have h2 : Zr ^ 5 ≤ (Dc * X) * Zr ^ 5 := by nlinarith
  have h3 : C * (Zr ^ 3 * S + Zr ^ 5) ≤ (Dc * X) * (4 * C * Zr ^ 5) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    nlinarith
  have h4 : 4 * C * Zr ^ 5 ≤ PP := by
    have a : Zr ≤ Zr ^ 7 := by
      calc Zr = Zr ^ 1 := (pow_one _).symm
        _ ≤ Zr ^ 7 := pow_le_pow_right₀ hZ1 (by norm_num)
    have b : 4 * C ≤ Zr ^ 7 := by linarith
    have c : 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := mul_le_mul_of_nonneg_right b hZ5
    calc 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := c
      _ = Zr ^ 12 := by ring
      _ ≤ PP := hPP
  have h5 : (Dc * X) * (4 * C * Zr ^ 5) ≤ (Dc * X) * PP := mul_le_mul_of_nonneg_left h4 (by linarith)
  calc Real.log abelian₂ ≤ _ := hLam
    _ ≤ _ := h3
    _ ≤ _ := h5
    _ = Dc * PP * X := by ring

theorem sum_le {S K A1 A2 Dc W : ℝ} (hSle : S ≤ K + A2 + Dc * A1) (hK : K ≤ W) (h1 : A1 ≤ W) (h2 : A2 ≤ W)
    (hDc : 1 ≤ Dc) (hW : 0 ≤ W) : S ≤ 3 * Dc * W := by
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Dc)
  nlinarith

theorem log_sum_le {S k fr L : ℝ} (hS0 : 0 ≤ S) (hSk : S ≤ (fr * L) ^ 2 * k) (hk : Real.log k ≤ 2 * L)
    (hfr : Real.log fr ≤ L) (hL1 : 1 ≤ L) (hfr1 : 1 ≤ fr) : Real.log S ≤ 10 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hZ : 0 < fr * L := by positivity
  have hk0 : 0 < k := by
    by_contra hk0
    push_neg at hk0
    have : (fr * L) ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk0
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc Real.log S ≤ Real.log ((fr * L) ^ 2 * k) := Real.log_le_log h hSk
    _ = 2 * (Real.log fr + Real.log L) + Real.log k := by
      rw [Real.log_mul (by positivity) hk0.ne', Real.log_pow, Real.log_mul (by linarith) (by linarith)]; push_cast; ring
    _ ≤ 10 * L := by linarith

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

set_option maxHeartbeats 1000000 in

theorem short_span_uc : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  intro hP2 _hDG hSz hFD
  obtain ⟨C, hC0, hH3⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP2
  have hGd := GlobalTheory.T.good_weight_antitone_gap hP2
  refine ((((((GlobalTheory.T.size_bounds_for_family hSz).and (GlobalTheory.T.weight_parameter_strict_antitone hSz)).and (Sizes.hostN (4 * C + 1))).and WtShape.wtN).and
    GlobalTheory.HSApp.wtBig_run).and hFD).imp fun Fm CH _ hh => ?_
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
