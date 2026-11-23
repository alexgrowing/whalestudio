import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
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
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCharacterBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevPhInjectiveOfLevDetNonZeroDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspPhMemChiLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormWCuspPhLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW
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

theorem mapsCore {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {D : D7} {x : ℝ}
    {V : (c.F →+* ℂ) → HSp D} {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
    (S : Subgroup (LevelAut Dw l)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Gm W G : WTZ E) (hGW : Gm + W = G)
    (hGm : Even Gm.2) (hW : Even W.2) (hKG : KeepsCusp U G) (hKW : KeepsCusp U W)
    (hLG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U G → g ∈ latW U G)
    (hLW : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W)
    (hNG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict G σ g = GlobalTheory.AllWt.normW U x V dict G σ f)
    (hGood : GoodW U x V dict G) (hGoodP : GoodW U x V dict (G + W))
    (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (hu : u ∈ latW U W)
    (hdet : ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (γ : LevelAut Dw l) (f : cuspW Xo c U Gm) (g : cuspW Xo c U (Gm + W)), (g : Rul Xo c) = f * pull Xo c γ u →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict Gm σ f)
    (b : ℝ) (hb : (Fintype.card S : ℝ) ^ 3 * B ^ 2 ≤ Real.exp (2 * b))
    (Lt : Submodule (𝓞 c.F) (cuspW Xo c U G)) (hLt : Lt = GlobalTheory.LevDesc.chiLat S U G χ) (Gp : WTZ E) (hGp : G + W = Gp) :
    ∃ (n : ℕ) (φ : Fin n → cuspW Xo c U Gm →ₗ[c.F] cuspW Xo c U G),
      (∀ h, ∀ f ∈ latW U Gm, φ h f ∈ Lt) ∧ (∀ f, (∀ h, φ h f = 0) → f = 0) ∧
      (∀ σ f, ∑ h, GlobalTheory.AllWt.normW U x V dict G σ (φ h f) ^ 2 ≤
        Real.exp (2 * b) * GlobalTheory.AllWt.normW U x V dict Gm σ f ^ 2) ∧
      n * Formalism.HN.rkK Lt ≤ rankW U Gp := by
  subst hGW hLt hGp
  have hm : ∀ f ∈ cuspW Xo c U Gm, ∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ (u : Rul Xo c) f h ∈ cuspW Xo c U (Gm + W) :=
    fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hGm hW hKG hKW χ u.2 hf h
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun k => LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm, ?_, ?_, ?_, ?_⟩
  · intro k f hf
    exact GlobalTheory.LevDesc.cuspPh_mem_chiLat Xo c U S hpq hA Gm W hGm hW hKG hKW hLG hLW χ u hu f hf (e k)
  · intro f hf0
    have hsec : (f : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ f.2)
    have husec : (u : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ u.2)
    apply Subtype.ext
    refine GlobalTheory.levPh_injective_of_levDet_nonZeroDivisor Xo c S hpq hA χ u husec hdet _ hsec fun h => ?_
    have h1 := hf0 (e.symm h)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Equiv.apply_symm_apply] at h1
    rw [← GlobalTheory.LevDesc.coe_cuspPh S χ _ hm f h, h1]
    rfl
  · intro σ f
    have h1 : ∑ k, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ ((LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm) f) ^ 2 =
        ∑ h : S, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2 :=
      e.sum_comp (fun h : S => GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2)
    rw [h1]
    refine (GlobalTheory.sum_sq_normW_cuspPh_le Xo c U x V dict S hpq hA Gm W hGm hW hKG hKW χ u B hB0 hGood.1 hNG hB f σ).trans ?_
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  · exact GlobalTheory.CovolRank.card_mul_rkK_chiLat_le_rankW Xo c U x V dict S hpq hA (Gm + W) W (hGm.add hW) hW hKG hKW hGood hGoodP χ u hdet

end GlobalTheory.CovTop.DescentMaps

namespace GlobalTheory.CovTop.DescentMaps

set_option maxHeartbeats 1000000 in

theorem maps : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Gram → DeepGood → Size → FlatDeg → Maps := by
  intro hP hGD hQ hSI hTF hSN hGram hDG hSz hFD
  obtain ⟨C, hC0, hub⟩ := GlobalTheory.T.exists_uniform_height_constant hP hGD hQ hSI hTF hSN
  have hT := GlobalTheory.T.lattice_level_character_bound hP hGram hDG
  have hS := GlobalTheory.T.size_bounds_for_family hSz
  have hH := GlobalTheory.CovTop.Sizes.hostN (2 * C + 200)
  unfold Maps Covers Lifts
  unfold DeepGood at hDG
  unfold FlatDeg at hFD
  unfold Covers Lifts at hT hS hDG hFD
  unfold HostN Lifts at hH
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
