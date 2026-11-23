import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumber
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorHalfGenerationOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumberStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.JetsCharZero
theorem exists_theta_rule_value_le_cover_char_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.divisor_half_generation_of_cover h1 h2 h3 h4
  have hG := GlobalTheory.LiftGaps.lift_gaps h3
  unfold Covers Lifts Formalism.MainNotions.Closed at hA hG ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hG⟩ := hG
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hG eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hGi⟩ := hx1 x hx hle ι p hp
  obtain ⟨α, hα, hdvd, hMb, hρq⟩ := hAi i hi Y hY
  obtain ⟨hp1, hgap⟩ := hGi i hi Y hY
  intro la hla cst hJ nab hnab T io y' C P φT hch hTr hP hφ
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hbd : ∀ (τ : AllWt.Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)),
      |((la τ k : ℤ) : ℝ)| ≤ ∑ τ' : AllWt.Psi p.T.Q.H, ∑ k' : Fin ((dat p i).p + (dat p i).q), |((la τ' k' : ℤ) : ℝ)| :=
    fun τ k => (Finset.single_le_sum (f := fun k' => |((la τ k' : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun τ' => ∑ k' : Fin ((dat p i).p + (dat p i).q),
        |((la τ' k' : ℤ) : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  have hEven : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    unfold GlobalTheory.RefSum.nCol
    exact ⟨4 * ((∑ f : Lt1 (dat p i), 2 * rk f) / 8 + Fintype.card (Lt1 (dat p i)) + 1), by ring⟩
  have hn1 : 1 ≤ GlobalTheory.RefSum.nCol (dat p i) := by unfold GlobalTheory.RefSum.nCol; omega
  obtain ⟨hDom, -⟩ := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hEven
    hanti hgp hbd
  have hg0 : 2 ≤ (Fm.D x ι).host.g 0 := ((Fm.D x ι).host.g_prime 0).two_le
  have hg1 : 2 ≤ (Fm.D x ι).host.g 1 := ((Fm.D x ι).host.g_prime 1).two_le
  obtain ⟨j1, j2, j3⟩ := hJ 0
  have hle0 : (Fm.D x ι).host.g 0 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hle0' : ((Fm.D x ι).host.g 0 : ℝ) ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) := by exact_mod_cast hle0
  have hg0' : (0 : ℝ) < (Fm.D x ι).host.g 0 := by exact_mod_cast (show 0 < (Fm.D x ι).host.g 0 by omega)
  have hN0 : (0 : ℝ) ≤ 2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m := by positivity
  have hR0 : 0 ≤ GlobalTheory.PtTie.rr0 (Fm.D x ι) := by unfold GlobalTheory.PtTie.rr0; positivity
  exact exists_thRule_value_le _ _ _ _ Y.d.Xo₂ Y.d.c₂ nab hnab T io y' C hTr P hP hch φT hφ α _ hα hdvd hMb _ _ hDom.1
    GlobalTheory.RefSum.sum_le_nCol hn1 (2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m) cst (by exact_mod_cast hρq) (j1.trans hle0)
    (lt_of_lt_of_le j2 hle0') (num_le _ _ _ _ _ _ _ hR0 hN0 (Nat.cast_nonneg _) hg0' hle0' j3)
end GlobalTheory.JetsCharZero
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_jet_value_bound_char_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero | exact _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero | (intros; apply _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero <;> assumption)
end
