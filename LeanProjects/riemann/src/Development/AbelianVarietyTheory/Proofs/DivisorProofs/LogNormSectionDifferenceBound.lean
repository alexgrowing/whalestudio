import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartAbelianFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDecompositionComparisonStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogNormCmp

open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

theorem psd_of_span_forms {g : ℕ} {ι Tau : Type} [Fintype Tau] {d : Tau → ℕ} (v : ι → Fin g → ℂ)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) (Gm Gm' : Matrix (Fin g) (Fin g) ℂ) (hG : Gm.IsHermitian)
    (hG' : Gm'.IsHermitian) (A A' : ∀ τ, Matrix (Fin (d τ)) (Fin (d τ)) ℂ) (x : ∀ τ, ι → Fin (d τ) → ℂ)
    (hA : ∀ i i', HermFrame.form Gm (v i) (v i') = ∑ τ, HermFrame.form (A τ) (x τ i) (x τ i'))
    (hA' : ∀ i i', HermFrame.form Gm' (v i) (v i') = ∑ τ, HermFrame.form (A' τ) (x τ i) (x τ i')) (K : ℝ)
    (hK : ∀ τ, (((K : ℂ) • A' τ) - A τ).PosSemidef) : (((K : ℂ) • Gm') - Gm).PosSemidef :=
  GlobalTheory.T.hermitian_form_decomposition_comparison v hv Gm Gm' hG hG' A A' x hA hA' K hK

theorem exists_span_crd_dUnit
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz}
    {g : ℕ} (ρ : Oz →+* ℂ) (y : CxPts q ρ) (ch : Chart ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g)
    (hy : y ∈ ptsIn q ρ ch.U) :
    ∃ (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W), y ∈ ptsIn q ρ (j ⁻¹ᵁ U) ∧
      Submodule.span ℂ (Set.range fun f : Γ(Z.t.G.left, W) =>
        ch.crd q ρ (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f)) y) = ⊤ :=
  GlobalTheory.T.toroidal_chart_abelian_fibre j ρ y ch hy

theorem chartGram_le_of_eig
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (G G' : ∀ σ', EigMet Z σ') {T : Scheme.{0}}
    (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} {g : ℕ} (h h' : VMetric q ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g)
    (hd : MetFam.IsDualEigOn G j h) (hd' : MetFam.IsDualEigOn G' j h') (σ' : c.F →+* ℂ)
    (yc : CxPts (genStr Z) σ') (y : CxPts q (σ'.comp β)) (e : y.1 ≫ j = yc.1 ≫ genι Z)
    (u : EigFrame Z σ' (yc.1 ≫ genι Z)) (K : ℝ)
    (hK : ∀ τ, (((K : ℂ) • ((G' σ').gram yc u τ)⁻¹) - ((G σ').gram yc u τ)⁻¹).PosSemidef)
    (ch : Chart ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g) (hy : y ∈ ptsIn q (σ'.comp β) ch.U) :
    (((K : ℂ) • (h'.met (σ'.comp β)).G ch y) - (h.met (σ'.comp β)).G ch y).PosSemidef := by
  obtain ⟨U, W, hU, hyU, hsp⟩ := exists_span_crd_dUnit j (σ'.comp β) y ch hy
  exact psd_of_span_forms _ hsp _ _ ((h.met _).posDef ch y hy).isHermitian ((h'.met _).posDef ch y hy).isHermitian
    (fun τ => ((G σ').gram yc u τ)⁻¹) (fun τ => ((G' σ').gram yc u τ)⁻¹)
    (fun τ f i => (valR (u.v τ i) W f).snd)
    (fun f f' => ((h.met _).form_eq ch hy _ _ hyU).symm.trans (hd σ' yc y e u U W hU f f' hyU))
    (fun f f' => ((h'.met _).form_eq ch hy _ _ hyU).symm.trans (hd' σ' yc y e u U W hU f f' hyU)) K hK

theorem eig_inv_le {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {C : ℝ} (hC : x.IsMuExp C) (σ : κ.c.F →+* ℂ) (R R' : ℝ) (y : CxPts (genStr s.T.Z) σ)
    (hy : ¬ LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    ((((x.r σ y ^ C) ^ 2 : ℝ) : ℂ) • ((x.eigMetAt σ (some R')).gram y g τ)⁻¹ -
      ((x.eigMetAt σ (some R)).gram y g τ)⁻¹).PosSemidef := by
  have hr0 : 0 < x.r σ y := (Real.exp_pos 1).trans_le (x.exp_le_r σ y)
  have hm : 0 < x.r σ y ^ C := Real.rpow_pos_of_pos hr0 _
  have hA := (x.eigMetAt σ (some R)).pos y g τ
  have hB := (x.eigMetAt σ (some R')).pos y g τ
  have h0 := (x.eigMet σ).pos y g τ
  have c1 := (InterpMetricLog.cmp_interp x hC σ R y hy g τ).inv hA h0 hm
  have c2 := (InterpMetricLog.cmp_interp x hC σ R' y hy g τ).inv hB h0 hm
  have e : ((((x.r σ y ^ C) ^ 2 : ℝ) : ℂ) • ((x.eigMetAt σ (some R')).gram y g τ)⁻¹ -
      ((x.eigMetAt σ (some R)).gram y g τ)⁻¹) =
      ((x.r σ y ^ C : ℝ) : ℂ) • (((x.r σ y ^ C : ℝ) : ℂ) • ((x.eigMetAt σ (some R')).gram y g τ)⁻¹ -
        ((x.eigMet σ).gram y g τ)⁻¹) +
      ((((x.r σ y ^ C : ℝ) : ℂ) • ((x.eigMet σ).gram y g τ)⁻¹) - ((x.eigMetAt σ (some R)).gram y g τ)⁻¹) := by
    rw [sq, Complex.ofReal_mul, mul_smul, smul_sub]
    abel
  rw [e]
  exact (c2.2.smul (Complex.zero_le_real.2 hm.le)).add c1.1

theorem chartGram_le {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c) (σ : O.κ.c.F →+* ℂ) (R R' : ℝ)
    (y : CxPts M.q (σ.comp _)) (hy : Inner (up M.b rfl σ y))
    (ch : Chart ((Scheme.Modules.pullback M.b).obj (omega O.s.T.Z.t.G)) (D.R.f * O.N))
    (hch : y ∈ ptsIn M.q (σ.comp _) ch.U) :
    (((((M.x.r σ (up M.b rfl σ y) ^ M.x.muExp) ^ 2 : ℝ) : ℂ) • (((M.h R').pull M.b rfl).met (σ.comp _)).G ch y) -
      (((M.h R).pull M.b rfl).met (σ.comp _)).G ch y).PosSemidef := by
  obtain ⟨u⟩ := EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z ℂ σ (up M.b rfl σ y).1 (up M.b rfl σ y).2
  exact chartGram_le_of_eig (fun σ' => M.x.eigMetAt σ' (some R)) (fun σ' => M.x.eigMetAt σ' (some R')) M.b
    ((M.h R).pull M.b rfl) ((M.h R').pull M.b rfl) (MetFam.isDualEigOn_pull (M.dual R) M.b rfl)
    (MetFam.isDualEigOn_pull (M.dual R') M.b rfl) σ (up M.b rfl σ y) y (up_ι M.b rfl σ y).symm u _
    (fun τ => eig_inv_le M.x M.x.isMuExp_muExp' σ R R' _ hy u τ) ch hch

theorem abs_log_nsq_le : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (m : ℕ) (sc : (lbPow M.lamB m).Sec),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : O.κ.c.F →+* ℂ) (R : ℝ) (y : CxPts M.q (σ.comp _)), Inner (up M.b rfl σ y) →
      |Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ sc) y) / 2 -
        Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ sc) y) / 2| ≤ C * Real.log (M.x.r σ (up M.b rfl σ y)) := by
  intro D O c M m sc
  have hμ : 0 ≤ M.x.muExp := M.x.isMuExp_muExp'.1
  refine ⟨m * (D.R.f * O.N : ℕ) * M.x.muExp, by positivity, ?_⟩
  intro σ R y hy
  have hr0 : 0 < M.x.r σ (up M.b rfl σ y) := (Real.exp_pos 1).trans_le (M.x.exp_le_r σ _)
  have hr1 : 1 ≤ M.x.r σ (up M.b rfl σ y) := by
    linarith [Real.add_one_le_exp (1 : ℝ), M.x.exp_le_r σ (up M.b rfl σ y)]
  have hlr : 0 ≤ Real.log (M.x.r σ (up M.b rfl σ y)) := Real.log_nonneg hr1
  have hjy := mem_pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y
  have hch := mem_pow_iff.1 hjy
  have key : ∀ R R' : ℝ, Real.log ((((M.h R).pull M.b rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).G
      (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y PUnit.unit) y).det.re ≤
      (D.R.f * O.N : ℕ) * (2 * (M.x.muExp * Real.log (M.x.r σ (up M.b rfl σ y)))) +
      Real.log ((((M.h R').pull M.b rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).G
        (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y PUnit.unit) y).det.re := by
    intro R R'
    have hK := chartGram_le M σ R R' y hy _ hch
    have hA := (((M.h R).pull M.b rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).posDef _ y hch
    have hB := (((M.h R').pull M.b rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).posDef _ y hch
    have d := CompMetric.det_re_le_of_sub (by positivity) hA hK (1 : Matrix (Fin (D.R.f * O.N)) (Fin (D.R.f * O.N)) ℂ)
    simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at d
    have pa := det_re_pos hA
    have pb := det_re_pos hB
    have l := Real.log_le_log pa d
    rw [Real.log_mul (by positivity) pb.ne', Real.log_pow, Real.log_pow, Real.log_rpow hr0] at l
    push_cast at l ⊢
    linarith
  have eR : ∀ R : ℝ, (((M.lam R).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).nsq (secVal M.q _ sc) y =
      ‖secVal M.q _ sc (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y) y‖ ^ 2 *
        Real.exp (-(m * -Real.log ((((M.h R).pull M.b rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).G
          (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y PUnit.unit) y).det.re)) := by
    intro R
    simp only [Weight.nsq, HermLB.pow, Weight.pow]
    erw [Weight.zpow_φ]
    rfl
  rw [eR R, eR 2]
  by_cases hs : ‖secVal M.q _ sc (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y) y‖ = 0
  · rw [hs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, Real.log_zero, zero_div, sub_self,
      abs_zero]
    positivity
  · have ha : 0 < ‖secVal M.q _ sc (pick (((M.lam 2).pow m).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isLB y) y‖ ^ 2 := by positivity
    rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_exp]
    have k1 := key R 2
    have k2 := key 2 R
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [abs_le]
    constructor <;> nlinarith

end GlobalTheory.LogNormCmp
