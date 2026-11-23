import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionaryStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
noncomputable section
namespace GlobalTheory.KerConjRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Jets
open Formalism.L2.Ker
end Jets
section Row
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
end Row
theorem conjugate_row_mem_kernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 →
    BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  intro _ hInp hDict _ C1 hC1
  obtain ⟨K, hK0, hFock⟩ := GlobalTheory.FockJetBound.jetOp_norm_le
  obtain ⟨CF0, h⟩ := BigC.and (BigC.and hDict rowSizes) GlobalTheory.KerConjMean.TopSizes.sizesK
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (24 * (6 + 126 * K) + 36 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨hA, hwt⟩, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, -⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 24 * (6 + 126 * K) + 36 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hlog4 : Real.log (4 * large₂.sc.b) ≤ 3 * Real.log large₂.sc.b := by
    calc _ ≤ Real.log (large₂.sc.b ^ 3) := Real.log_le_log (by linarith) (by nlinarith [mul_le_mul hb3 hb3 (by norm_num) (by linarith)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 32 * D.R.f * bigN D * large₂.sc.b,
    4 * D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨L, hL⟩ : ∃ L, L = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g, g = fF D * (ch.G.V (.grid (j + 1) D.R.m)).rank * (ch.G.V (.grid j D.R.m)).rank := ⟨_, rfl⟩
    obtain ⟨H, harea, hdiff, hgr, hfeq⟩ := row_jets ch (hInp D) hA hocc c j fm hfm σ hρ L hL g hg
    have hp : DefPair D.R.m (.chi j D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨j.2, rfl⟩
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.grid j D.R.m)) (wt ch.G (.grid (j + 1) D.R.m)) _
      (wtOK_of_defPair ch.G _ hp).2
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area L)⁻¹ := by
      unfold hArea; rw [hL]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hL]
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.grid j D.R.m)).rank with ha
    set bb := (ch.G.V (.grid ((j : ℕ) + 1) D.R.m)).rank with hbb
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)
    have hrk : ∀ jj : ℕ, jj ≤ D.R.m → ((ch.G.V (.grid jj D.R.m)).rank : ℝ) ≤ bigN D := fun jj hjj => by
      exact_mod_cast GlobalTheory.DefRank.rank_le_bigN ch.G (.grid jj D.R.m) ⟨hjj, rfl⟩
    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * (4 * large₂.sc.b)) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.grid jj D.R.m)).rank, (8 * (4 * large₂.sc.b)) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hwt jj τ i).trans (by linarith)
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.grid jj D.R.m)).rank : ℝ) * (8 * (4 * large₂.sc.b))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * (4 * large₂.sc.b))) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right (hrk jj hjj) (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := hrk j j.2.le
    have hbN : (bb : ℝ) ≤ bigN D := hrk _ (Nat.succ_le_of_lt j.2)
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg, mul_right_comm]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) (4 * large₂.sc.b) D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0
      (Nat.cast_nonneg _) (by exact_mod_cast hcard) (by linarith) hN1' (by linarith) hf1' (by linarith)
      hrd0 (by linarith) (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ 12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]
      refine hc0.trans ((mul_le_mul_of_nonneg_left hlog4 (by positivity)).trans (le_of_eq ?_))
      ring
    have hdN : (deg : ℝ) ≤ 32 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := Real.posLog_nonneg
    have hpX : 0 ≤ Real.posLog X := Real.posLog_nonneg
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp (12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 32 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        4 * D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg *
          nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)
end GlobalTheory.KerConjRow
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjRowAt_of_dict_depth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  first | exact @_root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel | exact _root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel | (intros; apply _root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel <;> assumption)
end
