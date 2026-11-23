import CompanionTheory.AutomorphicTheory.NumberFieldModels.TransferGaugeGeneratorZbarInv
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.MainStatements.NFTie

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def trL (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) :
    Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] (M.Ty P → MA.SmQ P.r P.TT) where
  toFun := tr P Bs e
  map_add' := tr_add hpl hk he
  map_smul' a Φ := trR_smul _ _ a _

theorem baseTie (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hG : GaugeQQ P Bs e) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Formalism.FourierDecayAlt.P.NormalFormRelations.BaseTie X (trL hpl hk he) where
  op l j := by
    fin_cases j
    · exact transfer_operator_p hpl hk he X l
    · exact transfer_operator_c hpl hk he X l
    · exact transfer_operator_c_inv hpl hk he X l
    · exact transfer_operator_pbar hpl hk he X l
    · exact transfer_operator_cbar hpl hk he X l
    · exact transfer_operator_cbar_inv hpl hk he X l
  fn j := by
    fin_cases j
    · exact transfer_gauge_generator_z hpl hk he X
    · exact transfer_gauge_generator_z_inv hpl hk he X
    · exact transfer_gauge_generator_zbar hpl hk he X
    · exact transfer_gauge_generator_zbar_inv hpl hk he X
    · exact transfer_gauge_generator_ggi hpl hk he X
    · exact transfer_gauge_generator_gg_inv hpl hk he X
  t Y a b := transfer_torus_action hpl hk he X hG Y a b

theorem tie_cpt (p : KB.Pl P Wp Wq) {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P p.T.base e)
    (hG : GaugeQQ P p.T.base e) {Lm : R.LevelData (MA.A P (MA.DQ P)) P.r} (hM : MA.IsModelLevel P (MA.DQ P) Lm)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (a : Wd.Ix (Fin w.length))
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) :
    (∃ Φ, Top.IsRadOf P p.T.base Φ (p.Θ.Θ w a F)) ∧
      trJB P p.T.base e (B.JF p.T.base (p.Θ.Θ w a F)) =
        MA.actA P (Formalism.FourierDecayAlt.P.NormalFormRelations.gM P p.l0 Lm (D.positionted w) a) (trJB P p.T.base e (B.JF p.T.base F)) := by
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  obtain ⟨hl1, hlk, hk⟩ := p.hl
  obtain ⟨L', hM', hsl, hS, -⟩ := Formalism.FourierDecayAlt.P.model_frame_analytic P hD.1.1 p.l0 hl1 hlk
  obtain rfl := modelLevel_unique hM hM'
  have hadm : Fr.admitted st (D.positionted w) := (Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 hl1 hlk
    hD.2.2.2.2.1 hD.2.2.2.2.2.1 w hw.1 hw.2).1
  obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P.PBN.radExists p hF
  have h1 := hTL w hw F hF Φ hΦ a
  refine ⟨⟨_, h1⟩, ?_⟩
  rw [trJB_of_rad hD.1 h1, trJB_of_rad hD.1 hΦ]
  exact Formalism.FourierDecayAlt.P.NormalFormRelations.word_tied hD (baseTie hD.1 hk he hG X) hM hsl hS (D.positionted w) hadm Φ a

theorem evQ_trJB (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : Top.IsRadOf P Bs Φ H)
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    MA.evQ P (trJB P Bs e (B.JF Bs H) ρ) q = rawJ P Bs e (B.JF Bs H) ρ q := by
  rw [trJB_of_rad hpl h, tc_rawJ]
  show ((trR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _
  rw [trR_val hpl hk he (famR_rad hpl Φ) ρ q]
  have := h _ (mu_domR hpl q)
  simp only at this
  simp only [rawR, this]

theorem jf_mem_fib (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : (Fin P.r → ℂ) × ℂ) :
    B.JF Bs H (B.gq Bs x) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' x.2 := by
  rintro ⟨h, h'⟩ ⟨hh, hh', hst⟩
  simp only at hh hh' hst ⊢
  rw [← Formalism.FourierDecayAlt.P5.jf_uEquiv Bs H _ hh hh']
  congr 1
  have hc := Formalism.FourierDecayAlt.P.Qx3.wlist_comm (k := P.k) (Fin.last P.r) x.1
    ((List.finRange P.r).filter fun a => a.val < (Fin.last P.r).val)
    (fun a ha => by simpa using (List.mem_filter.1 ha).2) (Formalism.FourierDecayAlt.P.Qx3.uw_glev (Fin.last P.r) hh)
  change Q.wCell P.k P.r (Fin.last P.r) x.1 * h = h * Q.wCell P.k P.r (Fin.last P.r) x.1 at hc
  rw [tc_gq, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc h, hst]

theorem wq_nonneg (q : MA.Qp P.r P.TT) : 0 ≤ MA.wq P.k q.1 P.TT := by
  unfold MA.wq
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (Complex.normSq_nonneg _) _)
    (pow_nonneg (sub_nonneg.2 (le_of_lt q.2.2)) _)

theorem parseval (he : IsFrameB P Bs e) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (q : MA.Qp P.r P.TT) :
    ∑ ρ, ‖rawJ P Bs e (B.JF Bs H) ρ q‖ ^ 2 = MA.wq P.k q.1 P.TT * ‖B.hsVec (B.JF Bs H (B.gq Bs q.1))‖ ^ 2 := by
  obtain ⟨-, -, hsp⟩ := he.2 q.1.2 q.2.2
  set X := B.JF Bs H (B.gq Bs q.1) with hX
  have hx := hsp X (jf_mem_fib H q.1)
  have h1 : B.hsVec X = ∑ ρ, inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec X) • B.hsVec (e ρ q.1.2) := by
    conv_lhs => rw [hx]
    rw [tc_hsVec_sum]
    simp only [tc_hsVec_smul]
  have h2 : ((‖B.hsVec X‖ ^ 2 : ℝ) : ℂ) = ((∑ ρ, ‖inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec X)‖ ^ 2 : ℝ) : ℂ) := by
    have e0 : inner ℂ (B.hsVec X) (B.hsVec X) = ((‖B.hsVec X‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← e0]
    conv_lhs => enter [3]; rw [h1]
    rw [inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [inner_smul_right, ← inner_conj_symm (B.hsVec X), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [Complex.ofReal_injective h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [rawJ]
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (wq_nonneg q)]

theorem gf_gq (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    Gf P.k P.r Bs.z Bs.z' (B.gq Bs q.1) = MA.Gq P q := by
  have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs _ (mu_domR hpl q)).2.2.2
  simp only at h
  rw [tc_gq, h, gg_mu hpl q, MA.Gq, map_prod]

theorem rawJ_Gpow (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (s : ℕ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawJ P Bs e (B.JF Bs fun g => ((Gf P.k P.r Bs.z Bs.z' g ^ s : ℝ) : ℂ) • F g) ρ q =
      ((MA.Gq P q ^ s : ℝ) : ℂ) * rawJ P Bs e (B.JF Bs F) ρ q := by
  have h := Formalism.FourierDecayAlt.P.JCTx2.JF_cutF Bs (fun x => x ^ s) F 1 (B.gq Bs q.1)
  unfold D.cutF at h
  simp only [div_one] at h
  simp only [rawJ]
  rw [h, gf_gq hpl q, hsV_smul, inner_smul_right]
  ring

theorem jf_cpt_FF {k r : ℕ} (Db : B.RealPlaceData k r Wp Wq) {H : B.Mat k r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef Db H) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 (OmB Db) := by
  obtain ⟨ε, -, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hH
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := Formalism.FourierDecayAlt.P.CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2
    exact Formalism.FourierDecayAlt.P5.Rad.jf_smoothLev Db H hn.2.1 g₀ ⟨hg₀.1, hg₀O.2⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

theorem hsVec_proj_le (E : Wp →L[ℂ] Wp) (h1 : E.comp E = E) (h2 : ∀ v v' : Wp, inner ℂ (E v) v' = inner ℂ v (E v'))
    (X : Wq →L[ℂ] Wp) : ‖B.hsVec (E.comp X)‖ ^ 2 ≤ ‖B.hsVec X‖ ^ 2 := by
  have hv : ∀ v : Wp, ‖E v‖ ≤ ‖v‖ := by
    intro v
    have e1 : inner ℂ (E v) (E v) = inner ℂ v (E v) := by
      rw [h2]; congr 1; exact congrArg (fun T : Wp →L[ℂ] Wp => T v) h1
    have e2 : ‖E v‖ ^ 2 ≤ ‖v‖ * ‖E v‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) v (E v)
      rw [← e1, inner_self_eq_norm_sq_to_K] at this
      simpa using this
    by_cases h0 : ‖E v‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hp : 0 < ‖E v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [sq] at e2
      exact le_of_mul_le_mul_right e2 hp
  unfold B.hsVec
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv _) 2

end

end Formalism.MainStatements.NFTie
