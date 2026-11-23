import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.MeasConjM
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNBoxHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMSLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj.InfCut
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem place_eq {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Q' : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Q' = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {t : ℝ} (ht : 0 < t)
    (hc : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = (t : ℂ) ^ (r - (a : ℕ)) • e a ∧
      Q *ᵥ Pi.single (esI k r a) 1 = (star ((t : ℂ) ^ (r - (a : ℕ))))⁻¹ • f a) (κ : ℝ≥0∞) :
    (haarLie (Nset k r) κ).comap (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (trG Q Q' γ) : Mt k r)) =
      (κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • refNg hn ε e f wf (z0v T z) := by
  subst hn
  have hF := JX.isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hF
  have emb' : MeasurableEmbedding (cM (ε := ε) Q' Q) := cM_measEmb (A' := Q) (B' := Q') h2 h2
  set P := Qm e f wf (z0v T z) with hP
  set P' := Qi ε e f wf (z0v T z) with hP'
  have p1 : P' * P = 1 := Qi_mul_Qm hF
  have p2 : P * P' = 1 := Qm_mul_Qi hF
  have hdi : (P' * Q)⁻¹ = Q' * P := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h2, Matrix.one_mul, p1]
  have hd : P' * Q ∈ UH (Hpk k r) := by
    show (P' * Q)ᴴ * Hpk k r * (P' * Q) = Hpk k r
    calc _ = Qᴴ * (P'ᴴ * Hpk k r * P') * Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [QiHQi hF, hg]
  have hmap := conj_levi hd ht
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).1, Matrix.mulVec_smul, ← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec])
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).2, Matrix.mulVec_smul, ← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec]
      simp)
  have hcomp : cM (ε := ε) P' P = conjM (P' * Q) ∘ cM (ε := ε) Q' Q := by
    funext g
    show P' * uMat g * P = P' * Q * (Q' * uMat g * Q) * (P' * Q)⁻¹
    rw [hdi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q' P, h2, Matrix.one_mul, ← Matrix.mul_assoc Q Q', h2, Matrix.one_mul]
  have hu : IsUnit (P' * Q).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hd
  have hinj : Function.Injective (conjM (k := k) (r := r) (P' * Q)) := fun x y h => by
    have h' : P' * Q * Matrix.of x * (P' * Q)⁻¹ = P' * Q * Matrix.of y * (P' * Q)⁻¹ := h
    have := congrArg (fun m => (P' * Q)⁻¹ * m * (P' * Q)) h'
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
    exact this
  have hκ : haarLie (Nset k r) κ = κ • haarLie (Nset k r) 1 := by simp [haarLie]
  ext s hs
  show (haarLie (Nset k r) κ).comap (cM (ε := ε) Q' Q) s =
    ((κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • (haarLie (Nset k r) 1).comap (cM (ε := ε) P' P)) s
  rw [emb'.comap_apply, Measure.smul_apply, emb.comap_apply, hκ, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  have h3 := congrArg (fun m : Measure (Mt k r) => m (cM (ε := ε) P' P '' s)) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  rw [← h3, Measure.map_apply (meas_conjM _) (emb.measurableSet_image.2 hs), hcomp, Set.image_comp,
    Set.preimage_image_eq _ hinj]

theorem pi_smul {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  have : ∀ i, SigmaFinite ((c : ℝ≥0∞) • μ i) := fun i => inferInstanceAs (SigmaFinite (c • μ i))
  refine Measure.pi_eq fun s _ => ?_
  simp [Measure.pi_pi, Finset.prod_mul_distrib]

theorem kap_real (k r : ℕ) :
    (B.kap k r : ℝ) = (4 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 2 * r) / 3 + k * ((r : ℝ) ^ 2 + r) := by
  have hs : B.kap k r = ∑ j ∈ Finset.range r, 2 * (2 * (j + 1) + k) * (j + 1) := by
    unfold B.kap Mdim
    rw [Fin.sum_univ_eq_sum_range (fun a => 2 * (2 * (r - a) + k + 1 - 1) * (r - a)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show r - (r - 1 - j) = j + 1 by omega]
    rfl
  rw [hs]
  clear hs
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.cast_add, ih]; push_cast; ring

def iF {D : D7} (X : HidaSetting D) : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    ((X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply] at h'
      exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h'),
     fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem disc_rd (D : D7) (X : HidaSetting D) : |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f := by
  refine Formalism.L2.SG.Pf.Carrier.EnergyMS.discRd_of (fun D X => ?_) finrank_E D X
  have hE : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.E X.ιE
  have hF : NumberField.discr X.B.I.F = NumberField.discr D.host.F :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.F (iF X)
  rw [hE, hF, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  push_cast
  rw [abs_pow]

theorem covariance_formula : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  intro D X Y θ C u hθ
  set ρ : ℝ := 2 * D.host.v with hρ
  have hρ1 : 1 ≤ ρ := Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D
  have hρ0 : 0 < ρ := by linarith
  have hrd : D.host.rdE = ρ := by rw [hρ]; unfold Formalism.BasicNotions.Host.v; ring
  have hfr : frS D = ((ρ⁻¹ : ℝ) : ℂ) := by
    unfold frS Formalism.BasicNotions.Host.ka
    congr 1
    have hv : D.host.v ≠ 0 := by intro h; rw [hρ, h] at hρ0; simp at hρ0
    rw [hρ]
    field_simp
  set c : ℝ≥0∞ := Formalism.MainNotions.S.kapN D θ * ENNReal.ofReal (((ρ⁻¹) ^ B.kap D.R.k D.R.rS)⁻¹) with hcdef
  have hloc : ∀ (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F), vOf X τ = v →
      Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ v = c • refNX X u v := by
    rintro τ v rfl
    obtain ⟨-, h2, hg, hcol⟩ := C.isT τ
    rw [hfr] at hcol
    exact place_eq (nX X) _ (eV X _) (ProductExactness.pV X _) (X.wfr u _) (ProductExactness.zV X u _) (ProductExactness.Tw_pos u) (fX_ee X _) (fX_ff X _)
      (fX_ef X _) (fX_ww X u _) (fX_ew X u _) (fX_fw X u _) (fX_ez X u _) (fX_fz X u _) (frame_real_z_z_eq_neg X u _) (fX_zw X u _)
      (C.Q τ) (C.Qi τ) h2 hg (inv_pos.2 hρ0) (fun a => hcol a a rfl) _
  have hv : Formalism.L2.SG.Pf.AmpWinGlob.muNv C = fun v => c • refNX X u v :=
    funext fun v => hloc (X.pl v) v (X.pl.symm_apply_apply v)
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
        SigmaFinite (Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ w) := by
      rintro τ w rfl
      exact Formalism.L2.SG.Pf.AmpWinLoc.sf_muNl C τ hθ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  have : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have hcov : Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) =
      Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) (Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hce : c = ENNReal.ofReal (ρ ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * ρ ^ (B.kap D.R.k D.R.rS : ℝ)) := by
    rw [hcdef, inv_pow, inv_inv, Real.rpow_natCast, ENNReal.ofReal_mul (by positivity)]
    rfl
  have href := covol_refN (covolN_of_coordCovol (coordCovol_of kapLaw_holds NOf.nofib_holds CovB.blockCovol_holds))
    refNBox_holds X u u (Y.FN u) (Y.FN_fund u)
  have hcard : Fintype.card (InfinitePlace X.B.I.F) = Fintype.card D.what₂.Tau := Fintype.card_congr X.pl
  have hf : D.R.f = Fintype.card D.what₂.Tau := D.what₂.card_Tau.symm
  unfold Formalism.L2.SG.LoopTerm.covN
  rw [hcov, hv, pi_smul _ (by rw [hce]; exact ENNReal.ofReal_ne_top), Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    href, disc_rd D X, hrd, hf, hcard, hce, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ← Real.rpow_natCast ρ, ← Real.rpow_mul hρ0.le, mul_comm ((Fintype.card D.what₂.Tau : ℕ) : ℝ), Real.rpow_mul hρ0.le,
    Real.rpow_natCast (ρ ^ Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k), ← mul_pow]
  congr 1
  have e : Formalism.L2.SG.Pf.LoopBCovN.eN D = -((D.R.rS : ℝ) * D.R.k) + (B.kap D.R.k D.R.rS : ℝ) +
      Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k := by
    rw [kap_real]
    unfold Formalism.L2.SG.Pf.LoopBCovN.eN Formalism.L2.SG.Pf.LsNc5.covolumeExponent
    ring
  rw [e, Real.rpow_add hρ0, Real.rpow_add hρ0]
  ring

end Formalism.MainStatements.RowRest
