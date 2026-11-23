import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jdc_thrW (o : ℕ) (A d : ℝ) (hd : 0 ≤ d)
    (h : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  unfold Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  rw [hn] at h
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) <
      12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by
    nlinarith [pow_nonneg hr 3, mul_nonneg hr (mul_nonneg hk hk), mul_nonneg (mul_nonneg hr hr) hk,
      mul_nonneg hr hr, mul_nonneg hr hk, mul_nonneg hk hk]
  have hpos : 0 < 12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  constructor <;> linarith

theorem jdc_om_sub_gpos (Db : B.RealPlaceData k r Wp Wq) : JF.Om k r Db.z Db.z' ⊆ B.GPos Db := by
  intro g hg
  unfold JF.Om Q.OmPlus at hg
  unfold B.GPos
  exact ⟨hg.1, hg.2.2⟩

theorem jdc_om_of (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (h : 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0) :
    g ∈ JF.Om k r z z' := by
  refine ⟨hg, ?_, h.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | h0
  · have e : l = ⟨0, by omega⟩ := Fin.ext h0
    rw [e]
    unfold Formalism.QuantumDeterminants.Dmin
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have e : l = ⟨((⟨l.val - 1, by omega⟩ : Fin r) : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact h.2 _

theorem jdc_of_om (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0 := by
  unfold JF.Om Q.OmPlus at hg
  obtain ⟨_, hD, hG⟩ := hg
  exact ⟨hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩

end gen

section gen2

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem jdc_ckOn_mono {m : ℕ∞} {UU VV : Set (B.Mat k r)} (h : UU ⊆ VV) {f : B.Mat k r → E₁} (hf : B.CkOn m VV f) :
    B.CkOn m UU f := by
  intro g₀ hg₀
  exact hf g₀ (h hg₀)

theorem jdc_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  unfold B.CkOn at *
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', hea⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hg₂, hΦ', heΦ⟩ := hΦ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have hr : ContDiffOn ℝ _ (fun g => (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ) (a' g)) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (ha'.mono Set.inter_subset_left)
    exact hr.clm_apply (hΦ'.mono Set.inter_subset_right)
  · intro g hg hgG
    simp only [hea g hg.1 hgG, heΦ g hg.2 hgG]

theorem jdc_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end gen2

section gen3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem jdc_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (jdc_ckOn_ap (h T (by simp)) (jdc_ckOn_Rw T.word_lie hJ))
      (jdc_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem jdc_ckOn_om (z z' : Fin (2 * r + k + 1) → ℂ) {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : Q.SmoothLev k r 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} J) :
    B.CkOn ⊤ (JF.Om k r z z') J := by
  unfold B.CkOn
  unfold Q.SmoothLev at hJ
  intro g₀ hg₀
  unfold JF.Om Q.OmPlus at hg₀
  obtain ⟨hgG, hD, hG⟩ := hg₀
  have hmem : g₀ ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    ⟨⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ g₀ hmem
  refine ⟨U, F, hU, hgU, hF, ?_⟩
  intro g hg hgV
  exact hJF g hg ⟨hgV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

variable [FiniteDimensional ℂ Wp]

theorem jdc_ffl (Db : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hSC : B.SmoothCoef (B.GPos Db) Θ)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (hH : ∀ g ∈ JF.Om k r Db.z Db.z', B.opApply Θ J g = B.JF Db H g) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := jdc_om_of _ _ hg₀.1.1 hg₀.2
    have hck := jdc_ckOn_opApply (jdc_ckOn_om Db.z Db.z' hJ.1) Θ
      (fun T hT => jdc_ckOn_mono (jdc_om_sub_gpos Db) (hSC T hT).1)
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hck g₀ hg₀O
    refine ⟨U ∩ Q.OmPlus k r Db.z Db.z', f', hU.inter (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _), ⟨hgU, hg₀O.2⟩,
      hc.mono Set.inter_subset_left, ?_⟩
    intro g hg hgG
    have hgO : g ∈ JF.Om k r Db.z Db.z' := ⟨hgG.1, hg.2⟩
    rw [← hH g hgO]
    exact he g hg.1 hgG.1
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

end gen3

theorem transfer_commutation_holds : JDJComm := by
  refine ⟨12, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d A hd hSC hC _hG hA F _hCk hCC hJF
  have hT := jdc_thrW (k := S.G.k) (r := S.G.r) (B.opOrder Θ) A d hd hA
  have hCOm : B.Commutes (T v).base (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') Θ :=
    fun p hp f' hf' g hg => hC p hp f' hf' g (jdc_om_sub_gpos _ hg)
  have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ (T v).base A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT (hCC _) hCOm
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨jdc_ffl (T v).base Θ hSC hJF _ hth, ?_⟩
  intro x hx
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  exact hth _ (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq)

end

end Formalism.FourierDecayAlt.P.CutMP
