import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section left

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sE (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) : B.Mat k n := D.castM e (PBQ.sP Bj x)

open Classical in

def gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (x : PBQ.XP k p ρ)
    (g : B.Mat k n) : Wq →L[ℂ] Wp :=
  if PBQ.GoodP Bj x then (Bj.π (Matrix.of x.1.1)).comp (Ψ (sE Bj e x * g)) else 0

def TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (g : B.Mat k n) :
    Wq →L[ℂ] Wp :=
  ∫ x, PBQ.cP Bj x • gI Bj e Ψ x g ∂(PBQ.muXP Bj)

theorem pbF_eq_TI (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) : PBQ.pbF Bj B0 e H = TI Bj e (PBG.Kr B0 H) := by
  funext g
  unfold PBQ.pbF TI
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  simp [PBQ.pbI, gI, hx, sE]

theorem isLowerUni_one {d : ℕ} : G.IsLowerUni (1 : Matrix (Fin d) (Fin d) ℂ) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  simp only [Matrix.transpose_apply, Matrix.one_apply]
  rw [if_neg (ne_of_lt hij)]

theorem leftFactor_mem (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) :
    PBQ.sP Bj x ∈ Sset k (p + ρ) (liftVec k p ρ Bj.z) := by
  by_cases hx : PBQ.GoodP Bj x
  · rw [PBQ.sP, if_pos hx]
    have h := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.left_factor_mem k p ρ Bj.z (-x.2) 1 (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem
      isLowerUni_one hx.1 hx.2
    rwa [Matrix.conjTranspose_one, inv_one, Formalism.FourierDecayAlt.P.PBH.muP_one', Matrix.mul_one] at h
  · rw [PBQ.sP, if_neg hx]
    exact Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k (p + ρ) _

theorem sP_GV (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) : PBQ.sP Bj x ∈ B.GV k (p + ρ) :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub (leftFactor_mem Bj x)

theorem sE_GV (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) : sE Bj e x ∈ B.GV k n :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV e (sP_GV Bj x)

theorem sE_mem_S (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) :
    sE Bj e x ∈ Sset k n (D.castV e (liftVec k p ρ Bj.z)) := by
  subst e
  simp only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact leftFactor_mem Bj x

theorem goodP_closed (Bj : B.RealPlaceData k ρ Wp Wq) : IsClosed {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} := by
  have h1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)) := continuous_fst.fst
  have h2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  exact ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z).preimage h1).inter ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage h2)

theorem leftFactor_continuousOn (Bj : B.RealPlaceData k ρ Wp Wq) :
    ContinuousOn (fun x : PBQ.XP k p ρ => PBQ.sP Bj x) {x | PBQ.GoodP Bj x} := by
  have h1 : Continuous (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2)) :=
    (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd.neg
  have hof1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)) := continuous_fst.fst
  have hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  have hi1 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun x hx => hx.1.1)
  have hi2 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof2.continuousOn (fun x hx => hx.2.1)
  have hf : ContinuousOn (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2) *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)) {x | PBQ.GoodP Bj x} :=
    h1.continuousOn.mul ((Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp_continuousOn (hi1.mul hi2))
  refine hf.congr (fun x hx => ?_)
  simp only [PBQ.sP, if_pos (show PBQ.GoodP Bj x from hx)]

theorem sE_contOn (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) :
    ContinuousOn (fun x : PBQ.XP k p ρ => sE Bj e x) {x | PBQ.GoodP Bj x} := by
  subst e
  simp only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact leftFactor_continuousOn Bj

theorem norm_cP (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) : ‖PBQ.cP Bj x‖ ≤ 1 := by
  unfold PBQ.cP
  rw [norm_mul, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, one_mul]

theorem continuous_characterProduct (Bj : B.RealPlaceData k ρ Wp Wq) : Continuous (fun x : PBQ.XP k p ρ => PBQ.cP Bj x) := by
  unfold PBQ.cP
  have hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  exact ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of Bj.z cStd).comp hof2).mul
    ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of (liftVec k p ρ Bj.z) cStd).comp
      ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd))

theorem norm_gI_le (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp))
    (x : PBQ.XP k p ρ) (g : B.Mat k n) : ‖gI Bj e Ψ x g‖ ≤ ‖Ψ (sE Bj e x * g)‖ := by
  unfold gI
  split_ifs with hx
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.opNorm_pi_le Bj hx.1
    exact (mul_le_of_le_one_left (norm_nonneg _) this)
  · simp

theorem xp_borel : BorelSpace (PBQ.XP k p ρ) := by
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
  exact Prod.borelSpace

theorem gI_aesm (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : ContinuousOn Ψ (B.GV k n)) {g : B.Mat k n} (hg : g ∈ B.GV k n) :
    AEStronglyMeasurable (fun x => gI Bj e Ψ x g) (PBQ.muXP Bj) := by
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  set S := {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} with hSdef
  have hπ : ContinuousOn (fun x : PBQ.XP k p ρ => Bj.π (Matrix.of x.1.1)) S :=
    Bj.π_cont.comp (continuous_fst.fst : Continuous fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)).continuousOn
      (fun x hx => hx.1)
  have hs : ContinuousOn (fun x => sE Bj e x * g) S := (sE_contOn Bj e).mul continuousOn_const
  have hΨ' : ContinuousOn (fun x => Ψ (sE Bj e x * g)) S :=
    hΨ.comp hs (fun x _ => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg)
  have hcont : ContinuousOn (fun x => (Bj.π (Matrix.of x.1.1)).comp (Ψ (sE Bj e x * g))) S := hπ.clm_comp hΨ'
  have hm := hcont.aestronglyMeasurable (μ := PBQ.muXP Bj) (goodP_closed Bj).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (s := S) (PBQ.ae_goodP (p := p) Bj)] at hm
  refine hm.congr ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  simp [gI, hx]

end left

section deriv

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

def VanishL (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k n)) :
    Prop :=
  ∀ y ∈ U, ∃ V : Set (B.Mat k n), IsOpen V ∧ y ∈ V ∧ ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧
    ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K → Ψ (sE Bj e x * g) = 0

theorem fmoc_XP (Bj : B.RealPlaceData k ρ Wp Wq) : IsFiniteMeasureOnCompacts (PBQ.muXP (p := p) Bj) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : IsFiniteMeasureOnCompacts Bj.μW := ⟨fun K hK => Bj.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts Bj.μN := ⟨fun K hK => Bj.haarN.finite_compact K hK⟩
  have := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.fmoc_RC (k := k) (p := p) (ρ := ρ)
  unfold PBQ.muXP
  infer_instance

theorem img_cpt (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {K : Set (PBQ.XP k p ρ)} (hK : IsCompact K)
    {Kc : Set (B.Mat k n)} (hKc : IsCompact Kc) (hKcG : Kc ⊆ B.GV k n) :
    ∃ S : Set (B.Mat k n), IsCompact S ∧ S ⊆ B.GV k n ∧
      ∀ x ∈ K, PBQ.GoodP Bj x → ∀ g ∈ Kc, sE Bj e x * g ∈ S := by
  refine ⟨(fun q : PBQ.XP k p ρ × B.Mat k n => sE Bj e q.1 * q.2) '' ((K ∩ {x | PBQ.GoodP Bj x}) ×ˢ Kc), ?_, ?_, ?_⟩
  · refine ((hK.inter_right (goodP_closed Bj)).prod hKc).image_of_continuousOn ?_
    exact ((sE_contOn Bj e).comp continuous_fst.continuousOn (fun q hq => hq.1.2)).mul continuous_snd.continuousOn
  · rintro _ ⟨q, hq, rfl⟩
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e q.1) (hKcG hq.2)
  · intro x hx hg g hgK
    exact ⟨(x, g), ⟨⟨hx, hg⟩, hgK⟩, rfl⟩

theorem rdV_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Ψ : B.Mat k n → E) (s g X : B.Mat k n) :
    RdV X (fun g' => Ψ (s * g')) g = RdV X Ψ (s * g) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

theorem rdV_zero_of_vanish {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ψ : B.Mat k n → E}
    {s : B.Mat k n} {V : Set (B.Mat k n)} (hV : IsOpen V) (h : ∀ g ∈ V, g ∈ B.GV k n → Ψ (s * g) = 0)
    {g : B.Mat k n} (hg : g ∈ V) (hgG : g ∈ B.GV k n) {X : B.Mat k n} (hX : inLie k n X) : RdV X Ψ (s * g) = 0 := by
  rw [← rdV_transl, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr (f₂ := fun _ => (0 : E)) hV hg hgG hX (fun x hx hxG => h x hx hxG)]
  simp [RdV]

theorem ckOn_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {m : ℕ∞} {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn m (GV k n) Ψ) (x : PBQ.XP k p ρ) : CkOn m (GV k n) (gI Bj e Ψ x) := by
  by_cases hx : PBQ.GoodP Bj x
  · have e1 : gI Bj e Ψ x = fun g =>
        (ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1))) (Ψ (sE Bj e x * g * 1)) := by
      funext g; simp [gI, hx]
    rw [e1]
    exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hΨ (sE_GV Bj e x) Formalism.QuantumDeterminants.WeylGroupFacts.uh_one) _
  · have e1 : gI Bj e Ψ x = fun _ => 0 := by funext g; simp [gI, hx]
    rw [e1]; exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _

theorem op_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn 1 (GV k n) Ψ) {X : B.Mat k n} (hX : inLie k n X) (x : PBQ.XP k p ρ) {g : B.Mat k n}
    (hg : g ∈ GV k n) : op false X (gI Bj e Ψ x) g = gI Bj e (RdV X Ψ) x g := by
  by_cases hx : PBQ.GoodP Bj x
  · set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1)) with hL
    have e1 : gI Bj e Ψ x = fun g' => L (Ψ (sE Bj e x * g')) := by
      funext g'; simp [gI, hx, hL]
    rw [e1]
    have e2 : gI Bj e (RdV X Ψ) x g = L (RdV X Ψ (sE Bj e x * g)) := by simp [gI, hx, hL]
    rw [e2]
    have hc := Formalism.FourierDecayAlt.P.B5.ckOn_curve hΨ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg) hX
    have hd := (hc.differentiable one_ne_zero 0).hasDerivAt
    have e3 : (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) =
        fun t : ℝ => L (Ψ (sE Bj e x * g * NormedSpace.exp ((t : ℂ) • X))) := by
      funext t; simp only [cv, Matrix.mul_assoc]
    show deriv (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) 0 = _
    rw [e3]
    have h5 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    exact h5.deriv
  · have e1 : gI Bj e Ψ x = fun _ => 0 := by funext g; simp [gI, hx]
    rw [e1]
    simp [op, gI, hx]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rdV_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) {X : B.Mat k n} (hX : inLie k n X)
    {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    Integrable (fun x => PBQ.cP Bj x • gI Bj e (RdV X Ψ) x y) (PBQ.muXP Bj) ∧
      RdV X (TI Bj e Ψ) y = TI Bj e (RdV X Ψ) y := by
  have := fmoc_XP (p := p) Bj
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨V, hVo, hyV, K, hK, hvan⟩ := hv y hyU
  have hΨ1 : CkOn 1 (GV k n) Ψ := Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hΨ
  have hΨc : ContinuousOn Ψ (GV k n) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hΨ
  have hRΨ : CkOn ⊤ (GV k n) (RdV X Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hΨ)
  have hRc : ContinuousOn (RdV X Ψ) (GV k n) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hRΨ
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, cv false X t y ∈ V := by
    have ho : IsOpen ((fun t : ℝ => cv false X t y) ⁻¹' V) := hVo.preimage (cv_continuous false X y)
    have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv false X t y) ⁻¹' V := by
      show cv false X 0 y ∈ V; rw [cv_zero]; exact hyV
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 ho 0 h0
    exact ⟨ε, hε, fun t ht => hb ht⟩
  set Kc := (fun t : ℝ => cv false X t y) '' Metric.closedBall (0 : ℝ) (ε / 2) with hKcdef
  have hKc : IsCompact Kc := (isCompact_closedBall _ _).image (cv_continuous false X y)
  have hKcG : Kc ⊆ GV k n := by rintro _ ⟨t, _, rfl⟩; exact cv_mem hX hy t
  obtain ⟨S, hS, hSG, hSmem⟩ := img_cpt Bj e hK hKc hKcG
  obtain ⟨M1, hM1⟩ := hS.exists_bound_of_continuousOn (hΨc.mono hSG)
  obtain ⟨M2, hM2⟩ := hS.exists_bound_of_continuousOn (hRc.mono hSG)
  set M := max (max M1 M2) 0 with hMdef
  set β : PBQ.XP k p ρ → ℝ := K.indicator (fun _ => M) with hβdef
  have hβI : Integrable β (PBQ.muXP Bj) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hmemKc : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ Kc :=
    fun t ht => ⟨t, Metric.ball_subset_closedBall ht, rfl⟩
  have hinV : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ V :=
    fun t ht => hball t (Metric.ball_subset_ball (by linarith) ht)
  have hb1 : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), ∀ x,
      ‖op false X (gI Bj e Ψ x) (cv false X t y)‖ ≤ β x := by
    intro t ht x
    rw [op_gI Bj e hΨ1 hX x (cv_mem hX hy t)]
    by_cases hxK : x ∈ K
    · rw [hβdef, Set.indicator_of_mem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · exact (norm_gI_le Bj e _ x _).trans ((hM2 _ (hSmem x hxK hx _ (hmemKc t ht))).trans
          (le_trans (le_max_right _ _) (le_max_left _ _)))
      · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
    · rw [hβdef, Set.indicator_of_notMem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · have hz : RdV X Ψ (sE Bj e x * cv false X t y) = 0 :=
          rdV_zero_of_vanish hVo (fun g hg hgG => hvan g hg hgG x hx hxK) (hinV t ht) (cv_mem hX hy t) hX
        simp [gI, hx, hz]
      · simp [gI, hx]
  have hb0 : ∀ x, ‖gI Bj e Ψ x (cv false X 0 y)‖ ≤ β x := by
    intro x
    rw [cv_zero]
    by_cases hxK : x ∈ K
    · rw [hβdef, Set.indicator_of_mem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · have hyKc : y ∈ Kc := by
          have := hmemKc 0 (Metric.mem_ball_self hε2); rwa [cv_zero] at this
        exact (norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y hyKc)).trans
          (le_trans (le_max_left _ _) (le_max_left _ _)))
      · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
    · rw [hβdef, Set.indicator_of_notMem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · simp [gI, hx, hvan y hyV hy x hx hxK]
      · simp [gI, hx]
  have key := step_loc (μ := PBQ.muXP Bj) (b := false) hX (fun x => PBQ.cP Bj x) (norm_cP Bj)
    (continuous_characterProduct Bj).aestronglyMeasurable (gI Bj e Ψ) (fun x => ckOn_gI Bj e hΨ1 x) hy hε2
    (fun t _ => gI_aesm Bj e hΨc (cv_mem hX hy t))
    ((gI_aesm Bj e hRc hy).congr (Eventually.of_forall fun x => (op_gI Bj e hΨ1 hX x hy).symm))
    β hβI (fun x => by have := hb0 x; rwa [cv_zero] at this) hb1 (TI Bj e Ψ) (fun t _ => rfl)
  refine ⟨?_, ?_⟩
  · refine hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hRc hy))
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_
    have := hb1 0 (Metric.mem_ball_self hε2) x
    rwa [cv_zero, op_gI Bj e hΨ1 hX x hy] at this
  · show op false X (TI Bj e Ψ) y = _
    rw [key]
    unfold TI
    congr 1
    funext x
    rw [op_gI Bj e hΨ1 hX x hy]

end deriv

section fold

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem gI_top (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (u : ℂ)
    (a b : Fin (2 * n + k + 1)) (x : PBQ.XP k p ρ) (g : B.Mat k n) :
    gI Bj e (Top (Q.EH k n) u a b Ψ) x g =
      (if a = b then u • gI Bj e Ψ x g else 0) +
        (gI Bj e (RdV (Xa k n a b) Ψ) x g + Complex.I • gI Bj e (RdV (Xb k n a b) Ψ) x g) := by
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx, top_apply', EH_apply]
    split_ifs <;> simp [ContinuousLinearMap.comp_add]
  · simp [gI, hx]

theorem vanish_top (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) (u : ℂ) (a b : Fin (2 * n + k + 1)) :
    VanishL Bj e (Top (Q.EH k n) u a b Ψ) U := by
  intro y hy
  obtain ⟨V, hV, hyV, K, hK, h⟩ := hv y hy
  refine ⟨V, hV, hyV, K, hK, fun g hg hgG x hx hxK => ?_⟩
  have h0 : ∀ g' ∈ V, g' ∈ GV k n → Ψ (sE Bj e x * g') = 0 := fun g' a b => h g' a b x hx hxK
  rw [top_apply', EH_apply, h g hg hgG x hx hxK, rdV_zero_of_vanish hV h0 hg hgG (Xa_unit a b).1,
    rdV_zero_of_vanish hV h0 hg hgG (Xb_unit a b).1]
  simp

theorem ckOn_top {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)} (hΨ : CkOn ⊤ (GV k n) Ψ) (u : ℂ) (a b : Fin (2 * n + k + 1)) :
    CkOn ⊤ (GV k n) (Top (Q.EH k n) u a b Ψ) := by
  have hA : CkOn ⊤ (GV k n) (RdV (Xa k n a b) Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xa_unit a b).1 (by simpa using hΨ)
  have hB : CkOn ⊤ (GV k n) (RdV (Xb k n a b) Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xb_unit a b).1 (by simpa using hΨ)
  by_cases hab : a = b
  · have e1 : Top (Q.EH k n) u a b Ψ = u • Ψ + (RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ) := by
      funext g; rw [top_apply', EH_apply, if_pos hab]; rfl
    rw [e1]
    exact Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hΨ)
      (Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB))
  · have e1 : Top (Q.EH k n) u a b Ψ = RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ := by
      funext g; rw [top_apply', EH_apply, if_neg hab, zero_add]; rfl
    rw [e1]
    exact Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB)

theorem int_lin {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (P : Prop) [Decidable P] (u : ℂ) {f0 fA fB : α → V}
    (h0 : Integrable f0 μ) (hA : Integrable fA μ) (hB : Integrable fB μ) :
    ∫ x, ((if P then u • f0 x else 0) + (fA x + Complex.I • fB x)) ∂μ =
      (if P then u • ∫ x, f0 x ∂μ else 0) + (∫ x, fA x ∂μ + Complex.I • ∫ x, fB x ∂μ) := by
  have hB' : Integrable (fun x => Complex.I • fB x) μ := hB.smul Complex.I
  have hAB : Integrable (fun x => fA x + Complex.I • fB x) μ := hA.add hB'
  split_ifs
  · have h0' : Integrable (fun x => u • f0 x) μ := h0.smul u
    rw [integral_add h0' hAB, integral_add hA hB', integral_smul, integral_smul]
  · simp only [zero_add]
    rw [integral_add hA hB', integral_smul]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem int_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨc : ContinuousOn Ψ (GV k n)) {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) {y : B.Mat k n}
    (hyU : y ∈ U) (hy : y ∈ GV k n) : Integrable (fun x => PBQ.cP Bj x • gI Bj e Ψ x y) (PBQ.muXP Bj) := by
  have := fmoc_XP (p := p) Bj
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  obtain ⟨V, hVo, hyV, K, hK, hvan⟩ := hv y hyU
  obtain ⟨S, hS, hSG, hSmem⟩ := img_cpt Bj e hK (isCompact_singleton (x := y)) (Set.singleton_subset_iff.2 hy)
  obtain ⟨M1, hM1⟩ := hS.exists_bound_of_continuousOn (hΨc.mono hSG)
  have hβI : Integrable (K.indicator (fun _ => max M1 0)) (PBQ.muXP Bj) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  refine hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hΨc hy)) (Eventually.of_forall fun x => ?_)
  rw [norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    by_cases hx : PBQ.GoodP Bj x
    · exact (norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y (Set.mem_singleton y))).trans (le_max_left _ _))
    · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
  · rw [Set.indicator_of_notMem hxK]
    by_cases hx : PBQ.GoodP Bj x
    · simp [gI, hx, hvan y hyV hy x hx hxK]
    · simp [gI, hx]

theorem foldT_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) :
    ∀ ts : List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1)),
      CkOn ⊤ (GV k n) (foldT ts Ψ) ∧ VanishL Bj e (foldT ts Ψ) U ∧
        ∀ y ∈ U, y ∈ GV k n → foldT ts (TI Bj e Ψ) y = TI Bj e (foldT ts Ψ) y
  | [] => ⟨hΨ, hv, fun _ _ _ => rfl⟩
  | t :: ts => by
    have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
    obtain ⟨hc, hvv, ih⟩ := foldT_TI Bj e hΨ hU hv ts
    have e0 : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) :=
      fun f => rfl
    refine ⟨by rw [e0]; exact ckOn_top hc _ _ _, by rw [e0]; exact vanish_top Bj e hvv _ _ _, fun y hyU hy => ?_⟩
    have hA := rdV_TI Bj e hc hvv (Xa_unit t.2.1 t.2.2).1 hyU hy
    have hB := rdV_TI Bj e hc hvv (Xb_unit t.2.1 t.2.2).1 hyU hy
    have hI0 := int_gI Bj e (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hc) hvv hyU hy
    have hL : foldT (t :: ts) (TI Bj e Ψ) y = (if t.2.1 = t.2.2 then t.1 • TI Bj e (foldT ts Ψ) y else 0) +
        (TI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) y +
          Complex.I • TI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) y) := by
      rw [e0, top_apply', EH_apply,
        rdV_congr hU hyU hy (Xa_unit _ _).1 (fun x hx hxG => ih x hx hxG),
        rdV_congr hU hyU hy (Xb_unit _ _).1 (fun x hx hxG => ih x hx hxG), ih y hyU hy, hA.2, hB.2]
    have hR : TI Bj e (foldT (t :: ts) Ψ) y = (if t.2.1 = t.2.2 then t.1 • TI Bj e (foldT ts Ψ) y else 0) +
        (TI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) y +
          Complex.I • TI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) y) := by
      have hf : (fun x => PBQ.cP Bj x • gI Bj e (foldT (t :: ts) Ψ) x y) = fun x =>
          (if t.2.1 = t.2.2 then t.1 • (PBQ.cP Bj x • gI Bj e (foldT ts Ψ) x y) else 0) +
            (PBQ.cP Bj x • gI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) x y +
              Complex.I • (PBQ.cP Bj x • gI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) x y)) := by
        funext x
        rw [e0, gI_top]
        split_ifs
        · rw [smul_add, smul_add, smul_comm (PBQ.cP Bj x) t.1, smul_comm (PBQ.cP Bj x) Complex.I]
        · rw [smul_add, smul_zero, smul_add, smul_comm (PBQ.cP Bj x) Complex.I]
      unfold TI
      rw [hf, int_lin _ _ hI0 hA.1 hB.1]
    rw [hL, hR]

end fold

section aa

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem foldT_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : B.Mat k n) :
    ∀ (ts : List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1))) (Ψ : B.Mat k n → E),
      foldT ts (fun g => Ψ (s * g)) = fun g => foldT ts Ψ (s * g)
  | [], _ => rfl
  | t :: ts, Ψ => by
    have e0 : ∀ f : B.Mat k n → E, foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) := fun f => rfl
    funext g
    rw [e0, e0, top_apply', top_apply', EH_apply, EH_apply, foldT_transl s ts Ψ, rdV_transl, rdV_transl]

theorem qminor_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : B.Mat k n) {t : ℕ}
    (a b : Fin t → Fin (2 * n + k + 1)) (u : ℂ) (Ψ : B.Mat k n → E) (g : B.Mat k n) :
    qminorOp (EabH (Hpk k n)) a b u (fun g' => Ψ (s * g')) g = qminorOp (EabH (Hpk k n)) a b u Ψ (s * g) := by
  rw [Formalism.FourierDecayAlt.P.PBG.qminor_foldT, Formalism.FourierDecayAlt.P.PBG.qminor_foldT]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldT_transl]

theorem comp_fsum {ι : Type*} (A : Wp →L[ℂ] Wp) (s : Finset ι) (c : ι → ℂ) (v : ι → (Wq →L[ℂ] Wp)) :
    A.comp (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • A.comp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ih]

theorem gI_sum (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (F : ι → B.Mat k n → (Wq →L[ℂ] Wp)) (x : PBQ.XP k p ρ) (g : B.Mat k n) :
    gI Bj e (fun g' => ∑ i ∈ s, c i • F i g') x g = ∑ i ∈ s, c i • gI Bj e (F i) x g := by
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]; exact comp_fsum _ s c _
  · simp [gI, hx]

theorem int_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {ι : Type*} (s : Finset ι) (a : ℂ) (b : ι → ℂ) (f : ι → α → V)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ x, a • ∑ i ∈ s, b i • f i x ∂μ = a • ∑ i ∈ s, b i • ∫ x, f i x ∂μ := by
  rw [integral_smul, integral_finsetSum s (f := fun i x => b i • f i x) (fun i hi => (hf i hi).smul (b i))]
  simp_rw [integral_smul]

open Classical in

def cfA (m : ℕ) (hm : m ≤ n) (g : B.Mat k n) (c : Fin m → Fin (2 * n + k + 1)) : ℂ :=
  if StrictMono c then
    (Matrix.of fun a l : Fin m => herm (Hpk k n) (g *ᵥ bvec (c l)) (bvec (eI k n (Fin.castLE hm a)))).det
  else 0

open Classical in

def cfV (m : ℕ) (hm : m ≤ n) (g : B.Mat k n) (c : Fin m → Fin (2 * n + k + 1)) : ℂ :=
  if StrictMono (fun l => C3.keyS k n (c l)) then
    (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k n (Fin.castLE hm a))) (c l)).det
  else 0

theorem AAop_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (hm : m ≤ n) (u : ℂ)
    (f : B.Mat k n → E) (g : B.Mat k n) :
    C3.AAop k n m hm u f g = ∑ c : Fin m → Fin (2 * n + k + 1),
      cfA m hm g c • qminorOp (EabH (Hpk k n)) (C3.xR k n m hm) c u f g := by
  unfold C3.AAop cfA
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem AAvop_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (hm : m ≤ n) (ell : ℂ)
    (f : B.Mat k n → E) (g : B.Mat k n) :
    C3.AAvop k n m hm ell f g = ∑ c : Fin m → Fin (2 * n + k + 1),
      cfV m hm g c • qminorOp (EabH (Hpk k n)) c (C3.sR k n m hm) (ell + (m : ℂ) - 1) f g := by
  unfold C3.AAvop cfV
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem qminor_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) {t : ℕ}
    (a b : Fin t → Fin (2 * n + k + 1)) (u : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    Integrable (fun x => PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) x y) (PBQ.muXP Bj) ∧
      qminorOp (EabH (Hpk k n)) a b u (TI Bj e Ψ) y = TI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) y := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j) with hts
  have hq : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), qminorOp (EabH (Hpk k n)) a b u f =
      fun g => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • foldT (ts σ) f g :=
    fun f => funext fun g => Formalism.FourierDecayAlt.P.PBG.qminor_foldT a b u f g
  have hF := fun σ => foldT_TI Bj e hΨ hU hv (ts σ)
  have hI : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      Integrable (fun x => PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y) (PBQ.muXP Bj) :=
    fun σ _ => int_gI Bj e (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (hF σ).1) (hF σ).2.1 hyU hy
  have hfun : (fun x => PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) x y) = fun x =>
      (1 : ℂ) • ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • (PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y) := by
    funext x
    rw [hq, one_smul, gI_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_finsetSum _ fun σ hσ => (hI σ hσ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).smul (1 : ℂ)
  · have lhs : qminorOp (EabH (Hpk k n)) a b u (TI Bj e Ψ) y =
        ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • TI Bj e (foldT (ts σ) Ψ) y := by
      rw [Formalism.FourierDecayAlt.P.PBG.qminor_foldT]
      exact Finset.sum_congr rfl fun σ _ => by rw [(hF σ).2.2 y hyU hy]
    rw [lhs]
    unfold TI
    rw [hfun, int_comb _ 1 _ _ hI, one_smul]

open Classical in

theorem AA_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) (m : ℕ) (hm : m ≤ n)
    (u : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    C3.AAop k n m hm u (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAop k n m hm u (fun g => Ψ (sE Bj e x * g)) y) else 0) ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hI := fun c => qminor_TI Bj e hΨ hU hv (C3.xR k n m hm) c u hyU hy
  have hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAop k n m hm u (fun g => Ψ (sE Bj e x * g)) y) else 0) =
      (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfA m hm y c •
        (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) (C3.xR k n m hm) c u Ψ) x y) := by
    intro x
    by_cases hx : PBQ.GoodP Bj x
    · rw [if_pos hx, AAop_sum, comp_fsum, one_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [qminor_transl, smul_comm]
      simp [gI, hx]
    · simp [gI, hx]
  rw [AAop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(hI c).2]; rfl

open Classical in

theorem AAv_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) (m : ℕ) (hm : m ≤ n)
    (ell : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    C3.AAvop k n m hm ell (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAvop k n m hm ell (fun g => Ψ (sE Bj e x * g)) y) else 0)
        ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hI := fun c => qminor_TI Bj e hΨ hU hv c (C3.sR k n m hm) (ell + (m : ℂ) - 1) hyU hy
  have hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAvop k n m hm ell (fun g => Ψ (sE Bj e x * g)) y) else 0) =
      (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfV m hm y c •
        (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) c (C3.sR k n m hm) (ell + (m : ℂ) - 1) Ψ) x y) := by
    intro x
    by_cases hx : PBQ.GoodP Bj x
    · rw [if_pos hx, AAvop_sum, comp_fsum, one_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [qminor_transl, smul_comm]
      simp [gI, hx]
    · simp [gI, hx]
  rw [AAvop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(hI c).2]; rfl

end aa

section vlet

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Classical in

theorem vLet_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U)
    (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n) (l : C.Letter) (ε : Fin 2) {y : B.Mat k n}
    (hyU : y ∈ U) (hy : y ∈ GV k n) :
    D.vLet k n z z' i hi l ε (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (D.vLet k n z z' i hi l ε (fun g => Ψ (sE Bj e x * g)) y) else 0)
        ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  by_cases h0 : ε = 1 ∧ i = 0
  · simp [D.vLet, h0]
  · by_cases hl : l.1 = true
    · simp only [D.vLet, h0, hl, if_false, if_true]
      rw [AA_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : PBQ.GoodP Bj x
      · simp only [if_pos hx]
        rw [ContinuousLinearMap.comp_smul, smul_comm]
      · simp [hx]
    · simp only [D.vLet, h0, hl, if_false]
      rw [AAv_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : PBQ.GoodP Bj x
      · simp only [if_pos hx, Bool.false_eq_true, if_false]
        rw [ContinuousLinearMap.comp_smul, smul_comm]
      · simp [hx]

theorem smoothOnH_of_ckOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k n → E}
    (hf : CkOn ⊤ (GV k n) f) : SmoothOnH (Hpk k n) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc, fun x hx hxG => he x hx hxG⟩

theorem vLet_pb (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) {Ht : B.Mat k n → (Wq →L[ℂ] Wp)} (hHt : CkOn ⊤ (GV k n) Ht)
    {Cs : Set (B.Mat k n)} (hCs : IsCompact Cs) (hS : ∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) {U : Set (B.Mat k n)}
    (hU : IsOpen U) (hv : VanishL Bj e (PBG.Kr B0 Ht) U) (i : ℕ) (hi : i ≤ n) (l : C.Letter) (ε : Fin 2)
    {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) (hD : Dmin k n B0.z B0.z' y ⟨i, by omega⟩ ≠ 0) :
    D.vLet k n B0.z B0.z' i hi l ε (PBQ.pbF Bj B0 e Ht) y =
      PBQ.pbF Bj B0 e (D.vLet k n B0.z B0.z' i hi l ε Ht) y := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hK : CkOn ⊤ (GV k n) (PBG.Kr B0 Ht) := fun g hg => Formalism.FourierDecayAlt.P.PBG.kr_loc_cpt B0 hHt hCs hS g hg
  have hKs : SmoothOnH (Hpk k n) (PBG.Kr B0 Ht) := smoothOnH_of_ckOn hK
  obtain ⟨R, hR⟩ := hCs.exists_bound_of_continuousOn (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn (s := Cs))
  have hRb : ∃ R : ℝ, ∀ g ∈ B.GV k n, Ht g ≠ 0 → B.gN g ≤ R := by
    refine ⟨R, fun g hg hne => ?_⟩
    by_contra hgt
    have hgC : g ∈ Cs := by
      by_contra hgC; exact hne (hS g hg hgC)
    have := hR g hgC
    rw [Real.norm_eq_abs] at this
    exact hgt ((le_abs_self _).trans this)
  have hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ Ht g :=
    fun g hg _ => hHt g hg
  rw [pbF_eq_TI, pbF_eq_TI, vLet_TI Bj e hK hU hv _ _ i hi l ε hyU hy]
  unfold TI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]
    have hs : sE Bj e x ∈ Sset k n B0.z := hzS ▸ sE_mem_S Bj e x
    have hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z' := Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'
    have hmem : sE Bj e x * y ∈ B.GV k n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy
    have hD' : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ ≠ 0 := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this]; exact hD
    have htr := Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_transl B0.z B0.z' B0.z_mem B0.z'_mem i hi l ε hKs hs hs1 hy
    simp only [Matrix.mul_one] at htr
    rw [← htr, ((Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm k n Wp Wq B0 i hi Ht hL hRb _ hmem hD').2 l ε)]
  · simp [gI, hx]

end vlet

end Formalism.FourierDecayAlt.P.PartialBesselProperness
