import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransportToLastLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstBasisVectorIsRadialSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isOpen_UT (k r : ℕ) (z z' : Fin (2 * (r - r) + k + 1) → ℂ) : IsOpen (UT k r z z') := by
  have h1 : Continuous fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1).det :=
    Continuous.matrix_det (continuous_fst)
  have h2 : Continuous fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      Q.GGl k (r - r) z z' (Matrix.of q.2) :=
    (Formalism.FourierDecayAlt.P.Qx8.GGl_cont k (r - r) z z').comp continuous_snd
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_lt continuous_const h2)

section asm

theorem omX_zero {r : ℕ} (c : Fin (r - r) → ℂ) : c ∈ OmX (r - r) := fun l => by
  exfalso; have := l.isLt; omega

theorem parFam_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
    {z z' : Fin (2 * (r - r) + k + 1) → ℂ} {f : (Fin r → Fin r → ℂ) × Mt k (r - r) → E}
    (hf : PBI.ParFam k (r - r) (UT k r z z') f) (Z : Fin r → Fin r → ℂ) (hZ : (Matrix.of Z).det ≠ 0) :
    ∀ g₀ : Q.Mx k (r - r), g₀ ∈ Q.Glev k (r - r) (Fin.last (r - r)) → 0 < Q.GGl k (r - r) z z' g₀ →
      ∃ (U : Set (Q.Mx k (r - r))) (F : Q.Mx k (r - r) → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
        ∀ g ∈ U, g ∈ Q.Glev k (r - r) (Fin.last (r - r)) → f (Z, Matrix.of.symm g) = F g := by
  intro g₀ hg₀ hG
  obtain ⟨U', F', hU', hq, hF', hag⟩ := hf (Z, Matrix.of.symm g₀) ⟨hZ, hG⟩ hg₀
  have hc : Continuous fun g : Q.Mx k (r - r) => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r)) :=
    continuous_const.prodMk continuous_id
  have hcd : ContDiff ℝ ∞ fun g : Q.Mx k (r - r) => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r))) ⁻¹' U', fun g => F' (Z, Matrix.of.symm g),
    hU'.preimage hc, hq, hF'.comp hcd.contDiffOn (fun g hg => hg), fun g hg hgG => hag _ hg hgG⟩

end asm

section closed

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem det_upUni {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : Formalism.DoubleCosetMeasures.IsUpUni u) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular hu.1]
  simp [hu.2]

theorem isClosed_upUni (n : ℕ) : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | Formalism.DoubleCosetMeasures.IsUpUni u} := by
  have h1 : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | u.IsUpperTriangular} := by
    have : {u : Matrix (Fin n) (Fin n) ℂ | u.IsUpperTriangular} = ⋂ i, ⋂ j, ⋂ (_ : j < i), {u | u i j = 0} := by
      ext u; simp [Matrix.IsUpperTriangular, Matrix.BlockTriangular]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have h2 : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | ∀ a, u a a = 1} := by
    have : {u : Matrix (Fin n) (Fin n) ℂ | ∀ a, u a a = 1} = ⋂ a, {u | u a a = 1} := by ext; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_eq ((continuous_apply a).comp (continuous_apply a)) continuous_const
  exact h1.inter h2

theorem isClosed_KU {n : ℕ} {Y : Type} [MetricSpace Y] {K : Set ((Fin n → Fin n → ℂ) × Y)} (hK : IsCompact K)
    (hKd : ∀ q ∈ K, (Matrix.of q.1).det ≠ 0) :
    IsClosed {q : (Fin n → Fin n → ℂ) × Y | ∃ u : Matrix (Fin n) (Fin n) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K} := by
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨s, hsK, hs⟩ := mem_closure_iff_seq_limit.1 hq
  choose u hu hus using hsK
  obtain ⟨W, hWK, φ, hφ, hlim⟩ := hK.tendsto_subseq hus

  have hdetc : Continuous fun q : (Fin n → Fin n → ℂ) × Y => (Matrix.of q.1).det :=
    Continuous.matrix_det continuous_fst
  have hd1 : Tendsto (fun m => (Matrix.of (s (φ m)).1).det) atTop (nhds (Matrix.of q.1).det) :=
    (hdetc.tendsto q).comp (hs.comp hφ.tendsto_atTop)
  have he : ∀ m, (Matrix.of (Matrix.of.symm (Matrix.of (s (φ m)).1 * u (φ m)), (s (φ m)).2).1).det =
      (Matrix.of (s (φ m)).1).det := by
    intro m; simp [Matrix.det_mul, det_upUni (hu (φ m))]
  have hd2 : Tendsto (fun m => (Matrix.of (s (φ m)).1).det) atTop (nhds (Matrix.of W.1).det) :=
    ((hdetc.tendsto W).comp hlim).congr (fun m => by simp only [Function.comp_apply]; exact he m)
  have hdq : (Matrix.of q.1).det = (Matrix.of W.1).det := tendsto_nhds_unique hd1 hd2
  have hqd : (Matrix.of q.1).det ≠ 0 := by rw [hdq]; exact hKd W hWK

  have hinv : Tendsto (fun m => (Matrix.of (s (φ m)).1)⁻¹) atTop (nhds (Matrix.of q.1)⁻¹) := by
    have hc : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℂ => M⁻¹) (Matrix.of q.1) :=
      continuousAt_matrix_inv _ (by simpa [Ring.inverse, isUnit_iff_ne_zero] using hqd)
    exact hc.tendsto.comp ((continuous_fst.tendsto q).comp (hs.comp hφ.tendsto_atTop))
  have hW1 : Tendsto (fun m => Matrix.of (s (φ m)).1 * u (φ m)) atTop (nhds (Matrix.of W.1)) :=
    ((continuous_fst.tendsto W).comp hlim).congr (fun m => rfl)
  have hu' : Tendsto (fun m => u (φ m)) atTop (nhds ((Matrix.of q.1)⁻¹ * Matrix.of W.1)) := by
    have := hinv.mul hW1
    refine this.congr' (Eventually.of_forall fun m => ?_)
    have hdm : (Matrix.of (s (φ m)).1).det ≠ 0 := by
      rw [← he m]; exact hKd _ (hus (φ m))
    simp only
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdm), Matrix.one_mul]
  have hUU : Formalism.DoubleCosetMeasures.IsUpUni ((Matrix.of q.1)⁻¹ * Matrix.of W.1) :=
    (isClosed_upUni n).mem_of_tendsto hu' (Eventually.of_forall fun m => hu (φ m))
  refine ⟨_, hUU, ?_⟩
  have hY : Tendsto (fun m => (s (φ m)).2) atTop (nhds W.2) :=
    ((continuous_snd.tendsto W).comp hlim).congr (fun m => rfl)
  have hY' : Tendsto (fun m => (s (φ m)).2) atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp (hs.comp hφ.tendsto_atTop)
  have hq2 : q.2 = W.2 := tendsto_nhds_unique hY' hY
  have e1 : Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of W.1) = Matrix.of W.1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hqd), Matrix.one_mul]
  rw [e1, hq2]
  exact hWK

end closed

theorem exceptional_assumption_holds : Asm := by
  intro hUw hST hPS hPR hPSupp hPE hMk hMC hTP hZx hHF hRST hROF hRE hRT hFP hRW hPicS
  intro Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  classical
  have hr0 : P.r - P.r = 0 := by omega

  obtain ⟨F₁, hF₁, hloc, hsl, K₁, hK₁c, hK₁0, hK₁⟩ := exists_compact_cutoff_coefficient p F hF h hh
  have hT₁ : TopCls p.T.base F₁ := ⟨hF₁, K₁, hK₁c, hK₁0, fun g _ hne => hK₁ g hne⟩

  set u : Wd.Ix (Fin w.length) → B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
    fun e' => D.uwG P.k P.r p.T.base.z p.T.base.z' F₁ P.r le_rfl w e' with hu
  have hTu : ∀ e', TopCls p.T.base (u e') := fun e' => hUw Wp Wq P p F₁ hT₁ w e'

  have hAdm : Fr.admitted st (D.positionted w) :=
    admissible_of_range Wp Wq (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 w p.hl.1 p.hl.2.1 hD hcut
  have hAdm₀ : Fr.admitted st₀ (D.positionted w) :=
    admissible_of_range Wp Wq P _ _ _ _ X₀ μ₀ L₀ st₀ p.l0 w p.hl.1 p.hl.2.1 hD₀ hcut

  set Ψf : (Fin P.r → Fin P.r → ℂ) → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z e' y => if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
      pbTop p (u e') (Matrix.of Z) (Matrix.of y) else 0 with hΨfdef
  have hΨf_pos : ∀ Z e' y, (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      Ψf Z e' y = pbTop p (u e') (Matrix.of Z) (Matrix.of y) := fun Z e' y hq => if_pos hq
  have hΨUT : ∀ e' (q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)),
      q ∉ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' → Ψf q.1 e' q.2 = 0 := fun e' q hq => if_neg hq
  have hΨsm : ∀ e', PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      (fun q => Ψf q.1 e' q.2) := by
    intro e' q₀ hq₀ hq₀G
    obtain ⟨U, Fe, hU, hq₀U, hFe, hag⟩ := hPS Wp Wq P p (u e') (hTu e') q₀ hq₀ hq₀G
    exact ⟨U ∩ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z', Fe, hU.inter (isOpen_UT _ _ _ _), ⟨hq₀U, hq₀⟩,
      hFe.mono Set.inter_subset_left, fun q hq hqG => (hΨf_pos q.1 e' q.2 hq.2).trans (hag q hq.1 hqG)⟩
  have hΨsupp : ∀ e', ∃ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K ∧
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
      ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        Ψf q.1 e' q.2 ≠ 0 →
        ∃ v : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni v ∧ (Matrix.of.symm (Matrix.of q.1 * v), q.2) ∈ K :=
    by
    intro e'
    obtain ⟨K, hKc, hKU, hK⟩ := hPSupp Wp Wq P p (u e') (hTu e')
    refine ⟨K, hKc, hKU, fun q hqG hne => ?_⟩
    by_cases hq : q ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [hΨf_pos q.1 e' q.2 hq] at hne
      exact hK q hq.1 hqG hne
    · exact absurd (hΨUT e' q hq) hne
  choose Ku hKuc hKuU hKu using hΨsupp
  have hΨex : ∀ (Z : Fin P.r → Fin P.r → ℂ) (e' : Wd.Ix (Fin w.length)),
      ∃ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∀ c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e' y := by
    intro Z e'
    by_cases hZ : (Matrix.of Z).det ≠ 0
    · obtain ⟨Ψ, hΨ⟩ := hROF Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π'
        (fun g => pbTop p (u e') (Matrix.of Z) g) (parFam_slice (hPS Wp Wq P p (u e') (hTu e')) Z hZ)
        (fun g hg hG h₁ hh₁ h₂ hh₂ => hPE Wp Wq P p (u e') (hTu e') (Matrix.of Z) hZ g hg h₁ hh₁ h₂ hh₂)
      refine ⟨Ψ, fun c y hy => ?_⟩
      by_cases hG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)
      · exact (hΨ (c, Matrix.of y) ⟨omX_zero c, hy, hG⟩).trans (hΨf_pos Z e' y ⟨hZ, hG⟩).symm
      · exact (Ψ.2.1 (c, Matrix.of y) (fun hx => hG hx.2.2)).trans
          (hΨUT e' (Z, y) (fun hq => hG hq.2)).symm
    · refine ⟨0, fun c y hy => ?_⟩
      show (0 : Wq →L[ℂ] Wp) = _
      symm
      exact hΨUT e' (Z, y) (fun hq => hZ hq.1)
  choose Ψ hΨ using hΨex

  obtain ⟨Φf, hΦval, hΦsm, hΦsupp, hΦswap⟩ := hFP Wp Wq P p X μ L st hD w hAdm (Fin P.r → Fin P.r → ℂ)
    (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (isOpen_UT _ _ _ _) (fun q hq => ⟨trivial, hq.2⟩) Ψ Ψf
    (fun Z e' c y hy => hΨ Z e' c y hy) hΨsm
  set K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)) := ⋃ e', Ku e' with hKdef
  have hKc : IsCompact K := isCompact_iUnion hKuc
  have hKU : K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := Set.iUnion_subset hKuU
  set K'' : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)) :=
    {q | ∃ v : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni v ∧ (Matrix.of.symm (Matrix.of q.1 * v), q.2) ∈ K}
    with hK''def
  have hK''cl : closure K'' = K'' := (isClosed_KU hKc (fun q hq => (hKU hq).1)).closure_eq
  have hΦ0 : ∀ q, q ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K'' → Φf q.1 e q.2 = 0 := by
    intro q hq hqG hqK
    refine hΦsupp K'' (fun e' q' hq' hnot => ?_) e q hq hqG ?_
    · by_contra hne
      obtain ⟨v, hv, hvK⟩ := hKu e' q' hq' hne
      exact hnot ⟨v, hv, Set.mem_iUnion.2 ⟨e', hvK⟩⟩
    · rw [hK''cl]; exact hqK

  have hΨR : ∀ (Z : Fin P.r → Fin P.r → ℂ) (v : Matrix (Fin P.r) (Fin P.r) ℂ), Formalism.DoubleCosetMeasures.IsUpUni v → ∀ e',
      Ψ (Matrix.of.symm (Matrix.of Z * v)) e' = psiU p v • Ψ Z e' := by
    intro Z v hv e'
    refine hRE Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' _ _ fun x hx => ?_
    show (Ψ (Matrix.of.symm (Matrix.of Z * v)) e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
      psiU p v • (Ψ Z e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2
    have h1 := hΨ (Matrix.of.symm (Matrix.of Z * v)) e' x.1 (Matrix.of.symm x.2) hx.2.1
    have h2 := hΨ Z e' x.1 (Matrix.of.symm x.2) hx.2.1
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (fun X => psiU p v • X) h2.symm)
    have hd : (Matrix.of (Matrix.of.symm (Matrix.of Z * v))).det = (Matrix.of Z).det := by
      simp [Matrix.det_mul, det_upUni hv]
    by_cases hq : (Z, Matrix.of.symm x.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · have hq' : (Matrix.of.symm (Matrix.of Z * v), Matrix.of.symm x.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' :=
        ⟨hd ▸ hq.1, hq.2⟩
      rw [hΨf_pos _ e' _ hq', hΨf_pos _ e' _ hq]
      exact hPR Wp Wq P p (u e') (hTu e') (Matrix.of Z) v x.2 hv
    · have hq' : (Matrix.of.symm (Matrix.of Z * v), Matrix.of.symm x.2) ∉ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' :=
        fun h' => hq ⟨hd ▸ h'.1, h'.2⟩
      rw [hΨUT e' (_, _) hq', hΨUT e' (_, _) hq, smul_zero]
  have hΦR : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)) (v : Matrix (Fin P.r) (Fin P.r) ℂ),
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni v →
      Φf (Matrix.of.symm (Matrix.of Z * v)) e y = psiU p v • Φf Z e y := by
    intro Z y v hy hv
    rw [← hΦval _ e (fun _ => 0) y hy, ← hΦval Z e (fun _ => 0) y hy]
    have : Ψ (Matrix.of.symm (Matrix.of Z * v)) = fun e' => psiU p v • Ψ Z e' := funext (hΨR Z v hv)
    rw [this]
    erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
    rfl

  obtain ⟨b, b', β, κ, hb, hbc, hb', hb'c, hκ, hβ, hK', hmk⟩ := hMk Wp Wq P p
  obtain ⟨K', hK'c, hK'U, hK'mem⟩ := hK' K hKc hKU
  classical
  set Φ₀ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z y => if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0 with hΦ₀def
  set Φβ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ₀ Z' y' with hΦβdef
  have hΦβsm : PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (fun q => Φβ q.1 q.2) := by
    intro q₀ hq₀ hq₀G
    obtain ⟨U, Fe, hU, hq₀U, hFe, hag⟩ := hΦsm e q₀ hq₀ hq₀G
    have hβq : ContDiffOn ℝ ∞ (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => β q.1)
        (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') :=
      hβ.comp contDiff_fst.contDiffOn (fun q hq => hq.1)
    refine ⟨U ∩ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z', fun q => β q.1 • κ⁻¹ • Fe q, hU.inter (isOpen_UT _ _ _ _),
      ⟨hq₀U, hq₀⟩, ?_, fun q hq hqG => ?_⟩
    · exact (hβq.mono Set.inter_subset_right).smul ((hFe.const_smul κ⁻¹).mono Set.inter_subset_left)
    · show ((β q.1 : ℝ) : ℂ) • (if (q.1, q.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
          κ⁻¹ • Φf q.1 e q.2 else 0) = β q.1 • κ⁻¹ • Fe q
      rw [if_pos hq.2, Complex.coe_smul]
      rw [show Φf q.1 e q.2 = Fe q from hag q hq.1 hqG]
  have hΦβK : ∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K' → Φβ q.1 q.2 = 0 := by
    intro q hqG hqK
    show ((β q.1 : ℝ) : ℂ) • (if (q.1, q.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf q.1 e q.2 else 0) = 0
    by_cases hβ0 : β q.1 = 0
    · rw [hβ0]; simp
    split_ifs with hq
    · have hqK'' : q ∉ K'' := fun h' => hqK (hK'mem q hq.1 hβ0 h')
      rw [hΦ0 q hq hqG hqK'', smul_zero, smul_zero]
    · rw [smul_zero]
  set F₂ := F2 b b' Φβ with hF₂def
  have hT₂ : TopCls p.T.base F₂ := hMC Wp Wq P p b b' hb hbc hb' hb'c Φβ hΦβsm K' hK'c hK'U hΦβK

  have hE₀ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)),
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → ∀ h₁ ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
      ∀ h₂ ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
        Φ₀ Z (Matrix.of.symm (h₁ * Matrix.of y * h₂)) = ((p.T.bs P.r).π h₁).comp ((Φ₀ Z y).comp ((p.T.bs P.r).π' h₂)) := by
    intro Z y hy h₁ hh₁ h₂ hh₂
    have hGG : Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂) =
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y) := Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh₁ hh₂ _
    have hy' : h₁ * Matrix.of y * h₂ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) :=
      Formalism.FourierDecayAlt.P.Qx8.glev_mul (Formalism.FourierDecayAlt.P.Qx8.glev_mul (Formalism.FourierDecayAlt.P.Qx8.uw_glev _ hh₁) hy)
        (Formalism.FourierDecayAlt.P.Qx8.uw_glev _ hh₂)
    have hiff : (Z, Matrix.of.symm (h₁ * Matrix.of y * h₂)) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ↔
        (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        change 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂) at h2
        rw [hGG] at h2; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂)
        rw [hGG]; exact h2
    show (if (Z, Matrix.of.symm (h₁ * Matrix.of y * h₂)) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf Z e (Matrix.of.symm (h₁ * Matrix.of y * h₂)) else 0) =
      ((p.T.bs P.r).π h₁).comp ((if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0).comp
        ((p.T.bs P.r).π' h₂))
    by_cases hq : (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [if_pos (hiff.2 hq), if_pos hq]
      have e1 := hΦval Z e (fun _ => 0) (Matrix.of.symm (h₁ * Matrix.of y * h₂)) hy'
      have e2 := hΦval Z e (fun _ => 0) y hy
      have hx : ((fun _ => 0, Matrix.of y) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx P.k (P.r - P.r)) ∈
          Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨omX_zero _, hy, hq.2⟩
      have e3 := (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e).2.2.2 _ hx h₁ hh₁ h₂ hh₂
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ← e1, ← e2]
      exact congrArg (fun X => κ⁻¹ • X) e3
    · rw [if_neg (fun h' => hq (hiff.1 h')), if_neg hq]
      simp
  have hR₀ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)) (v : Matrix (Fin P.r) (Fin P.r) ℂ),
      (Matrix.of Z).det ≠ 0 → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni v →
      Φ₀ (Matrix.of.symm (Matrix.of Z * v)) y = psiU p v • Φ₀ Z y := by
    intro Z y v hZ hy hv
    have hiff : (Matrix.of.symm (Matrix.of Z * v), y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ↔
        (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := by
      have hd : (Matrix.of (Matrix.of.symm (Matrix.of Z * v))).det = (Matrix.of Z).det := by
        simp [Matrix.det_mul, det_upUni hv]
      exact ⟨fun h' => ⟨hd ▸ h'.1, h'.2⟩, fun h' => ⟨hd.symm ▸ h'.1, h'.2⟩⟩
    show (if (Matrix.of.symm (Matrix.of Z * v), y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf (Matrix.of.symm (Matrix.of Z * v)) e y else 0) =
      psiU p v • (if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0)
    by_cases hq : (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [if_pos (hiff.2 hq), if_pos hq, hΦR Z y v hy hv, smul_comm]
    · rw [if_neg (fun h' => hq (hiff.1 h')), if_neg hq, smul_zero]
  have hmkΦ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)), (Matrix.of Z).det ≠ 0 →
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      pbTop p F₂ (Matrix.of Z) (Matrix.of y) = κ • Φ₀ Z y :=
    fun Z y hZ hy => hmk Φ₀ hE₀ hR₀ Z y hZ hy
  have hF₂val : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)),
      (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      pbTop p F₂ (Matrix.of Z) (Matrix.of y) = Φf Z e y := by
    intro Z y hq hy
    rw [hmkΦ Z y hq.1 hy]
    show κ • (if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0) = _
    rw [if_pos hq, smul_smul, mul_inv_cancel₀ hκ, one_smul]

  have hVopen : IsOpen {y : Mt P.k (P.r - P.r) | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} :=
    isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_id)
  have hkey : ∀ (h' : C.LPt) (hh' : D.IsLocPt h' P.r)
      (Ψh : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
        (p.T.bs P.r).π (p.T.bs P.r).π'),
      (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Ψh e')
        (D.castF (by rw [hh'.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' (u e') h'))) →
      ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
        0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
        B.JF (p.T.bs P.r) (D.castF (by rw [hh'.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h')) γ =
          (P5.act (Fr.ofWord L st (D.positionted w)).F Ψh e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ := by
    intro h' hh' Ψh hΨh c γ hγG hγGG
    have hγL : γ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) := ((hTP Wp Wq P p).2 γ).1 hγG

    have hHFe : ∀ e', PBI.ParFam P.k (P.r - P.r)
          (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
          (fun q : PBQ.XH h' × Mt P.k (P.r - P.r) => PBQ.ellH h' q.1 (Ψf (PBQ.zxH h' P.r hh'.2 q.1) e' q.2)) ∧
        ∃ Kp : Set (PBQ.XH h'), IsCompact Kp ∧ ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
          Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Ψf (PBQ.zxH h' P.r hh'.2 v) e' y = 0 :=
      fun e' => hHF Wp Wq P p h' hh' (fun q => Ψf q.1 e' q.2) (hΨsm e') (Ku e') (hKuc e') (hKuU e') (hKu e')
    choose hsm2 Kpe hKpec hKpev using hHFe
    set Kp : Set (PBQ.XH h') := ⋃ e', Kpe e' with hKpdef
    have hKpc : IsCompact Kp := isCompact_iUnion hKpec
    have hKpv : ∀ e', ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
        Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Ψf (PBQ.zxH h' P.r hh'.2 v) e' y = 0 :=
      fun e' v hv y hy => hKpev e' v (fun h'' => hv (Set.mem_iUnion.2 ⟨e', h''⟩)) y hy

    set a : PBQ.XH h' → ℂ := fun v => G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h') v)) with hadef
    have hell : ∀ v (X : Wq →L[ℂ] Wp), PBQ.ellH h' v X = a v • X := fun v X => rfl
    set Ψ' : PBQ.XH h' → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' := fun v e' => a v • Ψ (PBQ.zxH h' P.r hh'.2 v) e' with hΨ'def
    set Ψ'f : PBQ.XH h' → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
      fun v e' y => PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y) with hΨ'fdef
    have hval' : ∀ v e' c' y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ' v e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' (Matrix.of y) = Ψ'f v e' y := by
      intro v e' c' y hy
      show a v • (Ψ (PBQ.zxH h' P.r hh'.2 v) e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c'
        (Matrix.of y) = PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y)
      rw [hell]
      exact congrArg (fun X => a v • X) (hΨ _ e' c' y hy)
    obtain ⟨Φf', hΦval', hΦsm', hΦsupp', hΦswap'⟩ := hFP Wp Wq P p X μ L st hD w hAdm (PBQ.XH h')
      (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
      (isOpen_univ.prod hVopen) le_rfl Ψ' Ψ'f hval' hsm2

    have h5 : ∀ v y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        Φf' v e y = PBQ.ellH h' v (Φf (PBQ.zxH h' P.r hh'.2 v) e y) := by
      intro v y hy
      rw [← hΦval' v e (fun _ => 0) y hy, ← hΦval (PBQ.zxH h' P.r hh'.2 v) e (fun _ => 0) y hy, hell]
      show (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => a v • Ψ (PBQ.zxH h' P.r hh'.2 v) e') e :
        Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) (fun _ => 0) (Matrix.of y) = _
      erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
      rfl

    have h6 : ∀ v y, v ∉ Kp → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y) → Φf' v e y = 0 := by
      intro v y hv hy hG
      refine hΦsupp' (Kp ×ˢ Set.univ) (fun e' q hqG hq => ?_) e (v, y) ⟨trivial, hG⟩ hy ?_
      · have hq1 : q.1 ∉ Kp := fun h'' => hq ⟨h'', trivial⟩
        show PBQ.ellH h' q.1 (Ψf (PBQ.zxH h' P.r hh'.2 q.1) e' q.2) = 0
        rw [hKpv e' q.1 hq1 q.2 hqG, map_zero]
      · rw [(hKpc.isClosed.prod isClosed_univ).closure_eq]
        exact fun h'' => hv h''.1

    haveI : IsFiniteMeasure ((volume : Measure (PBQ.XH h')).restrict Kp) :=
      isFiniteMeasure_restrict.mpr hKpc.measure_lt_top.ne
    have hνc : ((volume : Measure (PBQ.XH h')).restrict Kp) Kpᶜ = 0 := by
      rw [Measure.restrict_apply hKpc.isClosed.measurableSet.compl]; simp

    have hsw := hΦswap' ((volume : Measure (PBQ.XH h')).restrict Kp) Kp hKpc hνc Ψh (Matrix.of.symm γ)
      {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} hVopen hγGG hγL
      (fun q hq => ⟨trivial, hq.2⟩) (fun e' c' y' hy' hy'G => ?_) e c
    · obtain ⟨-, hJ⟩ := hST Wp Wq P p F₂ hT₂ h' hh' γ hγG hγGG
      rw [hJ]
      have hpt : ∀ v, PBQ.ellH h' v (pbTop p F₂ (PBQ.zxH h' P.r hh'.2 v) γ) = Φf' v e (Matrix.of.symm γ) := by
        intro v
        rw [h5 v (Matrix.of.symm γ) hγL]
        congr 1
        exact hF₂val (PBQ.zxH h' P.r hh'.2 v) (Matrix.of.symm γ) ⟨hZx P.r h' hh' v, hγGG⟩ hγL
      rw [integral_congr_ae (Eventually.of_forall hpt),
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Kp) (fun v hv => h6 v (Matrix.of.symm γ) hv hγL hγGG)]
      exact hsw.symm
    · have hx : ((c', Matrix.of y') : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx P.k (P.r - P.r)) ∈
          Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨omX_zero c', hy'G, hy'⟩
      have hGV : Matrix.of y' ∈ B.GV P.k (P.r - P.r) := ((hTP Wp Wq P p).2 (Matrix.of y')).2 hy'G
      obtain ⟨-, hJu⟩ := hST Wp Wq P p (u e') (hTu e') h' hh' (Matrix.of y') hGV hy'
      refine (hΨh e' _ hx).trans ?_
      refine (hRT _ (JC.parLev P P.r).k (JC.parLev P P.r).r hr0 _ _ _).trans ?_
      refine hJu.trans ?_
      have hcong : ∀ v, PBQ.ellH h' v (pbTop p (u e') (PBQ.zxH h' P.r hh'.2 v) (Matrix.of y')) = Ψ'f v e' y' :=
        fun v => (congrArg (PBQ.ellH h' v) (hΨf_pos (PBQ.zxH h' P.r hh'.2 v) e' y' ⟨hZx P.r h' hh' v, hy'⟩)).symm
      rw [integral_congr_ae (Eventually.of_forall hcong)]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Kp) (fun v hv => by
        show PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y') = 0
        rw [hKpv e' v hv y' hy'G, map_zero])]

  obtain ⟨Φ₂, hΦ₂⟩ := Formalism.FourierDecayAlt.P.PBN.radExists p hT₂.1
  refine ⟨F₁, F₂, hF₁, hT₂.1, fun ζ => hloc w hcut e Cb hdd ζ, ?_, ?_⟩
  ·
    intro Φ₁ hΦ₁ x hx
    rw [← hΦ₂ x hx]
    obtain ⟨g, hgL, hgGG, hxg⟩ := (hTP Wp Wq P p).1 x hx
    have hc : x.1 ∈ OmX P.r := hx.1
    have hgGV : g ∈ B.GV P.k (P.r - P.r) := ((hTP Wp Wq P p).2 g).2 hgL
    have hhc : D.IsLocPt (PBI.hcell x.1) P.r := by
      refine ⟨fun bl hbl => ?_, PBI.ptSize_hcell x.1⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hbl
      exact ⟨le_rfl, hc j⟩
    have hRSTc : ∀ e', ∃ Ψc : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
        (p.T.bs P.r).π (p.T.bs P.r).π', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) Ψc
          (D.castF (by rw [hhc.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' (u e') (PBI.hcell x.1))) :=
      fun e' => hRST Wp Wq P p (u e') (hTu e') (PBI.hcell x.1) hhc
    choose Ψc hΨc using hRSTc
    set W : ℂ := ((∏ j : Fin P.r, ‖x.1 j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) with hW

    have hR : (Φ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        W • (P5.act (Fr.ofWord L st (D.positionted w)).F Ψc e :
          Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) (fun _ => 0) g := by
      rw [hxg, hPicS Wp Wq P p F₂ hT₂.1 Φ₂ hΦ₂ x.1 hc g hgL hgGG]
      exact congrArg (fun X => W • X) (hkey (PBI.hcell x.1) hhc Ψc hΨc (fun _ => 0) g hgGV hgGG)
    rw [hR]

    obtain ⟨T, hT, hFT⟩ := Formalism.FourierDecayAlt.P.frame_transport_to_last_level Wp Wq P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD x.1 hc
    have hTb : ∀ e', T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e') = W • Ψc e' := by
      intro e'
      refine hRE Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' _ _ fun y hy => ?_
      show (T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e') :
          Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        W • (Ψc e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) y.1 y.2
      refine (hT _ y.1 y.2).trans ?_
      refine (hRW Wp Wq P p X₀ μ₀ L₀ st₀ hD₀ F₁ hF₁ w hcut Φ₁ hΦ₁ e' x.1 hc y.2 hy.2.1 hy.2.2).trans ?_
      refine congrArg (fun X => W • X) ?_
      refine Eq.symm ((hΨc e' y hy).trans ?_)
      exact hRT _ (JC.parLev P P.r).k (JC.parLev P P.r).r hr0 _ _ _
    rw [hxg]
    have hmul := Formalism.FourierDecayAlt.P.Topx1.act_mul ((Fr.ofWord L₀ st₀ (D.positionted w)).F) (P5.bTall L₀ (D.positionted w))
      (Top.firstStateVector Φ₁)
    rw [hmul, hFT w hAdm₀ hAdm _ e (fun _ => 0) g hgL hgGG]
    have : (fun e' => T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e')) = fun e' => W • Ψc e' :=
      funext hTb
    rw [this]
    erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
    rfl
  ·
    intro Φ hΦ c γ hγG hγGG
    refine hkey h hh Φ (fun e' => ?_) c γ hγG hγGG
    have h1 := hΦ e'
    rw [hsl w e'] at h1
    exact h1

end Formalism.FourierDecayAlt.P.CutEX
