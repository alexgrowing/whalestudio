import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHypPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThK.GlobLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def rapid : Submodule ℂ (UA σ J → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ ratU σ J, ∀ x, f (γ * x) = f x) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => ⟨0, fun h => by simp⟩⟩
  add_mem' := by
    rintro f g ⟨f1, f2, f3⟩ ⟨g1, g2, g3⟩
    refine ⟨f1.add g1, fun γ hγ x => by simp only [Pi.add_apply, f2 γ hγ x, g2 γ hγ x], fun N => ?_⟩
    obtain ⟨C, hC⟩ := f3 N
    obtain ⟨D, hD⟩ := g3 N
    refine ⟨C + D, fun h => ?_⟩
    calc ‖(f + g) h‖ * (qht h : ℝ) ^ N ≤ (‖f h‖ + ‖g h‖) * (qht h : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ ≤ C + D := by rw [add_mul]; exact add_le_add (hC h) (hD h)
  smul_mem' := by
    rintro c f ⟨f1, f2, f3⟩
    refine ⟨continuous_const.mul f1, fun γ hγ x => by simp only [Pi.smul_apply, f2 γ hγ x], fun N => ?_⟩
    obtain ⟨C, hC⟩ := f3 N
    refine ⟨‖c‖ * C, fun h => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC h) (norm_nonneg _)

theorem qht_le_transl (h y : UA σ J) : qht h ≤ qht (h * y) * ht y⁻¹ := by
  unfold qht
  rw [NNReal.iInf_mul]
  refine le_ciInf fun γ => (ciInf_le (OrderBot.bddBelow _) γ).trans ?_
  have e : γ.1 * h = γ.1 * (h * y) * y⁻¹ := by group
  rw [e]
  exact heightGL_mul_le F (γ.1 * (h * y)).1 (y⁻¹).1

theorem transl_mem_rapid (y : UA σ J) {f : UA σ J → ℂ} (hf : f ∈ rapid σ J) : (fun h => f (h * y)) ∈ rapid σ J := by
  obtain ⟨f1, f2, f3⟩ := hf
  haveI := (GlobalTheory.UnipCT.topFacts σ J).1
  refine ⟨f1.comp (continuous_id.mul continuous_const), fun γ hγ x => by simp only [mul_assoc, f2 γ hγ], fun N => ?_⟩
  obtain ⟨C, hC⟩ := f3 N
  refine ⟨C * (ht y⁻¹ : ℝ) ^ N, fun h => ?_⟩
  have h1 : (qht h : ℝ) ≤ qht (h * y) * ht y⁻¹ := by exact_mod_cast qht_le_transl h y
  calc ‖f (h * y)‖ * (qht h : ℝ) ^ N ≤ ‖f (h * y)‖ * ((qht (h * y) : ℝ) * ht y⁻¹) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 N) (norm_nonneg _)
    _ = ‖f (h * y)‖ * (qht (h * y) : ℝ) ^ N * (ht y⁻¹ : ℝ) ^ N := by ring
    _ ≤ C * (ht y⁻¹ : ℝ) ^ N := mul_le_mul_of_nonneg_right (hC _) (by positivity)

theorem integrableOn_mul_conj {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hfin : μ D < ⊤) {f k : UA σ J → ℂ}
    (hf : f ∈ rapid σ J) (hk : Continuous k ∧ (∀ γ ∈ ratU σ J, ∀ h, k (γ * h) = k h) ∧
      ∃ (C : ℝ) (m : ℕ), ∀ h, ‖k h‖ ≤ C * (ht h : ℝ) ^ m) :
    Integrable (fun h => f h * (starRingEnd ℂ) (k h)) (μ.restrict D) := by
  obtain ⟨f1, -, f3⟩ := hf
  obtain ⟨k1, k2, C, m, hC⟩ := hk
  obtain ⟨Cf, hCf⟩ := f3 m
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  refine (integrable_const (max C 0 * Cf)).mono' (f1.mul (Complex.continuous_conj.comp k1)).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖k h‖ ≤ ‖f h‖ * (max C 0 * (qht h : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht k2 hC h) (norm_nonneg _)
    _ = max C 0 * (‖f h‖ * (qht h : ℝ) ^ m) := by ring
    _ ≤ max C 0 * Cf := mul_le_mul_of_nonneg_left (hCf h) (le_max_right _ _)

theorem setIntegral_transl {μ : Measure (UA σ J)} [μ.IsHaarMeasure] {D : Set (UA σ J)}
    (hD : IsFundamentalDomain (ratU σ J) D μ) (hfin : μ D < ⊤) {φ : UA σ J → ℂ}
    (hφ : ∀ γ ∈ ratU σ J, ∀ h, φ (γ * h) = φ h) (y : UA σ J) : ∫ h in D, φ (h * y) ∂μ = ∫ h in D, φ h ∂μ := by
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.UnipCT.topFacts σ J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ μ hD (hD.measure_ne_zero (NeZero.ne μ)) hfin.ne
  have hp : MeasurePreserving (MeasurableEquiv.mulRight y⁻¹) μ μ := measurePreserving_mul_right μ y⁻¹
  have h2 : IsFundamentalDomain (ratU σ J) ((MeasurableEquiv.mulRight y⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc, MeasurableEquiv.coe_mulRight]
  have h3 := hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight y⁻¹).measurableEmbedding (fun h => φ (h * y)) D
  rw [← h3]
  simp only [MeasurableEquiv.coe_mulRight, inv_mul_cancel_right]
  exact h2.setIntegral_eq hD fun γ x => hφ γ.1 γ.2 x

theorem exists_pairing {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hfin : μ D < ⊤) {A : Type} [AddCommGroup A] [Module ℂ A]
    (K : A →ₗ[ℂ] (UA σ J → ℂ)) (hK : ∀ Φ, Continuous (K Φ) ∧ (∀ γ ∈ ratU σ J, ∀ h, K Φ (γ * h) = K Φ h) ∧
      ∃ (C : ℝ) (m : ℕ), ∀ h, ‖K Φ h‖ ≤ C * (ht h : ℝ) ^ m) :
    ∃ L : rapid σ J →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ, ∀ f Φ, L f Φ = ∫ h in D, f.1 h * (starRingEnd ℂ) (K Φ h) ∂μ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f Φ => ∫ h in D, f.1 h * (starRingEnd ℂ) (K Φ h) ∂μ) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro f g Φ
    rw [← integral_add (integrableOn_mul_conj hfin f.2 (hK Φ)) (integrableOn_mul_conj hfin g.2 (hK Φ))]
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  · intro c f Φ
    rw [RingHom.id_apply, ← integral_smul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f Φ Ψ
    rw [← integral_add (integrableOn_mul_conj hfin f.2 (hK Φ)) (integrableOn_mul_conj hfin f.2 (hK Ψ))]
    simp only [map_add, Pi.add_apply, mul_add]
  · intro c f Φ
    rw [← integral_smul]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]

theorem exists_ne_zero_of_span {M : Type} [AddCommGroup M] [Module ℂ M] {τ : ℂ →+* ℂ} (N : Submodule ℂ M)
    (l : N →ₛₗ[τ] ℂ) {s : Set M} (hs : ∀ y ∈ s, y ∈ N) {x : M} (hx : x ∈ Submodule.span ℂ s) (hxN : x ∈ N)
    (h0 : l ⟨x, hxN⟩ ≠ 0) : ∃ y, ∃ hy : y ∈ s, l ⟨y, hs y hy⟩ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ z ∈ Submodule.span ℂ s, ∃ hz : z ∈ N, l ⟨z, hz⟩ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact ⟨hs z hz, hcon z hz⟩
    | zero => exact ⟨N.zero_mem, map_zero l⟩
    | add z w _ _ hz hw =>
      obtain ⟨z1, z2⟩ := hz
      obtain ⟨w1, w2⟩ := hw
      refine ⟨N.add_mem z1 w1, ?_⟩
      have := map_add l ⟨z, z1⟩ ⟨w, w1⟩
      rw [z2, w2, add_zero] at this
      exact this
    | smul c z _ hz =>
      obtain ⟨z1, z2⟩ := hz
      refine ⟨N.smul_mem c z1, ?_⟩
      have := map_smulₛₗ l c ⟨z, z1⟩
      rw [z2, smul_zero] at this
      exact this
  exact h0 (key x hx).2

theorem exists_local_form : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ c : ℂ, ∀ f ∈ GlobalTheory.ThK.DescB.Diffs B G X om om' R Rf c, (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
    ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
      V₁.J = H.ιᵀ * G.V.J * H.ι.map σ → M₁.IsGood B.ψ →
      IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
    ∀ (g : UA σ G.V.J), ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (e (om (g, h) Ψ))) ∂μ ≠ 0 →
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ)
      (Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ⋆[ℂ] ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Bf ≠ 0 ∧
      (∀ (g : GL (Fin a) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) ∧
      (∀ (h : GL (Fin (a + a')) (Fv F B.v₁)) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) ∧
      (∀ (z : Fin (a + a') → Fv F B.v₁) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁))),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c f hf hdec d₂ H hH V₁ M₁ e hV₁ hM₁ hev μ 𝓕 hμ h𝓕 g Ψ hΨ hne
  have hT := hM.triple
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) := hS.pres
  obtain ⟨ν₀, β₀, ι, ℓ, ψv, m1, m2, m3, m4, m5, m6, m7, m8, hbij, hA, hB, hC⟩ :=
    GlobalTheory.T.theta_lift_hyp_plane_split hKP F E σ B a a' G X om om' hT d₂ H hH
  have hker := GlobalTheory.T.pair_hyp_plane_split hKP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP d₂ H hH V₁ M₁ e hV₁ hM₁ hev

  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hd := GlobalTheory.ThK.DescB.Nondeg.det_ne_zero_of_cartan B G.W hT.geo.hW.cartan
  obtain ⟨c₀, hc₀, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hT.geo.hW.skew hd hc₀ hcs
  haveI := hμ
  have hfin := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hKP.siegelSetUnitary hcm hc₀ hJ h𝓕

  let K : schA F (Fin a × Fin (a + a')) →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Φ h => thetaSum F (e (om (1, h) Φ.1))
      map_add' := fun Φ Φ' => funext fun h => by
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
        exact thetaSum_add F (hev.maps _ (hpres _ _ Φ.2)) (hev.maps _ (hpres _ _ Φ'.2))
      map_smul' := fun t Φ => funext fun h => by
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        exact thetaSum_smul F t _ }
  have hK : ∀ Φ h, K Φ h = thetaSum F (e (om (1, h) Φ.1)) := fun _ _ => rfl
  obtain ⟨L, hL⟩ := exists_pairing hfin K fun Φ => hker Φ.1 Φ.2
  have hfN : f ∈ rapid σ G.W.J :=
    ⟨(GlobalTheory.ThK.DescB.Nondeg.diffs_reg hKP hM c f hf).1, (GlobalTheory.ThK.DescB.Nondeg.diffs_reg hKP hM c f hf).2, hdec⟩
  have hΨ₀ : om (g, 1) Ψ ∈ schA F (Fin a × Fin (a + a')) := hpres _ _ hΨ
  have hL0 : L.flip ⟨_, hΨ₀⟩ ⟨f, hfN⟩ ≠ 0 := by
    rw [LinearMap.flip_apply, hL]
    refine fun h0 => hne (Eq.trans ?_ h0)
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [hK]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  obtain ⟨_, ⟨T, hTN, hTa, hTe, φ₀, hφ₀, rfl⟩, hL1⟩ := exists_ne_zero_of_span (rapid σ G.W.J) (L.flip ⟨_, hΨ₀⟩)
    (by rintro _ ⟨T, hTN, -, -, φ, hφ, rfl⟩; exact hTN φ hφ)
    (GlobalTheory.T.matched_diffs_invariant_subspace hKP F E σ B a a' G X om om' R Rf hM c (rapid σ G.W.J) (fun y _ _ h => transl_mem_rapid y h) f hf hfN)
    hfN hL0
  rw [LinearMap.flip_apply] at hL1
  obtain ⟨_, ⟨φ₂, r, hφ₂, hr, rfl⟩, hL2⟩ := exists_ne_zero_of_span (schA F (Fin a × Fin (a + a'))) (L ⟨T φ₀, hTN φ₀ hφ₀⟩)
    (by rintro _ ⟨φ, r, hφ, hr, rfl⟩; exact (hr φ hφ).2)
    (GlobalTheory.PureAtPlace.schA_le_span_tens F B.v₁ (Fin a × Fin (a + a')) hΨ₀) hΨ₀ hL1

  let ιr : SB (Fin a × Fin (a + a') → Fv F B.v₁) →ₗ[ℂ] SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) :=
    ι.restrict fun φ hφ => hbij.mapsTo hφ
  have hιr : Function.Bijective ιr := by
    refine ⟨fun φ φ' h => Subtype.ext (hbij.injOn φ.2 φ'.2 (congrArg Subtype.val h)), fun Y => ?_⟩
    obtain ⟨φ, hφ, h⟩ := hbij.surjOn Y.2
    exact ⟨⟨φ, hφ⟩, Subtype.ext h⟩
  obtain ⟨j, hj1, hj2⟩ : ∃ j : SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ] SB (Fin a × Fin (a + a') → Fv F B.v₁),
      (∀ Y, ι (j Y).1 = Y.1) ∧ ∀ Y, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Y.1 = ι φ → (j Y).1 = φ := by
    have h1 : ∀ Y, ι ((LinearEquiv.ofBijective ιr hιr).symm Y).1 = Y.1 := fun Y =>
      congrArg Subtype.val ((LinearEquiv.ofBijective ιr hιr).apply_symm_apply Y)
    exact ⟨(LinearEquiv.ofBijective ιr hιr).symm.toLinearMap, h1, fun Y φ hφ h =>
      hbij.injOn ((LinearEquiv.ofBijective ιr hιr).symm Y).2 hφ ((h1 Y).trans h)⟩
  let T' : SB (Fin a × Fin (a + a') → Fv F B.v₁) →ₗ[ℂ] rapid σ G.W.J := T.restrict hTN
  let Rr : SB (Fin a × Fin (a + a') → Fv F B.v₁) →ₗ[ℂ] schA F (Fin a × Fin (a + a')) :=
    { toFun := fun φ => ⟨tens (evFin F B.v₁) φ.1 r, (hr φ.1 φ.2).2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [tens, Submodule.coe_add, Pi.add_apply, add_mul])
      map_smul' := fun t φ => Subtype.ext (funext fun x => by
        simp only [tens, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]) }
  obtain ⟨Bf, hBf⟩ : ∃ Bf : SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ[ℂ]
      SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) →ₗ⋆[ℂ] ℂ, ∀ Y₁ Y₂, Bf Y₁ Y₂ = L (T' (j Y₁)) (Rr (j Y₂)) :=
    ⟨((L.comp (T'.comp j)).flip.comp (Rr.comp j)).flip, fun _ _ => rfl⟩
  have hBi : ∀ Y₁ Y₂, Bf Y₁ Y₂ = ∫ h in 𝓕, T (j Y₁).1 h *
      (starRingEnd ℂ) (thetaSum F (e (om (1, h) (tens (evFin F B.v₁) (j Y₂).1 r)))) ∂μ := fun Y₁ Y₂ => by
    rw [hBf, hL]
    rfl
  refine ⟨ν₀, β₀, ℓ, ψv, Bf, m1, m2, m3, m4, m5, m6, m7, m8, fun h0 => hL2 ?_, ?_, ?_, ?_⟩
  · have h1 := hBi ⟨ι φ₀, hbij.mapsTo hφ₀⟩ ⟨ι φ₂, hbij.mapsTo hφ₂⟩
    rw [hj2 _ φ₀ hφ₀ rfl, hj2 _ φ₂ hφ₂ rfl, h0] at h1
    rw [hL]
    exact h1.symm
  · intro g' Y₁ Y₁' Y₂ hY
    obtain ⟨g₁, hg₁, hg⟩ := hA g'
    obtain ⟨φ₁, hφ₁, hact, hι⟩ := hg _ (j Y₁).2
    rw [hj1, ← hY] at hι
    have h1 : T (φ₁ - (j Y₁).1) = 0 := hTa (Submodule.subset_span ⟨g₁, hg₁, _, (j Y₁).2, φ₁, hφ₁, hact, rfl⟩)
    rw [map_sub, sub_eq_zero] at h1
    rw [hBi, hBi, hj2 _ φ₁ hφ₁ hι.symm, h1]
  · intro h' Y₁ Y₁' Y₂ Y₂' hY₁ hY₂
    obtain ⟨y, hy, hyy⟩ := hB h'
    obtain ⟨φ₁, hφ₁, hact₁, hι₁⟩ := hyy _ (j Y₁).2
    obtain ⟨φ₃, hφ₃, hact₃, hι₃⟩ := hyy _ (j Y₂).2
    rw [hj1, ← hY₁] at hι₁
    rw [hj1, ← hY₂] at hι₃
    rw [hBi, hBi, hj2 _ φ₁ hφ₁ hι₁.symm, hj2 _ φ₃ hφ₃ hι₃.symm, ← hact₃ r (hr _ (j Y₂).2),
      ← setIntegral_transl h𝓕 hfin (φ := fun h => T (j Y₁).1 h *
        (starRingEnd ℂ) (thetaSum F (e (om (1, h) (tens (evFin F B.v₁) (j Y₂).1 r))))) (fun γ hγ h => by
          beta_reduce
          rw [(hTN _ (j Y₁).2).2.1 γ hγ h, (hker _ (hr _ (j Y₂).2).2).2.1 γ hγ h]) y]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    beta_reduce
    rw [hTe y hy _ (j Y₁).2 φ₁ hφ₁ hact₁ h, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  · intro z Y₁ Y₂ Y₂' hY
    obtain ⟨u, ⟨w, rfl⟩, -, hu⟩ := hC z
    obtain ⟨φ₃, hφ₃, hact₃, hι₃⟩ := hu _ (j Y₂).2
    rw [hj1, ← hY] at hι₃
    rw [hBi, hBi, hj2 _ φ₃ hφ₃ hι₃.symm, ← hact₃ r (hr _ (j Y₂).2)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    beta_reduce
    have hΦ := (hr _ (j Y₂).2).2
    rw [hS.impl (1, h) _ _ hΦ, hev.inv _ _ _ (hpres _ _ hΦ)]
    refine ⟨mat h *ᵥ w, ?_⟩
    change (1 : Matrix _ _ _) * _ * (mat h)ᵀ = _
    rw [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

end GlobalTheory.ThK.GlobLoc
