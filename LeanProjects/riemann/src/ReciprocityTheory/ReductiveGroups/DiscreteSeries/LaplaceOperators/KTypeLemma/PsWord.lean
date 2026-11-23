import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP

noncomputable section

open Finset MeasureTheory Matrix Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PsW

variable {n : ℕ}

local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)

def mmul (A B : 𝕄) : 𝕄 := Matrix.of A * Matrix.of B

lemma contDiff_mmul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f g : X → 𝕄}
    (hf : ContDiff ℂ ω f) (hg : ContDiff ℂ ω g) : ContDiff ℂ ω fun x => mmul (f x) (g x) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [mmul, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun c _ =>
    (contDiff_pi.1 (contDiff_pi.1 hf a) c).mul (contDiff_pi.1 (contDiff_pi.1 hg c) b)

lemma continuous_mmul {X : Type*} [TopologicalSpace X] {f g : X → 𝕄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => mmul (f x) (g x) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [mmul, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finset_sum _ fun c _ =>
    ((continuous_apply c).comp ((continuous_apply a).comp hf)).mul
      ((continuous_apply b).comp ((continuous_apply c).comp hg))

lemma diffAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {s : Set E} {x : E} (h : ContDiffOn ℂ ω f s) (hs : IsOpen s)
    (hx : x ∈ s) : DifferentiableAt ℂ f x := by
  exact (h.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)

lemma contDiffAt_zpow {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : X → ℂ} {x : X}
    (hf : ContDiffAt ℂ ω f x) (hx : f x ≠ 0) (m : ℤ) : ContDiffAt ℂ ω (fun y => f y ^ m) x := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · simp only [zpow_natCast]
    exact hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv (pow_ne_zero _ hx)

private theorem contDiff_det_k_type {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Fin m → Fin m → ℂ => Matrix.det z) := by
  have h : (fun z : Fin m → Fin m → ℂ => Matrix.det z) =
      fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i := by
    funext z
    exact Matrix.det_apply' _
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)

lemma contDiff_lead (i : ℕ) : ContDiff ℂ ω (fun z : 𝕄 => lead i z) := by
  by_cases h : i ≤ n
  · have e : (fun z : 𝕄 => lead i z) = fun z : 𝕄 =>
        Matrix.det (fun a b => z (Fin.castLE h a) (Fin.castLE h b) : Fin i → Fin i → ℂ) := by
      funext z
      simp only [lead, dif_pos h]
      rfl
    rw [e]
    exact contDiff_det_k_type.comp (contDiff_pi.2 fun a => contDiff_pi.2 fun b =>
      contDiff_pi.1 (contDiff_pi.1 contDiff_id (Fin.castLE h a)) (Fin.castLE h b))
  · have e : (fun z : 𝕄 => lead i z) = fun _ => 0 := by
      funext z
      simp only [lead, dif_neg h]
    rw [e]
    exact contDiff_const

def PhiQ (μ : Fin n → ℤ) : 𝕄 → ℂ := fun y => PhiM μ y

lemma contDiffOn_phiQ (μ : Fin n → ℤ) : ContDiffOn ℂ ω (PhiQ μ) (OmegaSet n : Set 𝕄) := by
  show ContDiffOn ℂ ω (fun y : 𝕄 => ∏ i : Fin n, lead ((i : ℕ) + 1) y ^ (-(μ i - muNext μ i)))
    (OmegaSet n : Set 𝕄)
  refine contDiffOn_prod fun i _ => ?_
  have hne : ∀ y ∈ (OmegaSet n : Set 𝕄), lead ((i : ℕ) + 1) y ≠ 0 := fun y hy =>
    (show ∀ j : Fin n, lead ((j : ℕ) + 1) y ≠ 0 from hy) i
  have hg : ContDiffOn ℂ ω (fun y : 𝕄 => lead ((i : ℕ) + 1) y) (OmegaSet n : Set 𝕄) :=
    (contDiff_lead _).contDiffOn
  rcases Int.eq_nat_or_neg (-(μ i - muNext μ i)) with ⟨k, hk | hk⟩
  · simp only [hk, zpow_natCast]
    exact hg.pow k
  · simp only [hk, _root_.zpow_neg, zpow_natCast]
    exact (hg.pow k).inv fun y hy => pow_ne_zero _ (hne y hy)

def Om : Set WW := {q | q.2 ∈ OmegaSet n}

lemma isOpen_Om : IsOpen (Om : Set WW) := by
  have ho : IsOpen (OmegaSet n : Set 𝕄) := by
    show IsOpen {z : 𝕄 | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun (contDiff_lead (n := n) _).continuous continuous_const
  exact ho.preimage continuous_snd

def Fw (μ : Fin n → ℤ) (D : List MM) (q : WW) : ℂ :=
  lWord (D.map fun Z => mmul (mmul q.1.1 Z) q.1.2) (PhiM μ) q.2

lemma hasFDerivAt_slice {f : WW → ℂ} {q : WW} (hf : DifferentiableAt ℂ f q) :
    HasFDerivAt (fun y : 𝕄 => f (q.1, y))
      ((fderiv ℂ f q).comp (ContinuousLinearMap.inr ℂ (𝕄 × 𝕄) 𝕄)) q.2 := by
  first
  | exact hf.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
  | exact hf.hasFDerivAt.comp q.2 (hasFDerivAt_prod_mk_right q.1 q.2)

lemma contDiffOn_Fw (μ : Fin n → ℤ) : ∀ D : List MM, ContDiffOn ℂ ω (Fw μ D) Om
  | [] => (contDiffOn_phiQ μ).comp contDiff_snd.contDiffOn fun _ hq => hq
  | Z :: D => by
    have hD := contDiffOn_Fw μ D
    have h1 : ContDiffOn ℂ ω (fderiv ℂ (Fw μ D)) Om := hD.fderiv_of_isOpen isOpen_Om le_top
    have h2 : ContDiff ℂ ω fun q : WW => ((0 : 𝕄 × 𝕄), mmul (mmul (mmul q.1.1 Z) q.1.2) q.2) :=
      contDiff_const.prodMk (contDiff_mmul (contDiff_mmul (contDiff_mmul
        (contDiff_fst.comp contDiff_fst) contDiff_const) (contDiff_snd.comp contDiff_fst)) contDiff_snd)
    refine (h1.clm_apply h2.contDiffOn).congr fun q hq => ?_
    show fderiv ℂ (fun y : 𝕄 => Fw μ D (q.1, y)) q.2 (mmul (mmul (mmul q.1.1 Z) q.1.2) q.2) = _
    rw [(hasFDerivAt_slice (diffAt hD isOpen_Om hq)).fderiv]
    rfl

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

def psi (k : KG ε) (z : 𝕄) : WW := ((toMK k⁻¹, toMK k), mmul (mmul (toMK k⁻¹) z) (toMK k))

def dpsi (k : KG ε) : 𝕄 →L[ℂ] WW :=
  (0 : 𝕄 →L[ℂ] 𝕄 × 𝕄).prod (Ps1.conjCLM (toMK k⁻¹) (toMK k))

lemma hasFDerivAt_psi (k : KG ε) (z : 𝕄) : HasFDerivAt (psi k) (dpsi k) z := by
  first
  | exact (hasFDerivAt_const (toMK k⁻¹, toMK k) z).prodMk
      (Ps1.conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
  | exact (hasFDerivAt_const (toMK k⁻¹, toMK k) z).prod
      (Ps1.conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt

lemma continuous_psi : Continuous fun p : 𝕄 × KG ε => psi p.2 p.1 := by
  have h1 : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | continuity
    | (unfold toMK; continuity)
  have h2 : Continuous fun k : KG ε => toMK k⁻¹ := h1.comp continuous_inv
  have hm : Continuous fun p : 𝕄 × KG ε => mmul (mmul (toMK p.2⁻¹) p.1) (toMK p.2) :=
    continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_fst) (h1.comp continuous_snd)
  first
  | exact ((h2.comp continuous_snd).prodMk (h1.comp continuous_snd)).prodMk hm
  | exact ((h2.comp continuous_snd).prod_mk (h1.comp continuous_snd)).prod_mk hm

def cc (T : KType ε Λ) : ℂ := (Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)

def G (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) (z : 𝕄) (k : KG ε) : T.V →L[ℂ] T.V :=
  Fw μ D (psi k z) • (T.op k * projW T * T.op k⁻¹)

def G' (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) (z : 𝕄) (k : KG ε) :
    𝕄 →L[ℂ] (T.V →L[ℂ] T.V) :=
  ((fderiv ℂ (Fw μ D) (psi k z)).comp (dpsi k)).smulRight (T.op k * projW T * T.op k⁻¹)

lemma hasFDerivAt_G (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) (k : KG ε) {x : 𝕄}
    (hx : psi k x ∈ (Om : Set WW)) : HasFDerivAt (fun y => G T μ D y k) (G' T μ D x k) x := by
  exact ((diffAt (contDiffOn_Fw μ D) isOpen_Om hx).hasFDerivAt.comp x
    (hasFDerivAt_psi k x)).smul_const _

lemma continuousOn_G (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) :
    ContinuousOn (fun p : 𝕄 × KG ε => G T μ D p.1 p.2) (Ps1.Uset ε ×ˢ Set.univ) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  exact ((contDiffOn_Fw μ D).continuousOn.comp continuous_psi.continuousOn
    (fun ⦃p⦄ hp => hp.1 p.2)).smul (hC.comp continuous_snd).continuousOn

lemma continuousOn_G' (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) :
    ContinuousOn (fun p : 𝕄 × KG ε => G' T μ D p.1 p.2) (Ps1.Uset ε ×ˢ Set.univ) := by
  have h1 : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | continuity
    | (unfold toMK; continuity)
  have h2 : Continuous fun k : KG ε => toMK k⁻¹ := h1.comp continuous_inv
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  have hFd : ContinuousOn (fun p : 𝕄 × KG ε => fderiv ℂ (Fw μ D) (psi p.2 p.1))
      (Ps1.Uset ε ×ˢ Set.univ) :=
    ((contDiffOn_Fw μ D).continuousOn_fderiv_of_isOpen isOpen_Om le_top).comp
      continuous_psi.continuousOn (fun ⦃p⦄ hp => hp.1 p.2)
  refine continuousOn_clm_apply.2 fun y => ?_
  have hdy : Continuous fun p : 𝕄 × KG ε => dpsi p.2 y := by
    first
    | exact continuous_const.prodMk
        (continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_const) (h1.comp continuous_snd))
    | exact continuous_const.prod_mk
        (continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_const) (h1.comp continuous_snd))
  exact (hFd.clm_apply hdy.continuousOn).smul (hC.comp continuous_snd).continuousOn

lemma continuous_Fwk (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous fun k : KG ε => Fw μ D (psi k z) := by
  have hc : Continuous fun k : KG ε => psi k z := by
    first
    | exact continuous_psi.comp (Continuous.prodMk continuous_const continuous_id)
    | exact continuous_psi.comp (Continuous.prod_mk continuous_const continuous_id)
  exact (contDiffOn_Fw μ D).continuousOn.comp_continuous hc (fun k => hz k)

lemma continuous_Gk (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous (G T μ D z) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  exact (continuous_Fwk μ D hz).smul hC

lemma continuous_G'k (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous (G' T μ D z) := by
  have h1 : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | continuity
    | (unfold toMK; continuity)
  have h2 : Continuous fun k : KG ε => toMK k⁻¹ := h1.comp continuous_inv
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  have hps : Continuous fun k : KG ε => psi k z := by
    first
    | exact continuous_psi.comp (Continuous.prodMk continuous_const continuous_id)
    | exact continuous_psi.comp (Continuous.prod_mk continuous_const continuous_id)
  have hFd : Continuous fun k : KG ε => fderiv ℂ (Fw μ D) (psi k z) :=
    ((contDiffOn_Fw μ D).continuousOn_fderiv_of_isOpen isOpen_Om le_top).comp_continuous hps
      (fun k => hz k)
  refine continuous_clm_apply.2 fun y => ?_
  have hdy : Continuous fun k : KG ε => dpsi k y := by
    first
    | exact continuous_const.prodMk (continuous_mmul (continuous_mmul h2 continuous_const) h1)
    | exact continuous_const.prod_mk (continuous_mmul (continuous_mmul h2 continuous_const) h1)
  exact (hFd.clm_apply hdy).smul hC

lemma integrable_G [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄}
    (hz : z ∈ Ps1.Uset ε) : Integrable (G T μ D z) (muK ε) := by
  first
  | exact (continuous_Gk T μ D hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | exact integrableOn_univ.1 ((continuous_Gk T μ D hz).continuousOn.integrableOn_compact isCompact_univ)

lemma integrable_G' [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄}
    (hz : z ∈ Ps1.Uset ε) : Integrable (G' T μ D z) (muK ε) := by
  first
  | exact (continuous_G'k T μ D hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | exact integrableOn_univ.1 ((continuous_G'k T μ D hz).continuousOn.integrableOn_compact isCompact_univ)

lemma hasFDerivAt_intG [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM)
    {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, G T μ D x k ∂(muK ε)) (∫ k, G' T μ D z k ∂(muK ε)) z := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 Ps1.isOpen_Uset z hz
  have hr0 : 0 < ε₀ / 2 := half_pos hε₀
  have hcb : Metric.closedBall z (ε₀ / 2) ⊆ Ps1.Uset ε :=
    (Metric.closedBall_subset_ball (half_lt_self hε₀)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z (ε₀ / 2)).prod isCompact_univ).exists_bound_of_continuousOn
    ((continuousOn_G' T μ D).mono (Set.prod_mono hcb le_rfl))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds z hr0) ?_
    (integrable_G T μ D hz) (continuous_G'k T μ D hz).aestronglyMeasurable ?_ (integrable_const C) ?_
  · exact Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx =>
      (continuous_Gk T μ D hx).aestronglyMeasurable
  · exact ae_of_all _ fun k x hx => hC (x, k) ⟨Metric.ball_subset_closedBall hx, Set.mem_univ _⟩
  · exact ae_of_all _ fun k x hx => hasFDerivAt_G T μ D k (hcb (Metric.ball_subset_closedBall hx) k)

lemma toMK_mul_inv (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by
  first
  | (simp only [toMK]; rw [← map_mul, mul_inv_cancel, map_one])
  | (unfold toMK; rw [← map_mul, mul_inv_cancel, map_one])
  | simp [toMK, toM]
  | (unfold toMK toM; simp)
  | (simp only [toMK, toM]; simp [Matrix.mul_eq_one_comm])

lemma G'_apply (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : MM} (hz : z ∈ Ps1.Uset ε)
    (k : KG ε) (Z : MM) : G' T μ D z k (Z * z) = G T μ (Z :: D) z k := by
  have hq : psi k z ∈ (Om : Set WW) := hz k
  have hs := hasFDerivAt_slice (diffAt (contDiffOn_Fw μ D) isOpen_Om hq)
  have hrep : Fw μ (Z :: D) (psi k z) = fderiv ℂ (Fw μ D) (psi k z)
      (ContinuousLinearMap.inr ℂ (𝕄 × 𝕄) 𝕄
        (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2)) := by
    show fderiv ℂ (fun y : 𝕄 => Fw μ D ((psi k z).1, y)) (psi k z).2
      (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2) = _
    rw [hs.fderiv]
    rfl
  have hv : dpsi k (Z * z) = ContinuousLinearMap.inr ℂ (𝕄 × 𝕄) 𝕄
      (mmul (mmul (mmul (psi k z).1.1 Z) (psi k z).1.2) (psi k z).2) := by
    have h1 := toMK_mul_inv k
    refine Prod.ext rfl ?_
    show toMK k⁻¹ * (Z * z) * toMK k = toMK k⁻¹ * Z * toMK k * (toMK k⁻¹ * z * toMK k)
    calc toMK k⁻¹ * (Z * z) * toMK k = toMK k⁻¹ * Z * (toMK k * toMK k⁻¹) * z * toMK k := by
          rw [h1]
          simp only [mul_one, mul_assoc]
      _ = toMK k⁻¹ * Z * toMK k * (toMK k⁻¹ * z * toMK k) := by
          simp only [mul_assoc]
  show ((fderiv ℂ (Fw μ D) (psi k z)).comp (dpsi k)).smulRight (T.op k * projW T * T.op k⁻¹) (Z * z) =
    Fw μ (Z :: D) (psi k z) • (T.op k * projW T * T.op k⁻¹)
  rw [hrep, ← hv]
  rfl

lemma lWord_psM [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∀ (D : List MM) (z : MM), z ∈ Ps1.Uset ε →
      lWord D (psM T μ) z = cc T • ∫ k, G T μ D z k ∂(muK ε)
  | [], _, _ => rfl
  | Z :: D, z, hz => by
    have hE : (fun x : 𝕄 => lWord D (psM T μ) x) =ᶠ[𝓝 z]
        fun x => cc T • ∫ k, G T μ D x k ∂(muK ε) :=
      Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx => lWord_psM T μ D x hx
    have hd := (hasFDerivAt_intG T μ D hz).const_smul (cc T)
    show fderiv ℂ (fun x : 𝕄 => lWord D (psM T μ) x) z (Z * z) = _
    have h1 : fderiv ℂ (fun x : 𝕄 => lWord D (psM T μ) x) z = cc T • ∫ k, G' T μ D z k ∂(muK ε) :=
      hE.fderiv_eq.trans hd.fderiv
    refine (congrArg (fun L : 𝕄 →L[ℂ] (T.V →L[ℂ] T.V) => L (Z * z)) h1).trans ?_
    refine ((ContinuousLinearMap.smul_apply _ _ _).trans (congrArg (fun v => cc T • v)
      (ContinuousLinearMap.integral_apply (integrable_G' T μ D hz) (Z * z)))).trans ?_
    exact congrArg (fun v => cc T • v)
      (integral_congr_ae (Filter.Eventually.of_forall fun k => G'_apply T μ D hz k Z))

end PsW

theorem psM_word (n : ℕ) : PsMWordInterface n := by
  intro ε Λ T μ
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  refine ⟨Ps1.Uset ε, Ps1.isOpen_Uset, Ps1.posSet_subset_Uset, fun z hz k => hz k, fun D =>
    ⟨?_, fun z hz => PsW.continuous_Fwk μ D hz, fun z hz => ?_⟩⟩
  · intro z hz
    have heq : lWord D (psM T μ) =ᶠ[𝓝 z] fun x => PsW.cc T • ∫ k, PsW.G T μ D x k ∂(muK ε) :=
      Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx => PsW.lWord_psM T μ D x hx
    have hd : DifferentiableAt ℂ (fun x => PsW.cc T • ∫ k, PsW.G T μ D x k ∂(muK ε)) z :=
      ((PsW.hasFDerivAt_intG T μ D hz).const_smul (PsW.cc T)).differentiableAt
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  · rw [PsW.lWord_psM T μ D z hz]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
