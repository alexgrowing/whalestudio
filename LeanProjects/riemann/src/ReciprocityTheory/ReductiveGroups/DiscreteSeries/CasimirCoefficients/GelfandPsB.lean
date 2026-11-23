import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPsA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP

noncomputable section

open Finset MeasureTheory Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GPs

lemma contDiff_entry (i j : Fin n) : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z i j) := by
  first
    | exact contDiff_apply_apply (𝕜 := ℂ) (n := ∞) i j
    | fun_prop
    | exact ((contDiff_apply ℂ (Fin n → ℂ) i).clm_apply contDiff_const).comp contDiff_id

lemma contDiff_mat {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : X → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ContDiff ℂ ∞ (fun x => f x i j)) : ContDiff ℂ ∞ f := by
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => h i j

lemma contDiff_mmul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f g : X → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiff ℂ ∞ f) (hg : ContDiff ℂ ∞ g) : ContDiff ℂ ∞ (fun x => f x * g x) := by
  apply contDiff_mat
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp hf).mul ((contDiff_entry k j).comp hg)

lemma contDiff_trip : ContDiff ℂ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ ×
    Matrix (Fin n) (Fin n) ℂ => p.2.2 * p.1 * p.2.1) := by
  exact contDiff_mmul (contDiff_mmul (contDiff_snd.comp contDiff_snd) contDiff_fst) (contDiff_fst.comp contDiff_snd)

lemma contDiff_lead' (i : ℕ) : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dite_true, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
      | exact contDiff_prod fun l _ => contDiff_entry (Fin.castLE h (σ l)) (Fin.castLE h l)
      | exact ContDiff.finset_prod fun l _ => contDiff_entry (Fin.castLE h (σ l)) (Fin.castLE h l)
  · simp only [h, dite_false]
    exact contDiff_const

lemma isOpen_omega : IsOpen (OmegaSet n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  exact ReciprocityTheory.ChartRestriction.DS.S7.isOpen_omega

lemma contDiffOn_zpow' {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℂ ∞ (fun y => f y ^ m) s := by
  rcases m with k | k
  · simpa only [Int.ofNat_eq_coe, zpow_natCast] using hf.pow k
  · refine ((hf.pow (k + 1)).inv (fun x hx => pow_ne_zero _ (h0 x hx))).congr fun x _ => ?_
    exact zpow_negSucc (f x) k

lemma sm_phi (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) := by
  exact phiM_contDiffOn μ

def Wset (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  {p | p.2.2 * p.1 * p.2.1 ∈ OmegaSet n}

lemma isOpen_kappaOpenNeighbourhood : IsOpen (Wset n) := by
  exact isOpen_omega.preimage contDiff_trip.continuous

def g0 (μ : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun p => PhiM μ (p.2.2 * p.1 * p.2.1)

lemma smooth_g0_on_Wset (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (g0 μ) (Wset n) := by
  exact (sm_phi μ).comp contDiff_trip.contDiffOn (fun p hp => hp)

lemma dAtW {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) {p} (hp : p ∈ Wset n) : DifferentiableAt ℂ g p := by
  exact (hg.contDiffAt (isOpen_kappaOpenNeighbourhood.mem_nhds hp)).differentiableAt (by simp)

def DH (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun p => fderiv ℂ g p (X * p.1, 0)

lemma sm_DH (X : Matrix (Fin n) (Fin n) ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) : ContDiffOn ℂ ∞ (DH X g) (Wset n) := by
  have h2 : ContDiff ℂ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      ((X * p.1, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    (contDiff_mmul contDiff_const contDiff_fst).prodMk contDiff_const
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    first | simp | (exact_mod_cast le_rfl) | norm_cast | exact le_of_eq (by rfl)
  exact (hg.fderiv_of_isOpen isOpen_kappaOpenNeighbourhood hmn).clm_apply h2.contDiffOn

lemma DH_slice (X : Matrix (Fin n) (Fin n) ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ} {p}
    (hg : DifferentiableAt ℂ g p) : DH X g p = Lhol X (fun y => g (y, p.2)) p.1 := by
  have hs : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, p.2) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      ((ContinuousLinearMap.id ℂ _).prod 0) p.1 := (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have h1 := hg.hasFDerivAt.comp p.1 hs
  have h2 : fderiv ℂ (fun y => g (y, p.2)) p.1 = (fderiv ℂ g p).comp ((ContinuousLinearMap.id ℂ _).prod 0) := h1.fderiv
  unfold DH Lhol
  rw [h2]
  rfl

def I0 (n : ℕ) := fderiv ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
  ((y, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) 0

lemma zeroEmbedding_apply (H : Matrix (Fin n) (Fin n) ℂ) : I0 n H = (H, 0) := by
  have hs : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      ((ContinuousLinearMap.id ℂ _).prod 0) 0 := (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  unfold I0
  rw [hs.fderiv]
  rfl

lemma hasFDerivAt_slice (q : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, q) : Matrix (Fin n) (Fin n) ℂ ×
      Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) (I0 n) x := by
  have hs : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, q) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      ((ContinuousLinearMap.id ℂ _).prod 0) x := (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  exact hs.congr_fderiv (ContinuousLinearMap.ext fun H => by rw [zeroEmbedding_apply]; rfl)

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

local notation "𝕄f" => Fin n → Fin n → ℂ

def cK (T : KType ε Λ) : ℂ := (Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)

def Pk (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V := T.op k * projW T * T.op k⁻¹

def emb (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  (x, toMK k, toMK k⁻¹)

def Fint (T : KType ε Λ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  cK T • ∫ k, g (emb x k) • Pk T k ∂(muK ε)

lemma psM_eq (T : KType ε Λ) (μ : Fin n → ℤ) : psM T μ = Fint T (g0 μ) := rfl

lemma continuous_emb : Continuous (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => emb q.1 q.2) := by
  have hM : Continuous (fun k : KG ε => toMK k) := by
    unfold toMK toM
    first
      | fun_prop
      | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
      | done
  exact continuous_fst.prodMk ((hM.comp continuous_snd).prodMk (hM.comp (continuous_inv.comp continuous_snd)))

lemma emb_mem {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Ps1.Uset ε) (k : KG ε) : emb x k ∈ Wset n := by
  exact hx k

def FD (T : KType ε Λ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : 𝕄f →L[ℂ] (T.V →L[ℂ] T.V) :=
  fderiv ℂ (fun y : 𝕄f => g (emb y k) • Pk T k) x

lemma hasFDerivAt_FD (T : KType ε Λ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : emb x k ∈ Wset n) :
    HasFDerivAt (fun y : 𝕄f => g (emb y k) • Pk T k) (FD T g x k) x := by
  have h1 := ((dAtW hg hx).hasFDerivAt.comp x (hasFDerivAt_slice (toMK k, toMK k⁻¹) x)).smul_const (Pk T k)
  exact h1.differentiableAt.hasFDerivAt

lemma FD_apply (T : KType ε Λ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : emb x k ∈ Wset n)
    (H : Matrix (Fin n) (Fin n) ℂ) : FD T g x k H = fderiv ℂ g (emb x k) (H, 0) • Pk T k := by
  have h1 := ((dAtW hg hx).hasFDerivAt.comp x (hasFDerivAt_slice (toMK k, toMK k⁻¹) x)).smul_const (Pk T k)
  have h2 : FD T g x k = ((fderiv ℂ g (emb x k)).comp (I0 n)).smulRight (Pk T k) := h1.fderiv
  have h3 : ∀ v : Matrix (Fin n) (Fin n) ℂ, ((fderiv ℂ g (emb x k)).comp (I0 n)).smulRight (Pk T k) v =
      fderiv ℂ g (emb x k) (v, 0) • Pk T k := fun v => by
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, zeroEmbedding_apply]
  rw [h2]
  exact h3 H

section Int

variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}

lemma contOn_FD (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) :
    ContinuousOn (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => FD T g q.1 q.2) (Ps1.Uset ε ×ˢ Set.univ) := by
  have hop : Continuous (fun k : KG ε => T.op k) := continuous_subtype_val.comp T.cont
  have hPk : Continuous (Pk T) := (hop.mul continuous_const).mul (hop.comp continuous_inv)
  rw [continuousOn_clm_apply]
  intro H
  have hc : ContinuousOn (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => fderiv ℂ g (emb q.1 q.2) (H, 0) • Pk T q.2)
      (Ps1.Uset ε ×ˢ Set.univ) :=
    (((hg.continuousOn_fderiv_of_isOpen isOpen_kappaOpenNeighbourhood (by simp)).comp continuous_emb.continuousOn
      (fun q hq => emb_mem hq.1 q.2)).clm_apply continuousOn_const).smul (hPk.comp continuous_snd).continuousOn
  refine hc.congr fun q hq => ?_
  exact FD_apply T hg q.2 (emb_mem hq.1 q.2) H

lemma cont_int (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Continuous fun k => g (emb x k) • Pk T k := by
  have hop : Continuous (fun k : KG ε => T.op k) := continuous_subtype_val.comp T.cont
  have hPk : Continuous (Pk T) := (hop.mul continuous_const).mul (hop.comp continuous_inv)
  have he : Continuous (fun k : KG ε => emb x k) := continuous_emb.comp (continuous_const.prodMk continuous_id)
  have hgc : Continuous (fun k => g (emb x k)) := hg.continuousOn.comp_continuous he (fun k => emb_mem hx k)
  exact hgc.smul hPk

lemma cont_FD (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Continuous (FD T g x) := by
  exact (contOn_FD T hg).comp_continuous (continuous_const.prodMk continuous_id) (fun k => ⟨hx, Set.mem_univ _⟩)

variable [CompactSpace (KG ε)]

lemma int_int (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Integrable (fun k => g (emb x k) • Pk T k) (muK ε) := by
  exact (cont_int T hg hx).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

lemma int_FD (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Integrable (FD T g x) (muK ε) := by
  exact (cont_FD T hg hx).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

lemma hasFDerivAt_Fint (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ Ps1.Uset ε) :
    HasFDerivAt (fun x : 𝕄f => Fint T g x) (cK T • ∫ k, FD T g z k ∂(muK ε)) z := by
  unfold Fint
  refine HasFDerivAt.const_smul (f := fun x : 𝕄f => ∫ k, g (emb x k) • Pk T k ∂(muK ε)) ?_ (cK T)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (Ps1.isOpen_Uset (ε := ε)) z hz
  have hcb : Metric.closedBall z (r / 2) ⊆ Ps1.Uset ε :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (Metric.closedBall z (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall z (r / 2)).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((contOn_FD T hg).mono (Set.prod_mono hcb le_rfl))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := FD T g)
    (Metric.ball_mem_nhds (z : 𝕄f) (half_pos hr)) ?_ (int_int T hg hz) ?_ ?_ (integrable_const C) ?_
  · filter_upwards [(Ps1.isOpen_Uset (ε := ε)).mem_nhds hz] with y hy
    exact (cont_int T hg hy).aestronglyMeasurable
  · exact (cont_FD T hg hz).aestronglyMeasurable
  · exact ae_of_all _ fun k y hy => hC (y, k) ⟨Metric.ball_subset_closedBall hy, Set.mem_univ _⟩
  · exact ae_of_all _ fun k y hy => hasFDerivAt_FD T hg k (emb_mem (hcb (Metric.ball_subset_closedBall hy)) k)

lemma lhol_Fint (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) (X : Matrix (Fin n) (Fin n) ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Ps1.Uset ε) : Lhol X (Fint T g) z = Fint T (DH X g) z := by
  have h2 : fderiv ℂ (fun x : 𝕄f => Fint T g x) z = cK T • ∫ k, FD T g z k ∂(muK ε) :=
    (hasFDerivAt_Fint T hg hz).fderiv
  have h4 : fderiv ℂ (fun x : 𝕄f => Fint T g x) z (X * z) = cK T • ∫ k, FD T g z k (X * z) ∂(muK ε) := by
    rw [h2]
    exact congrArg (cK T • ·) (ContinuousLinearMap.integral_apply (int_FD T hg hz) (show 𝕄f from X * z))
  have h5 : ∀ k, FD T g z k (X * z) = DH X g (emb z k) • Pk T k := fun k => by
    rw [FD_apply T hg k (emb_mem hz k)]; rfl
  unfold Lhol
  refine h4.trans ?_
  unfold Fint
  simp only [h5]

lemma Fint_sum (T : KType ε Λ) {ι : Type*} (s : Finset ι)
    (G : ι → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hG : ∀ i ∈ s, ContDiffOn ℂ ∞ (G i) (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Fint T (∑ i ∈ s, G i) x = ∑ i ∈ s, Fint T (G i) x := by
  unfold Fint
  rw [← Finset.smul_sum]
  congr 1
  simp only [Finset.sum_apply, Finset.sum_smul]
  exact integral_finset_sum s fun i hi => int_int T (hG i hi) hx

end Int

section Ops

variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}

lemma sm_opPowH (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (hg : ContDiffOn ℂ ∞ g (Wset n))
    (m : ℕ) (a b : Fin n) : ContDiffOn ℂ ∞ (opPow (fun a b => DH (M a b)) m a b g) (Wset n) := by
  induction m generalizing a b with
  | zero =>
    simp only [opPow]
    split_ifs
    · exact hg
    · exact contDiff_zero_fun.contDiffOn
  | succ m ih =>
    simp only [opPow]
    have : (∑ c, DH (M a c) (opPow (fun a b => DH (M a b)) m c b g)) =
        fun p => ∑ c, DH (M a c) (opPow (fun a b => DH (M a b)) m c b g) p := by
      funext p; simp [Finset.sum_apply]
    rw [this]
    exact ContDiffOn.sum fun c _ => sm_DH _ (ih c b)

lemma opPowH_slice (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (hg : ContDiffOn ℂ ∞ g (Wset n))
    (m : ℕ) : ∀ a b, ∀ p ∈ Wset n, opPow (fun a b => DH (M a b)) m a b g p =
      opPow (fun a b => Lhol (M a b)) m a b (fun y => g (y, p.2)) p.1 := by
  induction m with
  | zero =>
    intro a b p hp
    simp only [opPow]
    split_ifs <;> rfl
  | succ m ih =>
    intro a b p hp
    simp only [opPow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [DH_slice (M a c) (dAtW (sm_opPowH M hg m c b) hp)]
    have hV : IsOpen {y : Matrix (Fin n) (Fin n) ℂ | (y, p.2) ∈ Wset n} :=
      isOpen_kappaOpenNeighbourhood.preimage (continuous_id.prodMk continuous_const)
    exact GPs.lhol_congr hV (fun y hy => ih c b (y, p.2) hy) (M a c) hp

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]

lemma opPow_Fint (T : KType ε Λ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hg : ContDiffOn ℂ ∞ g (Wset n)) (m : ℕ) : ∀ a b, ∀ z ∈ Ps1.Uset ε,
      opPow (fun a b => Lhol (M a b)) m a b (Fint T g) z = Fint T (opPow (fun a b => DH (M a b)) m a b g) z := by
  induction m with
  | zero =>
    intro a b z hz
    simp only [opPow]
    split_ifs
    · rfl
    · simp [Fint]
  | succ m ih =>
    intro a b z hz
    simp only [opPow, Finset.sum_apply]
    rw [Fint_sum T Finset.univ _ (fun c _ => sm_DH (M a c) (sm_opPowH M hg m c b)) hz]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GPs.lhol_congr (Ps1.isOpen_Uset (ε := ε)) (fun y hy => ih c b y hy) (M a c) hz]
    exact lhol_Fint T (sm_opPowH M hg m c b) (M a c) hz

theorem gelfand_Fint (T : KType ε Λ) (μ : Fin n → ℤ) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (C : ℂ)
    (hM : ∀ (k : KG ε) (z : Matrix (Fin n) (Fin n) ℂ), toMK k⁻¹ * z * toMK k ∈ OmegaSet n →
      opGelfand (fun a b => Lhol (M a b)) m (fun y => PhiM μ (toMK k⁻¹ * y * toMK k)) z =
        C * PhiM μ (toMK k⁻¹ * z * toMK k))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Ps1.Uset ε) :
    opGelfand (fun a b => Lhol (M a b)) m (psM T μ) z = C • psM T μ z := by
  have key : ∀ k : KG ε, (∑ a, opPow (fun a b => DH (M a b)) m a a (g0 μ)) (emb z k) =
      C * g0 μ (emb z k) := by
    intro k
    have hp := emb_mem hz k
    rw [Finset.sum_apply, Finset.sum_congr rfl fun a _ => opPowH_slice M (smooth_g0_on_Wset μ) m a a _ hp]
    have h := hM k z (hz k)
    unfold opGelfand at h
    rw [Finset.sum_apply] at h
    exact h
  rw [psM_eq]
  unfold opGelfand
  rw [Finset.sum_apply, Finset.sum_congr rfl fun a _ => opPow_Fint T M (smooth_g0_on_Wset μ) m a a z hz,
    ← Fint_sum T Finset.univ _ (fun a _ => sm_opPowH M (smooth_g0_on_Wset μ) m a a) hz]
  unfold Fint
  simp_rw [key, mul_smul]
  rw [integral_smul, smul_comm]

end Ops

lemma exp1 (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single a b 1 * B = ∑ c, ∑ d, (Aᵀ a c * Bᵀ d b) • Matrix.single c d (1 : ℂ) := by
  ext i j
  have lhs : (A * Matrix.single a b 1 * B : Matrix (Fin n) (Fin n) ℂ) i j = A i a * B b j := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  rw [lhs, Matrix.sum_apply]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma exp2 (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single (Fin.rev b) (Fin.rev a) 1 * B = ∑ c, ∑ d, ((B.submatrix Fin.revPerm Fin.revPerm) a c *
      (A.submatrix Fin.revPerm Fin.revPerm) d b) • Matrix.single (Fin.rev d) (Fin.rev c) (1 : ℂ) := by
  ext i j
  have lhs : (A * Matrix.single (Fin.rev b) (Fin.rev a) 1 * B : Matrix (Fin n) (Fin n) ℂ) i j = A i (Fin.rev b) * B (Fin.rev a) j := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
  rw [lhs, Matrix.sum_apply]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Fin.rev_eq_iff, mul_comm]

lemma tr1 {A B : Matrix (Fin n) (Fin n) ℂ} (h : B * A = 1) : Aᵀ * Bᵀ = 1 := by
  rw [← Matrix.transpose_mul, h, Matrix.transpose_one]

lemma sub1 {A B : Matrix (Fin n) (Fin n) ℂ} (h : B * A = 1) :
    (B.submatrix Fin.revPerm Fin.revPerm) * (A.submatrix Fin.revPerm Fin.revPerm) = 1 := by
  rw [Matrix.submatrix_mul_equiv, h, Matrix.submatrix_one_equiv]

end GPs

end ReciprocityTheory.ChartRestriction.DS.S7
