import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary

noncomputable section

open Filter Topology Module

namespace CompanionTheory.RgGu.NR.Sig

def qf {n : ℕ} (M : Fin n → Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, ∑ j, x i * (star (y j) * M i j)

theorem cont_qf {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => qf p.1 p.2.1 p.2.2 := by
  unfold qf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
    ((continuous_star.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)))

theorem qf_smul {n : ℕ} (M : Fin n → Fin n → ℂ) (a : ℂ) (x y : Fin n → ℂ) :
    qf M (a • x) (a • y) = a * star a * qf M x y := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_single {n : ℕ} (M : Fin n → Fin n → ℂ) (i j : Fin n) :
    qf M (Pi.single i 1) (Pi.single j 1) = M i j := by
  classical
  simp [qf, Pi.single_apply]

variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

abbrev Sq (W : Type) [AddCommGroup W] [Module ℂ W] := W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ

abbrev ef (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun

def gram (B : Sq W) : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ :=
  fun i j => B (Module.finBasis ℂ W i) (Module.finBasis ℂ W j)

def mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : Sq W :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => qf M (ef W v) (ef W w))
    (fun v v' w => by simp only [qf, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun v w w' => by
      simp only [qf, map_add, Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, starRingEnd_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem mk_apply (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) (v w : W) :
    mk M v w = qf M (ef W v) (ef W w) := rfl

theorem expand (B : Sq W) (v w : W) : B v w = qf (gram B) (ef W v) (ef W w) := by
  conv_lhs => rw [← (Module.finBasis ℂ W).sum_equivFun v, ← (Module.finBasis ℂ W).sum_equivFun w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    qf, gram, starRingEnd_apply, Finset.mul_sum, ef]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mk_gram (B : Sq W) : mk (gram B) = B := by
  ext v w
  rw [mk_apply, expand]

theorem gram_mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : gram (mk M : Sq W) = M := by
  funext i j
  have h : ∀ a, (Module.finBasis ℂ W).equivFun (Module.finBasis ℂ W a) = Pi.single a 1 := fun a => by
    funext b
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  simp only [gram, mk_apply, ef, h]
  exact qf_single M i j

theorem gram_smul (c : ℂ) (B : Sq W) : gram (c • B) = c • gram B := by
  funext i j
  simp [gram]

section Fam

variable {I : Type} (ι : I → I) (T : I → Module.End ℂ W)

def Inv (B : Sq W) : Prop := ∀ i v w, B (T i v) w = B v (T (ι i) w)

def Herm (B : Sq W) : Prop := ∀ v w, B w v = starRingEnd ℂ (B v w)

def Pos (B : Sq W) : Prop := ∀ v, v ≠ 0 → 0 < (B v v).re

variable {ι T}

theorem ker_bot (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B : Sq W) (hB : B ≠ 0)
    (hinv : Inv ι T B) : LinearMap.ker B = ⊥ := by
  have hst : ∀ i, ∀ w ∈ LinearMap.ker B, T i w ∈ LinearMap.ker B := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    ext u
    rw [hinv, hw]
    rfl
  rcases hsim (LinearMap.ker B) hst with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB

theorem inv_sub {B B' : Sq W} (h : Inv ι T B) (h' : Inv ι T B') (c : ℂ) : Inv ι T (B - c • B') := by
  intro i v w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h i v w, h' i v w]

theorem uniq (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B₀ B : Sq W) (h0 : B₀ ≠ 0)
    (hinv0 : Inv ι T B₀) (hinv : Inv ι T B) : ∃ c : ℂ, B = c • B₀ := by
  classical
  have hk := ker_bot hsim B₀ h0 hinv0
  let b := Module.finBasis ℂ W
  let E : (W →ₛₗ[starRingEnd ℂ] ℂ) →ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) :=
    { toFun := fun f j => f (b j)
      map_add' := fun f g => by funext j; simp
      map_smul' := fun c f => by funext j; simp }
  have hE : Function.Injective E := fun f g h => b.ext fun j => congrFun h j
  have hinj : Function.Injective (E ∘ₗ B₀) := hE.comp (LinearMap.ker_eq_bot.1 hk)
  have hdim : finrank ℂ W = finrank ℂ (Fin (finrank ℂ W) → ℂ) := by simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  let e := LinearEquiv.ofBijective (E ∘ₗ B₀) ⟨hinj, hsurj⟩
  let A : Module.End ℂ W := e.symm.toLinearMap ∘ₗ (E ∘ₗ B)
  have : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h0 (by ext v w; simp [Subsingleton.elim v 0])
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hAx : A x = c • x := Module.End.mem_eigenspace_iff.1 hx.1
  have key : B x = B₀ (c • x) := by
    apply hE
    have h1 := congrArg e hAx
    have h2 : e (A x) = E (B x) := by simp [A]
    rw [h2] at h1
    rw [h1]
    exact LinearEquiv.ofBijective_apply _ _
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : B - c • B₀ ≠ 0 := sub_ne_zero.2 hne
  have hk' := ker_bot hsim (B - c • B₀) hne' (inv_sub hinv hinv0 c)
  have hmem : x ∈ LinearMap.ker (B - c • B₀) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, key, map_smul, sub_self]
  rw [hk'] at hmem
  exact hx.2 ((Submodule.mem_bot ℂ).1 hmem)

theorem real_of {B₀ B : Sq W} (h0 : B₀ ≠ 0) (hh0 : Herm B₀) (hh : Herm B) (c : ℂ) (hc : B = c • B₀) :
    starRingEnd ℂ c = c := by
  obtain ⟨v, w, hvw⟩ : ∃ v w, B₀ v w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (by ext v w; simp [hn])
  have e1 := hh v w
  rw [hc] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, hh0 v w] at e1
  have hz : starRingEnd ℂ (B₀ v w) ≠ 0 := (map_ne_zero _).2 hvw
  exact (mul_right_cancel₀ hz e1).symm

theorem pos_of (B : Sq W) (hh : Herm B) (hk : LinearMap.ker B = ⊥) (hsd : ∀ v, 0 ≤ (B v v).re) : Pos B := by
  intro v hv
  rcases (hsd v).lt_or_eq with h | h
  · exact h
  exfalso
  have hvv : B v v = 0 := by
    have e := hh v v
    apply Complex.ext
    · exact h.symm
    · have := congrArg Complex.im e
      simp only [Complex.conj_im] at this
      simp only [Complex.zero_im]
      linarith
  have hB : B v = 0 := by
    ext w
    have hwv : B w v = starRingEnd ℂ (B v w) := hh v w
    have hww : (B w w).im = 0 := by
      have := congrArg Complex.im (hh w w)
      simp only [Complex.conj_im] at this
      linarith
    have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq (B v w) + t ^ 2 * Complex.normSq (B v w) * (B w w).re := by
      intro t
      set a : ℂ := -(t : ℂ) * B v w with ha
      have := hsd (v + a • w)
      have e0 : B (v + a • w) (v + a • w) =
          starRingEnd ℂ a * B v w + a * starRingEnd ℂ (B v w) + a * starRingEnd ℂ a * B w w := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
          hvv, hwv]
        ring
      have e : (B (v + a • w) (v + a • w)).re =
          -2 * t * Complex.normSq (B v w) + t ^ 2 * Complex.normSq (B v w) * (B w w).re := by
        rw [e0, ha]
        simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, Complex.conj_ofReal, hww,
          Complex.normSq_apply]
        ring
      linarith
    have hR : 0 < |(B w w).re| + 1 := by positivity
    have h1 := key (1 / (|(B w w).re| + 1))
    have hn := Complex.normSq_nonneg (B v w)
    have h2 : (1 / (|(B w w).re| + 1)) * (B w w).re ≤ 1 / (|(B w w).re| + 1) * |(B w w).re| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h3 : 1 / (|(B w w).re| + 1) * |(B w w).re| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hR]
      linarith
    have h4 : Complex.normSq (B v w) = 0 := by
      by_contra hne
      have hpos : 0 < Complex.normSq (B v w) := lt_of_le_of_ne hn (Ne.symm hne)
      have ht : 0 < 1 / (|(B w w).re| + 1) := by positivity
      nlinarith [mul_pos ht hpos]
    simpa using Complex.normSq_eq_zero.1 h4
  have hm : v ∈ LinearMap.ker B := LinearMap.mem_ker.2 hB
  rw [hk] at hm
  exact hv ((Submodule.mem_bot ℂ).1 hm)

end Fam

theorem pos_mk_iff (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) :
    (∀ v : W, v ≠ 0 → 0 < ((mk M : Sq W) v v).re) ↔ ∀ c, c ≠ 0 → 0 < (qf M c c).re := by
  constructor
  · intro h c hc
    have := h ((ef W).symm c) (((ef W).symm.map_ne_zero_iff).2 hc)
    rwa [mk_apply, LinearEquiv.apply_symm_apply] at this
  · intro h v hv
    rw [mk_apply]
    exact h _ ((LinearEquiv.map_ne_zero_iff _).2 hv)

theorem pos_open {n : ℕ} (M : Fin n → Fin n → ℂ) (hM : ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M c c).re) :
    ∀ᶠ M' in 𝓝 M, ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M' c c).re := by
  have hK : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have hcont : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (qf p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (cont_qf.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)))
  have h1 : ∀ᶠ M' in 𝓝 M, ∀ u ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (qf M' u u).re := by
    refine hK.eventually_forall_of_forall_eventually fun u hu => ?_
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu
      exact zero_ne_one hu
    exact (hcont.tendsto (M, u)).eventually (lt_mem_nhds (hM u hu0))
  filter_upwards [h1] with M' hM' c hc
  set a : ℂ := (‖c‖ : ℂ)
  have ha : a ≠ 0 := by simpa [a] using hc
  have hu : a⁻¹ • c ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv]
    simp [a, norm_ne_zero_iff.2 hc]
  have e : c = a • (a⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [e, qf_smul]
  have hs : a * star a = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [a, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [hs, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) (hM' _ hu)

theorem mk_smul (a : ℂ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : (mk (a • M) : Sq W) = a • mk M := by
  ext v w
  simp only [mk_apply, qf, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section Real

variable {I : Type} {ι : I → I} {T : I → Module.End ℂ W}

omit [FiniteDimensional ℂ W] in
theorem herm_smul {B : Sq W} (h : Herm B) (r : ℝ) : Herm ((r : ℂ) • B) := by
  intro v w
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h v w]

omit [FiniteDimensional ℂ W] in
theorem inv_smul {B : Sq W} (h : Inv ι T B) (c : ℂ) : Inv ι T (c • B) := by
  intro i v w
  simp only [LinearMap.smul_apply, h i v w]

theorem normalize (B : Sq W) (hB : B ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ‖gram ((r : ℂ) • B)‖ = 1 := by
  have hg : gram B ≠ 0 := by
    intro h
    apply hB
    rw [← mk_gram B, h]
    ext v w
    simp [mk_apply, qf]
  refine ⟨‖gram B‖⁻¹, inv_pos.2 (norm_pos_iff.2 hg), ?_⟩
  rw [gram_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hg)),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]

end Real

set_option maxHeartbeats 400000 in
theorem lim_form {I : Type} (ι : I → I) (T : ℝ → I → Module.End ℂ W)
    (hc : ∀ (i : I) (w : W) (l : Module.Dual ℂ W), Continuous fun s => l (T s i w))
    (s : ℕ → ℝ) (p : ℝ) (hs : Tendsto s atTop (𝓝 p)) (B : ℕ → Sq W) (hinv : ∀ k, Inv ι (T (s k)) (B k))
    (hh : ∀ k, Herm (B k)) (hn : ∀ k, ‖gram (B k)‖ = 1) :
    ∃ (φ : ℕ → ℕ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ), StrictMono φ ∧ ‖M‖ = 1 ∧
      Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) ∧ Inv ι (T p) (mk M) ∧ Herm (mk M) ∧
      ∀ v w, Tendsto (fun k => B (φ k) v w) atTop (𝓝 (mk M v w)) := by
  have hmem : ∀ k, gram (B k) ∈ Metric.sphere (0 : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) 1 := fun k => by
    rw [mem_sphere_zero_iff_norm]
    exact hn k
  obtain ⟨M, hM, φ, hφ, hlim0⟩ := (isCompact_sphere (0 : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) 1).tendsto_subseq
    hmem
  have hMn : ‖M‖ = 1 := mem_sphere_zero_iff_norm.1 hM
  have hcoord : ∀ i j, Tendsto (fun k => gram (B (φ k)) i j) atTop (𝓝 (M i j)) := by
    intro i j
    have h0 : Tendsto (fun k => ‖gram (B (φ k)) - M‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hlim0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0
    have h1 := norm_le_pi_norm ((gram (B (φ k)) - M) i) j
    have h2 := norm_le_pi_norm (gram (B (φ k)) - M) i
    simp only [Pi.sub_apply] at h1 h2
    exact h1.trans h2
  have hlim : Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hcoord i j
  have hcT : ∀ i v, Continuous fun t => ef W (T t i v) := fun i v => by
    refine continuous_pi fun j => ?_
    have h := hc i v ((Module.finBasis ℂ W).coord j)
    have e : (fun t => ef W (T t i v) j) = fun t => (Module.finBasis ℂ W).coord j (T t i v) := by
      funext t
      rw [Module.Basis.coord_apply, ef, Module.Basis.equivFun_apply]
    rw [e]
    exact h
  have key : ∀ (x y : ℕ → W) (x0 y0 : W), Tendsto (fun k => ef W (x k)) atTop (𝓝 (ef W x0)) →
      Tendsto (fun k => ef W (y k)) atTop (𝓝 (ef W y0)) →
      Tendsto (fun k => B (φ k) (x k) (y k)) atTop (𝓝 (mk M x0 y0)) := by
    intro x y x0 y0 hx hy
    have e : (fun k => B (φ k) (x k) (y k)) = fun k => qf (gram (B (φ k))) (ef W (x k)) (ef W (y k)) := by
      funext k
      exact expand _ _ _
    rw [e, mk_apply]
    unfold qf
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact (tendsto_pi_nhds.1 hx i).mul (((continuous_star.tendsto _).comp (tendsto_pi_nhds.1 hy j)).mul
      (hcoord i j))
  have hsφ : Tendsto (fun k => s (φ k)) atTop (𝓝 p) := hs.comp hφ.tendsto_atTop
  have cst : ∀ v : W, Tendsto (fun _ : ℕ => ef W v) atTop (𝓝 (ef W v)) := fun v => tendsto_const_nhds
  refine ⟨φ, M, hφ, hMn, hlim, fun i v w => ?_, fun v w => ?_, fun v w => key _ _ v w (cst v) (cst w)⟩
  · have h1 := key (fun k => T (s (φ k)) i v) (fun _ => w) (T p i v) w (((hcT i v).tendsto p).comp hsφ) (cst w)
    have h2 := key (fun _ => v) (fun k => T (s (φ k)) (ι i) w) v (T p (ι i) w) (cst v)
      (((hcT (ι i) w).tendsto p).comp hsφ)
    have e : (fun k => B (φ k) (T (s (φ k)) i v) w) = fun k => B (φ k) v (T (s (φ k)) (ι i) w) :=
      funext fun k => hinv (φ k) i v w
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 := key (fun _ => w) (fun _ => v) w v (cst w) (cst v)
    have h2 := key (fun _ => v) (fun _ => w) v w (cst v) (cst w)
    have h3 : Tendsto (fun k => B (φ k) w v) atTop (𝓝 (starRingEnd ℂ (mk M v w))) := by
      have e : (fun k => B (φ k) w v) = fun k => starRingEnd ℂ (B (φ k) v w) := funext fun k => hh (φ k) v w
      rw [e]
      exact (Complex.continuous_conj.tendsto _).comp h2
    exact tendsto_nhds_unique h1 h3

end CompanionTheory.RgGu.NR.Sig

namespace CompanionTheory.RgGu.NR

open Sig

set_option maxHeartbeats 800000 in
theorem signature : Signature := by
  intro I W _ _ _ ι T hc hsim hex hpos _ s hs B hB hh hinv
  classical
  have hnt : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hB (by ext v w; simp [Subsingleton.elim v 0])
  have hpos_ne : ∀ B₀ : Sq W, Sig.Pos B₀ → B₀ ≠ 0 := by
    intro B₀ h e
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have := h v hv
    rw [e] at this
    simp at this
  have re_smul : ∀ (c : ℂ) (z : ℂ), c.im = 0 → (c * z).re = c.re * z.re := by
    intro c z h
    simp [Complex.mul_re, h]
  let D : Set ℝ := {t | ∃ B₀ : Sq W, Sig.Herm B₀ ∧ Sig.Inv ι (T t) B₀ ∧ Sig.Pos B₀}
  let P : Set (Set.Ici (0 : ℝ)) := {x | x.1 ∈ D}
  have : PreconnectedSpace (Set.Ici (0 : ℝ)) := Subtype.preconnectedSpace isPreconnected_Ici
  have hcl : IsClosed P := by
    refine IsSeqClosed.isClosed fun x p hx hp => ?_
    have hsq : Tendsto (fun n => (x n).1) atTop (𝓝 p.1) := (continuous_subtype_val.tendsto p).comp hp
    choose B₁ hB1 hB2 hB3 using hx
    choose r hr hrn using fun k => normalize (B₁ k) (hpos_ne _ (hB3 k))
    obtain ⟨φ, M, hφ, hM, hlim, hinvM, hhM, hpt⟩ := lim_form ι T hc (fun n => (x n).1) p.1 hsq
      (fun k => (r k : ℂ) • B₁ k) (fun k => inv_smul (hB2 k) _) (fun k => herm_smul (hB1 k) _) hrn
    have hsd : ∀ v, 0 ≤ ((mk M : Sq W) v v).re := by
      intro v
      refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (hpt v v)) (Eventually.of_forall fun k => ?_)
      show 0 ≤ (((r (φ k) : ℂ) • B₁ (φ k)) v v).re
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      by_cases hv : v = 0
      · simp [hv]
      · exact (mul_pos (hr _) (hB3 _ v hv)).le
    have hne : (mk M : Sq W) ≠ 0 := by
      intro e
      have := gram_mk (W := W) M
      rw [e] at this
      have h0 : gram (0 : Sq W) = 0 := by funext i j; simp [gram]
      rw [h0] at this
      rw [← this] at hM
      simp at hM
    exact ⟨mk M, hhM, hinvM, pos_of _ hhM (ker_bot (hsim p.1 p.2) _ hne hinvM) hsd⟩
  have hop : IsClosed Pᶜ := by
    refine IsSeqClosed.isClosed fun x p hx hp => ?_
    intro hpD
    obtain ⟨B₀, h0h, h0i, h0p⟩ := hpD
    have hsq : Tendsto (fun n => (x n).1) atTop (𝓝 p.1) := (continuous_subtype_val.tendsto p).comp hp
    choose B₁ hB1 hB2 hB3 using fun k => hex (x k).1 (x k).2
    choose r hr hrn using fun k => normalize (B₁ k) (hB1 k)
    obtain ⟨φ, M, hφ, hM, hlim, hinvM, hhM, hpt⟩ := lim_form ι T hc (fun n => (x n).1) p.1 hsq
      (fun k => (r k : ℂ) • B₁ k) (fun k => inv_smul (hB3 k) _) (fun k => herm_smul (hB2 k) _) hrn
    have hne : (mk M : Sq W) ≠ 0 := by
      intro e
      have := gram_mk (W := W) M
      rw [e] at this
      have h0 : gram (0 : Sq W) = 0 := by funext i j; simp [gram]
      rw [h0] at this
      rw [← this] at hM
      simp at hM
    obtain ⟨c, hc⟩ := uniq (hsim p.1 p.2) B₀ (mk M) (hpos_ne _ h0p) h0i hinvM
    have hcr := real_of (hpos_ne _ h0p) h0h hhM c hc
    have hcim : c.im = 0 := by
      have := congrArg Complex.im hcr
      simp only [Complex.conj_im] at this
      linarith
    have hc0 : c.re ≠ 0 := by
      intro h
      apply hne
      have : c = 0 := Complex.ext h hcim
      rw [hc, this, zero_smul]
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, 0 < σ * c.re := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · exact ⟨-1, by linarith⟩
      · exact ⟨1, by linarith⟩
    have hposM : ∀ y, y ≠ 0 → 0 < (qf ((σ : ℂ) • M) y y).re := by
      rw [← pos_mk_iff]
      intro v hv
      rw [mk_smul, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul, ← mul_assoc, re_smul _ _ (by simp [hcim])]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcim, mul_zero, sub_zero]
      exact mul_pos hσ (h0p v hv)
    have hev := (hlim.const_smul (σ : ℂ)).eventually (pos_open _ hposM)
    obtain ⟨k, hk⟩ := hev.exists
    apply hx (φ k)
    refine ⟨(σ : ℂ) • ((r (φ k) : ℂ) • B₁ (φ k)), herm_smul (herm_smul (hB2 _) _) σ, inv_smul (inv_smul (hB3 _) _) _, ?_⟩
    have hk' := (pos_mk_iff (W := W) _).2 hk
    rwa [← gram_smul, mk_gram] at hk'
  have hne : P.Nonempty := by
    obtain ⟨B₀, h1, h2, h3⟩ := hpos
    exact ⟨⟨0, Set.mem_Ici.2 le_rfl⟩, B₀, h1, h3, h2⟩
  have huniv := IsClopen.eq_univ ⟨hcl, isClosed_compl_iff.1 hop⟩ hne
  have hsD : s ∈ D := by
    have : (⟨s, hs⟩ : Set.Ici (0 : ℝ)) ∈ P := by rw [huniv]; trivial
    exact this
  obtain ⟨B₀, h0h, h0i, h0p⟩ := hsD
  obtain ⟨c, hc⟩ := uniq (hsim s hs) B₀ B (hpos_ne _ h0p) h0i hinv
  have hcr := real_of (hpos_ne _ h0p) h0h hh c hc
  have hcim : c.im = 0 := by
    have := congrArg Complex.im hcr
    simp only [Complex.conj_im] at this
    linarith
  have hval : ∀ v, (B v v).re = c.re * (B₀ v v).re := by
    intro v
    rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, re_smul _ _ hcim]
  have hc0 : c.re ≠ 0 := by
    intro h
    apply hB
    have : c = 0 := Complex.ext h hcim
    rw [hc, this, zero_smul]
  rcases lt_or_gt_of_ne hc0 with h | h
  · right
    intro v hv
    rw [hval]
    exact mul_neg_of_neg_of_pos h (h0p v hv)
  · left
    intro v hv
    rw [hval]
    exact mul_pos h (h0p v hv)

end CompanionTheory.RgGu.NR
