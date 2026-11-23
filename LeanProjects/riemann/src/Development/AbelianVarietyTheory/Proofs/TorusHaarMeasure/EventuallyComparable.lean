import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder

namespace GlobalTheory.MajorantContinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_l {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_r {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma scale_lemma {n : ℕ} (s : ℝ) (A B : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, (s : ℂ) * A a * M a b * ((s : ℂ) * B b) = ((s ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, A a * M a b * B b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

lemma maj_real_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by
  have hc : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e2 : hermC τ.1 X.Gm ((t : ℂ) • v) ((t : ℂ) • v) = ((t ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_l, hermC_smul_r, hc]; push_cast; ring
  unfold Data.maj Data.posPart
  rw [e2]
  simp_rw [hermC_smul_l (a := (t : ℂ)) (u := v), map_mul, hc]
  rw [scale_lemma, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

lemma continuousAt_maj {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by
  have hH : ∀ f g : Frame X.Ψ r × (Fin r → ℂ) → (Fin r → ℂ), Continuous f → Continuous g →
      Continuous fun p => hermC τ.1 X.Gm (f p) (g p) := by
    intro f g hf hg
    unfold hermC
    have hf' : ∀ a, Continuous fun p => f p a := fun a => (continuous_apply a).comp hf
    have hg' : ∀ b, Continuous fun p => g p b := fun b => (continuous_apply b).comp hg
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hf' a).mul continuous_const).mul (Complex.continuous_conj.comp (hg' b))
  have hcol : ∀ k : Fin r, Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => col (mat p.1 τ) k := by
    intro k
    change Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => fun i => p.1 τ i k
    exact continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply τ).comp continuous_fst))
  have hG : Continuous fun y : Frame X.Ψ r => X.gramPos y τ := by
    unfold Data.gramPos
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_gram X τ).matrix_submatrix _ _
  have hdet : (X.gramPos x τ).det ≠ 0 := (X.gramPos_posDef hx τ).det_pos.ne'
  have hI : ContinuousAt (fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) x := by
    refine (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hIab : ∀ a b : Fin X.p0,
      ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹ a b) (x, v) :=
    fun a b => by
      have hI' : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹) (x, v) :=
        ContinuousAt.comp (g := fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) (f := Prod.fst) hI
          continuous_fst.continuousAt
      exact ContinuousAt.comp (g := fun M : Matrix (Fin X.p0) (Fin X.p0) ℂ => M a b)
        (continuous_id.matrix_elem a b).continuousAt hI'
  unfold Data.maj Data.posPart
  refine ContinuousAt.sub (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_))
    (Complex.continuous_re.comp (hH _ _ continuous_snd continuous_snd)).continuousAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  exact (((hH _ _ continuous_snd (hcol _)).continuousAt.mul (hIab a b)).mul
    (Complex.continuous_conj.comp (hH _ _ continuous_snd (hcol _))).continuousAt)

lemma exists_sphere {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ w ∈ Metric.sphere (0 : Fin r → ℂ) 1, v = ((‖v‖ : ℝ) : ℂ) • w := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn), one_smul]

lemma maj_at_zero {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC]

lemma ne_zero_of_sphere {r : ℕ} {w : Fin r → ℂ} (hw : w ∈ Metric.sphere (0 : Fin r → ℂ) 1) :
    w ≠ 0 := by
  rintro rfl
  rw [mem_sphere_zero_iff_norm, norm_zero] at hw
  exact zero_ne_one hw

theorem eventually_comparable {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v := by
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ X.dom := (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have key : ∀ τ : X.Ψ, ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      X.maj x τ w < (1 + ε) * X.maj y τ w ∧ X.maj y τ w < (1 + ε) * X.maj x τ w := by
    intro τ
    refine (isCompact_sphere (0 : Fin r → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro w hw
    have hpos : 0 < X.maj x τ w := X.maj_pos hx τ (ne_zero_of_sphere hw)
    have h1 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, w) :=
      continuousAt_maj X τ hx w
    have h2 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj x τ p.2) (x, w) :=
      ContinuousAt.comp_of_eq (g := fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
        (f := fun p : Frame X.Ψ r × (Fin r → ℂ) => (x, p.2)) h1
        (continuous_const.prodMk continuous_snd).continuousAt rfl
    refine (h2.eventually_lt (continuousAt_const.mul h1) ?_).and
      (h1.eventually_lt (continuousAt_const.mul h2) ?_)
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
  filter_upwards [hdom, Filter.eventually_all.2 key] with y hy hk
  refine ⟨hy, fun τ v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hx' : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hy' : X.maj y τ v = ‖v‖ ^ 2 * X.maj y τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X y τ _ w
  obtain ⟨k1, k2⟩ := hk τ w hw
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hx', hy']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k1.le ht]
  · nlinarith [mul_le_mul_of_nonneg_left k2.le ht]

theorem compact_bounds {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)} (hK : IsCompact K)
    (hKd : K ⊆ X.dom) : ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2 := by
  classical
  have hKS := hK.prod (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hcont : ∀ τ : X.Ψ, ContinuousOn (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
      (K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    fun τ => continuousOn_of_forall_continuousAt fun p hp => continuousAt_maj X τ (hKd hp.1) p.2
  have hlow : ∀ τ : X.Ψ, ∃ c', 0 < c' ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1,
      c' ≤ X.maj p.1 τ p.2 :=
    fun τ => hKS.exists_forall_le' (hcont τ) fun p hp => X.maj_pos (hKd hp.1) τ (ne_zero_of_sphere hp.2)
  have hup : ∀ τ : X.Ψ, ∃ C', ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1, ‖X.maj p.1 τ p.2‖ ≤ C' :=
    fun τ => hKS.exists_bound_of_continuousOn (hcont τ)
  choose cτ hcpos hcle using hlow
  choose Cτ hCle using hup
  have hsum : 0 ≤ ∑ σ, (cτ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hcpos σ)).le
  refine ⟨(1 + ∑ σ, (cτ σ)⁻¹)⁻¹, ∑ σ, |Cτ σ|, inv_pos.2 (by linarith), ?_⟩
  intro x hx τ v
  have hc_le : (1 + ∑ σ, (cτ σ)⁻¹)⁻¹ ≤ cτ τ := by
    have h1 : (cτ τ)⁻¹ ≤ ∑ σ, (cτ σ)⁻¹ :=
      Finset.single_le_sum (f := fun σ => (cτ σ)⁻¹) (fun σ _ => (inv_pos.2 (hcpos σ)).le)
        (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  have hC_le : Cτ τ ≤ ∑ σ, |Cτ σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cτ σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ))
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hm : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hlo : cτ τ ≤ X.maj x τ w := hcle τ (x, w) ⟨hx, hw⟩
  have hhi : X.maj x τ w ≤ Cτ τ := (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm.trans_le (hCle τ (x, w) ⟨hx, hw⟩))
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hc_le.trans hlo) ht]
  · nlinarith [mul_le_mul_of_nonneg_left (hhi.trans hC_le) ht]

theorem majorant_continuity :
    ((∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) ∧ (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2)) := ⟨fun _ X _ hx _ hε => eventually_comparable X hx hε,
    fun _ X _ hK hKd => compact_bounds X hK hKd⟩

end GlobalTheory.MajorantContinuity
