import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.Neumann

noncomputable section

theorem diffOn_tsum {H ι : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    {U : Set H} (hU : IsOpen U) {w : H → ℝ} (hw : ContinuousOn w U) {g : ι → H → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) {u : ι → ℝ} (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i)
    (hb : ∀ i, ∀ x ∈ U, ‖g i x‖ ≤ u i * w x) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  refine GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hg fun x hx => ?_
  have h1 : ∀ᶠ z in 𝓝 x, w z < w x + 1 :=
    (hw.continuousAt (hU.mem_nhds hx)).eventually (gt_mem_nhds (by linarith))
  refine ⟨_, Filter.inter_mem (hU.mem_nhds hx) h1, fun i => u i * (w x + 1), hu.mul_right _,
    fun i z hz => (hb i z hz.1).trans (mul_le_mul_of_nonneg_left (le_of_lt hz.2) (hu0 i))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  have h : Continuous fun x : Frame X.Ψ r => FD.gram τ.1 X.Gm (mat x τ) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [FD.gram, hermC, FD.col, mat, Matrix.of_apply]
    fun_prop
  exact (h.matrix_submatrix _ _).matrix_det

theorem isOpen_frames : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      (cont_dmin X τ i)))

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

theorem fac_pos (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 < fac X la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))) _

theorem fac_cont (la : Wt X.Ψ r) : ContinuousOn (fun x => (fac X la x)⁻¹) X.dom := by
  refine ContinuousOn.inv₀ ?_ fun x hx => (fac_pos X la hx).ne'
  refine continuousOn_finsetProd _ fun τ _ => continuousOn_finsetProd _ fun i _ => ?_
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl ?_
  · exact (((cont_dmin X τ _).continuousOn).div (cont_dmin X τ _).continuousOn
      fun x hx => dmin_ne X hx τ _).norm
  · exact norm_ne_zero_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))

theorem pnorm_le_iff (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (B : ℝ) : X.pnorm la P x ≤ B ↔ ‖P x‖ ≤ B * (fac X la x)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (fac_pos X la hx)]; rfl

omit [IsCMField E] in
theorem mapL_mul (γ δ : GL (Fin r) E) (L : Lt E r) : mapL (γ * δ) L = mapL γ (mapL δ L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

def mapE (γ : GL (Fin r) E) : Lt E r ≃ Lt E r where
  toFun := mapL γ
  invFun := mapL γ⁻¹
  left_inv L := by rw [← mapL_mul, inv_mul_cancel, mapL_one]
  right_inv L := by rw [← mapL_mul, mul_inv_cancel, mapL_one]

def op (𝓛 : Set (Lt E r)) (C : Lt E r → Lt E r → ℂ) (a : ℝ) (G : Lt E r → Frame X.Ψ r → ℂ)
    (L : Lt E r) (x : Frame X.Ψ r) : ℂ :=
  -(a : ℂ)⁻¹ * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x

variable {X} {Δ : Subgroup (GL (Fin r) E)} {𝓛 : Set (Lt E r)} {μ : GL (Fin r) E → Lt E r → ℂ}
  {la : Wt X.Ψ r} {C : Lt E r → Lt E r → ℂ} {a θ : ℝ}

theorem op_bound (ha : 0 < a)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    {G : Lt E r → Frame X.Ψ r → ℂ} {B : ℝ} (hB : 0 ≤ B) {x : Frame X.Ψ r}
    (hG : ∀ L ∈ 𝓛, ‖G L x‖ ≤ B) {L : Lt E r} (hL : L ∈ 𝓛) :
    ‖op X 𝓛 C a G L x‖ ≤ θ * B := by
  have h1 : ‖∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x‖ ≤
      (∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖) * B := by
    refine tsum_of_norm_bounded ((hC L hL).1.hasSum.mul_right B) fun L' => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hG _ L'.2.1) (norm_nonneg _)
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (hC L hL).2 hB)
  unfold op
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le,
    inv_mul_le_iff₀ ha]
  linarith

theorem op_form (ha : 0 < a)
    (hμ : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    (hinv : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛,
      C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L')
    {G : Lt E r → Frame X.Ψ r → ℂ} (hG : IsForm X Δ 𝓛 μ la G) :
    IsForm X Δ 𝓛 μ la (op X 𝓛 C a G) := by
  obtain ⟨B, hB⟩ := hG.bdd
  have hB' : ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ‖G L x‖ ≤ max B 0 * (fac X la x)⁻¹ := fun L hL x hx =>
    (pnorm_le_iff X la _ hx _).1 ((hB L hL x hx).trans (le_max_left _ _))
  refine ⟨fun L hL => ?_, fun L hL x hx b hb => ?_, fun γ hγ L hL x hx => ?_,
    θ * max B 0, fun L hL x hx => ?_⟩
  · refine DifferentiableOn.const_mul (diffOn_tsum (isOpen_frames X) (fac_cont X la)
      (fun L' => (hG.hol _ L'.2.1).const_mul _) ((hC L hL).1.mul_right (max B 0))
      (fun L' => mul_nonneg (norm_nonneg _) (le_max_right _ _)) fun L' x hx => ?_) _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB' _ L'.2.1 x hx) (norm_nonneg _)
  · unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    refine tsum_congr fun L' => ?_
    rw [hG.bor _ L'.2.1 x hx b hb]; ring
  · have he : ∀ L', (L' ∈ 𝓛 ∧ L' ≠ L) ↔ (mapE γ L' ∈ 𝓛 ∧ mapE γ L' ≠ mapL γ L) := by
      intro L'
      refine and_congr ⟨fun h => (hμ γ hγ L' h).1, fun h => ?_⟩ (mapE γ).injective.ne_iff.symm
      have := (hμ γ⁻¹ (Δ.inv_mem hγ) _ h).1
      rwa [show mapL γ⁻¹ (mapE γ L') = L' from (mapE γ).left_inv L'] at this
    unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹),
      ← ((mapE γ).subtypeEquiv he).tsum_eq]
    congr 1
    refine tsum_congr fun L' => ?_
    change C (mapL γ L) (mapL γ L'.1) * G (mapL γ L'.1) (lact γ x) = _
    rw [hG.aut γ hγ _ L'.2.1 x hx, ← hinv γ hγ L hL _ L'.2.1,
      ← Complex.inv_eq_conj (hμ γ hγ _ L'.2.1).2]
    have h0 : μ γ L ≠ 0 := norm_ne_zero_iff.1 (by rw [(hμ γ hγ L hL).2]; exact one_ne_zero)
    field_simp
  · rw [pnorm_le_iff X la _ hx, mul_assoc]
    exact op_bound ha hC (mul_nonneg (le_max_right _ _) (inv_pos.2 (fac_pos X la hx)).le)
      (fun L hL => hB' L hL x hx) hL

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (μ : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (C : Lt E r → Lt E r → ℂ) (a θ : ℝ), 0 < a → θ < 1 → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1) → (∀ γ ∈ Δ, ∀ x ∈ X.dom, lact γ x ∈ X.dom) → (∀ L ∈ 𝓛, C L L = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L') → ∀ F, IsForm X Δ 𝓛 μ la F → ∃ F', IsForm X Δ 𝓛 μ la F' ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, F L x = ∑' L' : 𝓛, C L L'.1 * F' L'.1 x := by
  intro E _ _ _ r X Δ 𝓛 μ la C a θ₀ ha hθ₀ hμ _ hC₀ hinv F hF
  set θ : ℝ := max θ₀ 0 with hθ
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hθ1 : θ < 1 := max_lt hθ₀ one_pos
  have hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a := fun L hL =>
    ⟨(hC₀ L hL).2.1, (hC₀ L hL).2.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le)⟩
  obtain ⟨G, hG0, hGs⟩ : ∃ G : ℕ → Lt E r → Frame X.Ψ r → ℂ, G 0 = F ∧
      ∀ k, G (k + 1) = op X 𝓛 C a (G k) :=
    ⟨fun k => (op X 𝓛 C a)^[k] F, rfl, fun k => Function.iterate_succ_apply' _ _ _⟩
  have hGf : ∀ k, IsForm X Δ 𝓛 μ la (G k) := by
    intro k
    induction k with
    | zero => rwa [hG0]
    | succ k ih => rw [hGs]; exact op_form ha hμ hC hinv ih
  obtain ⟨B₀, hB₀⟩ := hF.bdd
  set B : ℝ := max B₀ 0 with hBd
  have hB0 : 0 ≤ B := le_max_right _ _
  have hw : ∀ x ∈ X.dom, 0 ≤ (fac X la x)⁻¹ := fun x hx => (inv_pos.2 (fac_pos X la hx)).le
  have hGb : ∀ k, ∀ x ∈ X.dom, ∀ L ∈ 𝓛, ‖G k L x‖ ≤ θ ^ k * B * (fac X la x)⁻¹ := by
    intro k x hx
    induction k with
    | zero =>
      intro L hL
      rw [hG0, pow_zero, one_mul]
      exact (pnorm_le_iff X la _ hx _).1 ((hB₀ L hL x hx).trans (le_max_left _ _))
    | succ k ih =>
      intro L hL
      rw [hGs]
      refine (op_bound ha hC (mul_nonneg (by positivity) (hw x hx)) ih hL).trans (le_of_eq ?_)
      ring
  have hgeo : Summable fun k : ℕ => θ ^ k * B :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_right B
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  refine ⟨fun L x => (a : ℂ)⁻¹ * ∑' k, G k L x, ⟨fun L hL => ?_, fun L hL x hx b hb => ?_,
    fun γ hγ L hL x hx => ?_, ‖(a : ℂ)⁻¹‖ * ∑' k : ℕ, θ ^ k * B, fun L hL x hx => ?_⟩,
    fun L hL x hx => ?_⟩
  · exact (diffOn_tsum (isOpen_frames X) (fac_cont X la) (fun k => (hGf k).hol L hL) hgeo
      (fun k => by positivity) fun k x hx => hGb k x hx L hL).const_mul _
  · rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    exact tsum_congr fun k => (hGf k).bor L hL x hx b hb
  · rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹)]
    congr 1
    exact tsum_congr fun k => (hGf k).aut γ hγ L hL x hx
  · rw [pnorm_le_iff X la _ hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (tsum_of_norm_bounded (hgeo.hasSum.mul_right _)
      fun k => hGb k x hx L hL) (norm_nonneg _)
  · have hs : Summable fun k => G k L x :=
      Summable.of_norm_bounded (hgeo.mul_right _) fun k => hGb k x hx L hL
    have hp : Summable fun p : {L' // L' ∈ 𝓛 ∧ L' ≠ L} × ℕ =>
        (a : ℂ)⁻¹ * (C L p.1.1 * G p.2 p.1.1 x) := by
      refine Summable.mul_left _ (Summable.of_norm_bounded
        (Summable.mul_of_nonneg (hC L hL).1 (hgeo.mul_right (fac X la x)⁻¹)
          (fun _ => norm_nonneg _) fun k => mul_nonneg (by positivity) (hw x hx)) fun p => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hGb _ x hx _ p.1.2.1) (norm_nonneg _)
    have hcomm := Summable.tsum_comm (f := fun (L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}) (k : ℕ) =>
      (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x)) hp
    have hterm : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ∑' k, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x) := by
      intro L'
      rw [tsum_mul_left, tsum_mul_left]; ring
    have hk : ∀ k, ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        -G (k + 1) L x := by
      intro k
      rw [tsum_mul_left, hGs, op]; ring
    have hsum : HasSum (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x)) (-∑' k, G (k + 1) L x) := by
      have h := hp.prod.hasSum
      simp only at h
      rw [← hcomm] at h
      simp only [hterm, hk, tsum_neg] at h
      exact h
    have hall : ∀ s : Set (Lt E r), s = {L} ∪ {L' | L' ∈ 𝓛 ∧ L' ≠ L} →
        HasSum (fun L' : s => C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x))
          (C L L * ((a : ℂ)⁻¹ * ∑' k, G k L x) + -∑' k, G (k + 1) L x) := by
      rintro s rfl
      exact HasSum.add_disjoint (f := fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x))
        (by simp) (hasSum_singleton L fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x)) hsum
    rw [(hall 𝓛 ?_).tsum_eq, (hC₀ L hL).1, mul_inv_cancel_left₀ hac, hs.tsum_eq_zero_add, hG0]
    · ring
    · ext L'
      by_cases h : L' = L <;> simp [h, hL]

end GlobalTheory.SW.Neumann
