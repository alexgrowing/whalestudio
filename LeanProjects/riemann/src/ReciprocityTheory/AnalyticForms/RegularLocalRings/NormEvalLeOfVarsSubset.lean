import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem norm_eval_le_of_vars_subset {n : ℕ} (F : MvPolynomial (Fin n) ℂ) (S : Finset (Fin n))
    (hS : F.vars ⊆ S) (y : Fin n → ℂ) (hy : ∀ i ∈ S, ‖y i‖ ≤ 1) :
    ‖eval y F‖ ≤ ∑ m ∈ F.support, ‖F.coeff m‖ := by
  rw [MvPolynomial.eval_eq']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  have h1 : ‖∏ i, y i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow]
    by_cases h : m i = 0
    · simp [h]
    · refine pow_le_one₀ (norm_nonneg _) (hy i (hS ?_))
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨m, hm, Finsupp.mem_support_iff.mpr h⟩
  calc ‖F.coeff m‖ * ‖∏ i, y i ^ m i‖ ≤ ‖F.coeff m‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖F.coeff m‖ := mul_one _

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

def cptPiece (c : w.Idx) : Set w.M :=
  {x | x ∈ w.src c ∧ (∀ q, ‖w.coord c x (w.yq c.1 c.2 q)‖ ≤ 1) ∧
    ∀ k, ‖w.coord c x (w.yt c.1 c.2 k)‖ ≤ 1}

theorem isCompact_cptPiece (c : w.Idx) : IsCompact (w.cptPiece c) := by
  let S : Finset (Fin (w.pres c.1 c.2).n) :=
    Finset.univ.image (w.yq c.1 c.2) ∪ Finset.univ.image (w.yt c.1 c.2)
  choose F hFv hFK using w.gen c.1 c.2
  let B : Set (Fin (w.pres c.1 c.2).n → ℂ) :=
    (⋂ h ∈ ((w.pres c.1 c.2).K : Set (MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)), {y | eval y h = 0}) ∩
      ((⋂ q, {y | ‖y (w.yq c.1 c.2 q)‖ ≤ 1}) ∩ ⋂ k, {y | ‖y (w.yt c.1 c.2 k)‖ ≤ 1})
  have hBc : IsClosed B :=
    (isClosed_biInter fun h _ => isClosed_eq (MvPolynomial.continuous_eval h) continuous_const).inter
      ((isClosed_iInter fun q =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const).inter
      (isClosed_iInter fun k =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const))
  have hmemB : ∀ y, y ∈ B ↔ (∀ h ∈ (w.pres c.1 c.2).K, eval y h = 0) ∧
      (∀ q, ‖y (w.yq c.1 c.2 q)‖ ≤ 1) ∧ ∀ k, ‖y (w.yt c.1 c.2 k)‖ ≤ 1 := by
    intro y
    simp only [B, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
  have hS : ∀ y ∈ B, ∀ i ∈ S, ‖y i‖ ≤ 1 := by
    intro y hy i hi
    rw [hmemB] at hy
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.1 a
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.2 a
  have hBsub : B ⊆ Set.univ.pi fun l =>
      Metric.closedBall (0 : ℂ) (∑ m ∈ (F l).support, ‖(F l).coeff m‖) := by
    intro y hy
    have hy' := (hmemB y).mp hy
    refine Set.mem_univ_pi.mpr fun l => ?_
    rw [mem_closedBall_zero_iff]
    have h1 : y l = eval y (F l) := by
      have h2 := hy'.1 _ (hFK l)
      rw [map_sub, eval_X, sub_eq_zero] at h2
      exact h2
    rw [h1]
    exact norm_eval_le_of_vars_subset (F l) S (hFv l) y (hS y hy)
  have hBk : IsCompact B :=
    (isCompact_univ_pi fun l => isCompact_closedBall _ _).of_isClosed_subset hBc hBsub
  have hrange : B ⊆ Set.range (fun y : w.src c => w.coord c y) := by
    intro y hy
    have h3 : y ∈ w.coord c '' w.src c := by
      rw [w.image c]
      exact ((hmemB y).mp hy).1
    obtain ⟨x, hx, rfl⟩ := h3
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpre := (w.isEmbedding c).isInducing.isCompact_preimage' hBk hrange
  have heq : w.cptPiece c = Subtype.val '' ((fun y : w.src c => w.coord c y) ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨hx, hq, ht⟩
      refine ⟨⟨x, hx⟩, (hmemB _).mpr ⟨?_, hq, ht⟩, rfl⟩
      have h4 : w.coord c x ∈ w.coord c '' w.src c := ⟨x, hx, rfl⟩
      rw [w.image c] at h4
      exact h4
    · rintro ⟨y, hy, rfl⟩
      have hy' := (hmemB _).mp hy
      exact ⟨y.2, hy'.2.1, hy'.2.2⟩
  rw [heq]
  exact hpre.image continuous_subtype_val

theorem exists_cptPiece (x : w.M) : ∃ c, x ∈ w.cptPiece c := by
  obtain ⟨c0, h0⟩ := w.cover x
  have hz := w.lift_mem c0 x h0
  obtain ⟨p, hpnz, hpmax⟩ := exists_chart (fun q => eval (w.coord c0 x) (w.lift c0 q)) hz.1
  have hπ : w.π.base x.1 ∈ (chartOpen hP p).1 := (w.mem_chartOpen_iff c0 x h0 p).mpr hpnz
  have hxp : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hπ
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxp
  have hcl : IsClosed ({x.1} : Set w.W) := x.2
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (w.m p) → ℂ, ∀ k, τ k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi :=
    ⟨_, fun _ => rfl⟩
  have hτi : τ i = 1 := by
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hi hcl
    rw [hτ, w.t_self, ← hφ, map_one]
  have : Nonempty (Fin (w.m p)) := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun k => ‖τ k‖
  have hτj1 : 1 ≤ ‖τ j‖ := by
    have h5 := hj i
    rwa [hτi, norm_one] at h5
  have hpos : 0 < ‖τ j‖ := lt_of_lt_of_le one_pos hτj1
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [w.inter p i j]
    refine (w.W.evaluation_ne_zero_iff_mem_basicOpen x.1 hi (w.t p i j)).mp ?_
    rw [Ne, ← val_eq_zero_iff (w.π ≫ toSpecC hP) _ x.1 hi hcl, ← hτ]
    exact norm_pos_iff.mp hpos
  have hjV : x.1 ∈ (w.pres p j).V := hij.2
  have hcoc : ∀ k, val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV * τ j = τ k := by
    intro k
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hij hcl
    have h6 := congrArg φ (w.t_cocycle p i j k)
    rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h6
    rw [hτ, hτ]
    exact h6
  refine ⟨⟨p, j⟩, hjV, fun q => ?_, fun k => ?_⟩
  · have e1 : w.coord ⟨p, j⟩ x (w.yq p j q) =
        val (w.π ≫ toSpecC hP) ((w.pres p j).secHom (X (w.yq p j q))) x.1 hjV := by
      rw [(w.pres p j).val_secHom x.1 hjV hcl, eval_X, w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1, w.sec_yq,
      (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres p j) (chartCoord hP p q)
        x.1 hjV hcl).2]
    refine (congrArg (fun v => ‖v‖) (w.val_chartCoord c0 x h0 p _ q)).trans_le ?_
    simp only [affCoord, norm_div]
    exact div_le_one_of_le₀ (hpmax q.1 q.2) (norm_nonneg _)
  · have e1 : w.coord ⟨p, j⟩ x (w.yt p j k) = val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV := by
      rw [← w.sec_yt p j k, (w.pres p j).val_secHom x.1 hjV hcl, eval_X,
        w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1]
    have h7 : ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ * ‖τ j‖ = ‖τ k‖ := by
      rw [← norm_mul, hcoc k]
    calc ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ = ‖τ k‖ / ‖τ j‖ := by
          rw [← h7, mul_div_cancel_right₀ _ hpos.ne']
      _ ≤ 1 := div_le_one_of_le₀ (hj k) hpos.le

end WData

theorem WData.compactSpace (w : WData P D hP) : CompactSpace w.M := by
  refine isCompact_univ_iff.mp ?_
  have h : (Set.univ : Set w.M) = ⋃ c, w.cptPiece c := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact w.exists_cptPiece x
  rw [h]
  exact isCompact_iUnion fun c => w.isCompact_cptPiece c

end

end ReciprocityTheory.AnForm.R
