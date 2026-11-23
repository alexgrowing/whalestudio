import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitB

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem act_add' {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE, actE_add_right]

variable [IsCMField E]

private theorem exists_integer_complexConj (β : 𝓞 E) : ∃ β' : 𝓞 E, (β' : E) = IsCMField.complexConj E (β : E) :=
  ⟨⟨IsCMField.complexConj E (β : E), (mem_integralClosure_iff ℤ E).mpr
    ((NumberField.RingOfIntegers.isIntegral_coe β).map
      (RingHom.toIntAlgHom (IsCMField.complexConj E).toRingEquiv.toRingHom))⟩, rfl⟩

theorem greedy_step (X : PT E) {n : ℕ} (ω : Fin n → 𝓞 E) {Ω th : ℝ} (hΩ : 0 < Ω) (hth : 0 < th)
    (hΩth : Ω * th ^ 2 ≤ 1) (hω : ∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ Ω)
    (hsp : ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)))
    {I : Submodule ℤ (Vsp X.dim)} (hI : Good X (1 / (Ω * th)) I) {x : Vsp X.dim} (hx : x ∈ X.L)
    (hxI : x ∉ I) (hd : Metric.infDist x (IR I) < th) :
    ∃ J, Good X (1 / (Ω * th)) J ∧ Module.finrank ℝ (IR I) < Module.finrank ℝ (IR J) := by
  have hΩθ : 0 < Ω * th := mul_pos hΩ hth
  obtain ⟨p, hp, hxp⟩ := (Metric.infDist_lt_iff ⟨0, (IR I).zero_mem⟩).mp hd
  have hp' : p ∈ IR I := hp
  set r := x - p with hr
  have hrn : ‖r‖ < th := by
    rw [hr, ← dist_eq_norm]
    exact hxp
  have hxpr : x = p + r := by
    rw [hr]
    abel
  have hxIR : ∀ a ∈ IR I, (Hf x a).im = 0 := by
    obtain ⟨ux, hux⟩ := exists_isU I x
    have hux0 : ux = 0 := by
      by_contra hne
      have h1 := hI.sep x hx ux hux hne
      have h2 := hux.norm_sq
      have h3 : (Hf x ux).im = (Hf r ux).im := by
        rw [hxpr, Hf_im_add_left, hI.IR_iso p hp' ux hux.1, zero_add]
      have h4 := abs_Hf_im_le r ux
      have hpos : 0 < ‖ux‖ := norm_pos_iff.mpr hne
      have h5 : ‖ux‖ ^ 2 ≤ ‖r‖ * ‖ux‖ := by
        rw [h2, h3]
        exact le_trans (le_abs_self _) h4
      have h6 : ‖ux‖ < th := by nlinarith
      have h7 : 1 / (Ω * th) < th := lt_trans h1 h6
      rw [div_lt_iff₀ hΩθ] at h7
      nlinarith
    exact Hf_im_span_right (I : Set (Vsp X.dim)) x (hux.eq_zero_iff.mp hux0)
  have hrIR : ∀ a ∈ IR I, (Hf r a).im = 0 := by
    intro a ha
    have h := hxIR a ha
    rw [hxpr, Hf_im_add_left, hI.IR_iso p hp' a ha, zero_add] at h
    exact h
  have hact : ∀ (α : 𝓞 E) v, v ∈ IR I → act α v ∈ IR I := fun α v hv => hI.IR_stable α v hv
  have hC : ∀ j, (Hf x (act (ω j) x)).im = 0 := by
    intro j
    apply im_eq_zero_of_lt X hx (X.stable (ω j) x hx)
    obtain ⟨β', hβ'⟩ := exists_integer_complexConj (ω j)
    have e1 : (Hf p (act (ω j) p)).im = 0 := hI.IR_iso p hp' _ (hact _ p hp')
    have e2 : (Hf r (act (ω j) p)).im = 0 := hrIR _ (hact _ p hp')
    have e3 : (Hf p (act (ω j) r)).im = 0 := by
      rw [act_eq_actE, Hf_actE', ← hβ', ← act_eq_actE, Hf_im_antisymm, hrIR _ (hact β' p hp'), neg_zero]
    have e4 : |(Hf r (act (ω j) r)).im| < 1 := by
      have h1 := abs_Hf_im_le r (act (ω j) r)
      have h2 : ‖act (ω j) r‖ ≤ Ω * ‖r‖ := by
        rw [act_eq_actE]
        exact norm_actE_le _ Ω hΩ.le (hω j) r
      have h3 : ‖r‖ * ‖act (ω j) r‖ ≤ Ω * ‖r‖ ^ 2 := by nlinarith [norm_nonneg r]
      have h4 : ‖r‖ ^ 2 < th ^ 2 := by nlinarith [norm_nonneg r]
      have h5 : Ω * ‖r‖ ^ 2 < 1 := by nlinarith
      linarith
    rw [hxpr, act_add', Hf_im_add_left, Hf_im_add_right, Hf_im_add_right, e1, e2, e3]
    simpa using e4
  have hD : ∀ γ : 𝓞 E, (Hf x (act γ x)).im = 0 := by
    intro γ
    rw [act_eq_actE]
    refine Hf_im_span_right _ x ?_ _ (actE_mem_span_omega (fun j => (ω j : E)) (hsp γ) x)
    rintro _ ⟨j, rfl⟩
    show (Hf x (actE (ω j : E) x)).im = 0
    rw [← act_eq_actE]
    exact hC j
  set S : Set (Vsp X.dim) := (I : Set (Vsp X.dim)) ∪ Set.range (fun α : 𝓞 E => act α x) with hS
  set W : Submodule ℝ (Vsp X.dim) := Submodule.span ℝ S with hW
  set J : Submodule ℤ (Vsp X.dim) := X.L ⊓ W.restrictScalars ℤ with hJ
  have hSL : ∀ v ∈ S, v ∈ X.L := by
    rintro v (hv | ⟨α, rfl⟩)
    · exact hI.le hv
    · exact X.stable α x hx
  have hSJ : S ⊆ J := fun v hv => Submodule.mem_inf.mpr ⟨hSL v hv, Submodule.subset_span hv⟩
  have hIRJ : IR J = W := by
    apply le_antisymm
    · exact Submodule.span_le.mpr fun v hv => (Submodule.mem_inf.mp hv).2
    · exact Submodule.span_le.mpr fun v hv => Submodule.subset_span (hSJ hv)
  have hIJ : IR I ≤ W := Submodule.span_mono Set.subset_union_left
  refine ⟨J, ⟨inf_le_left, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy hyJ
    rw [hIRJ] at hyJ
    exact Submodule.mem_inf.mpr ⟨hy, hyJ⟩
  · intro α y hy
    obtain ⟨hyL, hyW⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨X.stable α y hyL, ?_⟩
    show act α y ∈ W
    rw [act_eq_actE]
    refine actE_mem_of_span (α : E) S W ?_ y hyW
    rintro v (hv | ⟨β, rfl⟩)
    · rw [← act_eq_actE]
      exact Submodule.subset_span (Or.inl (hI.stable α v hv))
    · show actE (α : E) (act β x) ∈ W
      rw [← act_eq_actE, ← act_mul']
      exact Submodule.subset_span (Or.inr ⟨α * β, rfl⟩)
  · have hSiso : ∀ v ∈ S, ∀ w ∈ S, (Hf v w).im = 0 := by
      rintro v (hv | ⟨β, rfl⟩) w (hw | ⟨γ, rfl⟩)
      · exact hI.iso v hv w hw
      · obtain ⟨γ', hγ'⟩ := exists_integer_complexConj γ
        show (Hf v (act γ x)).im = 0
        rw [Hf_im_antisymm, act_eq_actE, Hf_actE, ← hγ', ← act_eq_actE,
          hxIR _ (mem_IR (hI.stable γ' v hv)), neg_zero]
      · obtain ⟨β', hβ'⟩ := exists_integer_complexConj β
        show (Hf (act β x) w).im = 0
        rw [act_eq_actE, Hf_actE, ← hβ', ← act_eq_actE]
        exact hxIR _ (mem_IR (hI.stable β' w hw))
      · obtain ⟨β', hβ'⟩ := exists_integer_complexConj β
        show (Hf (act β x) (act γ x)).im = 0
        rw [act_eq_actE β, Hf_actE, ← hβ', ← act_eq_actE, ← act_mul']
        exact hD (β' * γ)
    intro y hy z hz
    exact Hf_im_span_iso S hSiso y (Submodule.mem_inf.mp hy).2 z (Submodule.mem_inf.mp hz).2
  · intro y hy u hu hu0
    obtain ⟨uI, huI⟩ := exists_isU I y
    have huIR : u ∈ W := by
      rw [← hIRJ]
      exact hu.1
    have hinner : ∀ a ∈ W, inner ℝ u a = (Hf y a).im := fun a ha => hu.2 a (by rw [hIRJ]; exact ha)
    by_cases huI0 : uI = 0
    · have horth : ∀ a ∈ IR I, inner ℝ u a = 0 := by
        intro a ha
        rw [hinner a (hIJ ha), ← huI.2 a ha, huI0, inner_zero_left]
      have hex : ∃ j, (Hf y (act (ω j) x)).im ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hu0
        have hyI : ∀ a ∈ I, (Hf y a).im = 0 := huI.eq_zero_iff.mp huI0
        have hyS : ∀ w ∈ S, (Hf y w).im = 0 := by
          rintro w (hw | ⟨γ, rfl⟩)
          · exact hyI w hw
          · show (Hf y (act γ x)).im = 0
            rw [act_eq_actE]
            refine Hf_im_span_right _ y ?_ _ (actE_mem_span_omega (fun j => (ω j : E)) (hsp γ) x)
            rintro _ ⟨j, rfl⟩
            show (Hf y (actE (ω j : E) x)).im = 0
            rw [← act_eq_actE]
            exact hall j
        have h1 := Hf_im_span_right S y hyS u huIR
        have h2 := hinner u huIR
        rw [h1, real_inner_self_eq_norm_sq] at h2
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
      obtain ⟨j, hj⟩ := hex
      have h1 := one_le_abs_im X hy (X.stable (ω j) x hx) hj
      have h2 : (Hf y (act (ω j) x)).im = inner ℝ u (act (ω j) r) := by
        have hmem : act (ω j) x ∈ W := Submodule.subset_span (Or.inr ⟨ω j, rfl⟩)
        rw [← hinner _ hmem, hxpr, act_add', inner_add_right,
          horth _ (hact _ p hp'), zero_add]
      have h3 : |inner ℝ u (act (ω j) r)| ≤ ‖u‖ * (Ω * ‖r‖) := by
        refine le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg u))
        rw [act_eq_actE]
        exact norm_actE_le _ Ω hΩ.le (hω j) r
      rw [h2] at h1
      have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have h4 : ‖u‖ * (Ω * ‖r‖) < ‖u‖ * (Ω * th) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hrn hΩ) hu_pos
      rw [div_lt_iff₀ hΩθ]
      linarith
    · have h1 := hI.sep y hy uI huI huI0
      have h2 : ‖uI‖ ^ 2 = inner ℝ u uI := by
        rw [hinner uI (hIJ huI.1), ← huI.2 uI huI.1, real_inner_self_eq_norm_sq]
      have h3 : inner ℝ u uI ≤ ‖u‖ * ‖uI‖ := real_inner_le_norm u uI
      have hpos : 0 < ‖uI‖ := norm_pos_iff.mpr huI0
      have h4 : ‖uI‖ ≤ ‖u‖ := by nlinarith
      linarith
  · apply Submodule.finrank_lt_finrank_of_lt
    rw [hIRJ]
    refine lt_of_le_of_ne hIJ ?_
    intro heq
    have hxW : x ∈ W := Submodule.subset_span (Or.inr ⟨1, act_one' x⟩)
    rw [← heq] at hxW
    exact hxI (hI.sat x hx hxW)

theorem exists_maximal (X : PT E) {n : ℕ} (ω : Fin n → 𝓞 E) {Ω th : ℝ} (hΩ : 0 < Ω)
    (hth : 0 < th) (hΩth : Ω * th ^ 2 ≤ 1) (hω : ∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ Ω)
    (hsp : ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) :
    ∃ I, Good X (1 / (Ω * th)) I ∧ ∀ x ∈ X.L, x ∉ I → th ≤ Metric.infDist x (IR I) := by
  have key : ∀ k : ℕ, ∀ I : Submodule ℤ (Vsp X.dim), Good X (1 / (Ω * th)) I →
      Module.finrank ℝ (Vsp X.dim) - Module.finrank ℝ (IR I) ≤ k →
      ∃ J, Good X (1 / (Ω * th)) J ∧ ∀ x ∈ X.L, x ∉ J → th ≤ Metric.infDist x (IR J) := by
    intro k
    induction k with
    | zero =>
      intro I hI hk
      refine ⟨I, hI, fun x hx hxI => ?_⟩
      by_contra hlt
      push Not at hlt
      obtain ⟨J, -, hJ⟩ := greedy_step X ω hΩ hth hΩth hω hsp hI hx hxI hlt
      have := Submodule.finrank_le (IR J)
      omega
    | succ k ih =>
      intro I hI hk
      by_cases h : ∀ x ∈ X.L, x ∉ I → th ≤ Metric.infDist x (IR I)
      · exact ⟨I, hI, h⟩
      · push Not at h
        obtain ⟨x, hx, hxI, hlt⟩ := h
        obtain ⟨J, hJ, hJr⟩ := greedy_step X ω hΩ hth hΩth hω hsp hI hx hxI hlt
        have := Submodule.finrank_le (IR J)
        exact ih J hJ (by omega)
  exact key _ ⊥ (Good.bot X _) (Nat.sub_le _ _)

end

end ReciprocityTheory.ChartRestriction.G.I2
