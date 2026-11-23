import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qe25.OmX :
    (m : ℕ) → Set (Fin m → ℂ) :=
    fun (m : ℕ) ↦ {x : Fin m → ℂ | ∀ (l : Fin m), x l ≠ (0 : ℂ)}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe25.Mx :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe25.Fn.{u_2} :
    ℕ → ℕ → Type u_2 → Type u_2 :=
    fun (k r : ℕ) (E : Type u_2) ↦ (Fin r → ℂ) → UpperTheory.Reformulated.B.Qe25.Mx k r → E

noncomputable def UpperTheory.Reformulated.B.Qe25.Mdim :
    ℕ → (r : ℕ) → Fin r → ℕ :=
    fun (k r : ℕ) (a : Fin r) ↦ (2 : ℕ) * (r - (↑a : ℕ)) + k + (1 : ℕ)

theorem UpperTheory.Reformulated.B.Qe25.aux5 :
    ∀ (k r : ℕ) (a : Fin r), (2 : ℕ) * r + k - (↑a : ℕ) < (2 : ℕ) * r + k + (1 : ℕ) := by
  intro k r a
  omega

noncomputable def UpperTheory.Reformulated.B.Qe25.esI :
    (k r : ℕ) → Fin r → Fin ((2 : ℕ) * r + k + (1 : ℕ)) :=
    fun (k r : ℕ) (a : Fin r) ↦
      (⟨(2 : ℕ) * r + k - (↑a : ℕ), UpperTheory.Reformulated.B.Qe25.aux5 k r a⟩ : Fin ((2 : ℕ) * r + k + (1 : ℕ)))

theorem UpperTheory.Reformulated.B.Qe25.aux7 :
    ∀ (k r : ℕ) (a : Fin r), (↑a : ℕ) < (2 : ℕ) * r + k + (1 : ℕ) := by
  intro k r a
  have := a.isLt
  omega

noncomputable def UpperTheory.Reformulated.B.Qe25.eI :
    (k r : ℕ) → Fin r → Fin ((2 : ℕ) * r + k + (1 : ℕ)) :=
    fun (k r : ℕ) (a : Fin r) ↦ (⟨(↑a : ℕ), UpperTheory.Reformulated.B.Qe25.aux7 k r a⟩ : Fin ((2 : ℕ) * r + k + (1 : ℕ)))

noncomputable def UpperTheory.Reformulated.B.Qe25.w1 :
    (k r : ℕ) → Fin r → ℂ → UpperTheory.Reformulated.B.Qe25.Mx k r :=
    fun (k r : ℕ) (l : Fin r) (c : ℂ) (p q : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if p = UpperTheory.Reformulated.B.Qe25.esI k r l ∧ q = UpperTheory.Reformulated.B.Qe25.eI k r l then c
      else
        if p = UpperTheory.Reformulated.B.Qe25.eI k r l ∧ q = UpperTheory.Reformulated.B.Qe25.esI k r l then (Star.star c)⁻¹
        else if p = q ∧ p ≠ UpperTheory.Reformulated.B.Qe25.eI k r l ∧ p ≠ UpperTheory.Reformulated.B.Qe25.esI k r l then (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qe25.wCell :
    (k r : ℕ) → Fin (r + (1 : ℕ)) → (Fin r → ℂ) → UpperTheory.Reformulated.B.Qe25.Mx k r :=
    fun (k r : ℕ) (i : Fin (r + (1 : ℕ))) (c : Fin r → ℂ) ↦
      (List.map (fun (a : Fin r) ↦ UpperTheory.Reformulated.B.Qe25.w1 k r a (c a))
          (List.filter (fun (a : Fin r) ↦ Decidable.decide ((↑a : ℕ) < (↑i : ℕ))) (List.finRange r))).prod

noncomputable def UpperTheory.Reformulated.B.Qe25.resG.{u_1} :
    {E : Type u_1} →
      [inst : NormedAddCommGroup E] →
        [NormedSpace ℂ E] → (k r : ℕ) → Fin (r + (1 : ℕ)) → (UpperTheory.Reformulated.B.Qe25.Mx k r → E) → UpperTheory.Reformulated.B.Qe25.Fn k r E :=
    fun {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + (1 : ℕ)))
        (J : UpperTheory.Reformulated.B.Qe25.Mx k r → E) (c : Fin r → ℂ) (g : UpperTheory.Reformulated.B.Qe25.Mx k r) ↦
      (↑(∏ a : Fin r, if (↑a : ℕ) < (↑i : ℕ) then ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - (1 : ℕ)) else (1 : ℝ)) : ℂ) •
        J (UpperTheory.Reformulated.B.Qe25.wCell k r i c * g)

noncomputable def UpperTheory.Reformulated.B.Qe25.gaugeF :
    ℕ → (r : ℕ) → (Fin r → ℂ) → ℂ :=
    fun (k r : ℕ) (c : Fin r → ℂ) ↦
      UpperTheory.Reformulated.B.Qe25.resG k r (Fin.last r) (fun (x : UpperTheory.Reformulated.B.Qe25.Mx k r) ↦ (1 : ℂ)) c (1 : UpperTheory.Reformulated.B.Qe25.Mx k r)

theorem UpperTheory.Reformulated.B.Qe25.algebra_smulCommClass_complex.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : (Fin m → ℂ) → E},
      f ∈
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
        g ∈
            {f : (Fin m → ℂ) → E |
              ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
          ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f + g) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧
            ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (f + g) x = (0 : E) := by
  intro m E _ _ f g hf hg
  exact ⟨hf.1.add hg.1, fun x hx ↦ by simp [hf.2 x hx, hg.2 x hx]⟩

theorem UpperTheory.Reformulated.B.Qe25.zero_contDiffOn_supported.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E],
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (0 : (Fin m → ℂ) → E) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧
        ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (0 : (Fin m → ℂ) → E) x = (0 : E) := by
  intro m E _ _
  exact ⟨contDiffOn_const, fun _ _ ↦ rfl⟩

theorem UpperTheory.Reformulated.B.Qe25.sign_action_map_comm.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] (a : ℂ) {f : (Fin m → ℂ) → E},
      f ∈
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a • f) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (a • f) x = (0 : E) := by
  intro m E _ _ a f hf
  exact ⟨hf.1.const_smul a, fun x hx ↦ by simp [hf.2 x hx]⟩

noncomputable def UpperTheory.Reformulated.B.Qe25.WSm.{u_1} :
    (m : ℕ) → (E : Type u_1) → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℂ E] → Submodule ℂ ((Fin m → ℂ) → E) :=
    fun (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] ↦
      {
        carrier :=
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)},
        add_mem' := @UpperTheory.Reformulated.B.Qe25.algebra_smulCommClass_complex m E inst inst_1, zero_mem' := UpperTheory.Reformulated.B.Qe25.zero_contDiffOn_supported m E,
        smul_mem' := UpperTheory.Reformulated.B.Qe25.sign_action_map_comm m E : Submodule ℂ ((Fin m → ℂ) → E) }

private theorem UpperTheory.Reformulated.B.Qe25.gauge_eq (k r : ℕ) (c : Fin r → ℂ) :
    UpperTheory.Reformulated.B.Qe25.gaugeF k r c =
      ((∏ a : Fin r, ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - 1) : ℝ) : ℂ) := by
  simp [UpperTheory.Reformulated.B.Qe25.gaugeF, UpperTheory.Reformulated.B.Qe25.resG]

private theorem UpperTheory.Reformulated.B.Qe25.gauge_ne (k r : ℕ) (c : Fin r → ℂ)
    (hc : c ∈ UpperTheory.Reformulated.B.Qe25.OmX r) : UpperTheory.Reformulated.B.Qe25.gaugeF k r c ≠ 0 := by
  rw [UpperTheory.Reformulated.B.Qe25.gauge_eq, Complex.ofReal_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun a _ ↦ pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))

private theorem UpperTheory.Reformulated.B.Qe25.gauge_smooth (k r : ℕ) (c : Fin r → ℂ)
    (hc : c ∈ UpperTheory.Reformulated.B.Qe25.OmX r) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (UpperTheory.Reformulated.B.Qe25.gaugeF k r) c := by
  have h : UpperTheory.Reformulated.B.Qe25.gaugeF k r = fun c ↦ Complex.ofRealCLM
      (∏ a : Fin r, ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - 1)) :=
    funext fun c ↦ UpperTheory.Reformulated.B.Qe25.gauge_eq k r c
  rw [h]
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp c (contDiffAt_prod fun a _ ↦ ?_)
  exact (ContDiffAt.norm ℝ (contDiffAt_apply ℝ ℂ a c) (hc a)).pow _

theorem UpperTheory.Reformulated.B.Qe25.loc :
    ∀ {X : Type} [inst : NormedAddCommGroup X] [inst_1 : NormedSpace ℂ X] {k r : ℕ} (Φ : (Fin r → ℂ) → X)
      (U : Set (Fin r → ℂ)) (c : Fin r → ℂ),
      IsOpen U →
        U ⊆ UpperTheory.Reformulated.B.Qe25.OmX r →
          c ∈ U →
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (c' : Fin r → ℂ) ↦ UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • Φ c') U →
              ∃ φ ∈ UpperTheory.Reformulated.B.Qe25.WSm r X,
                Φ =ᶠ[nhds c] φ ∧
                  (fun (c' : Fin r → ℂ) ↦ UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • Φ c') =ᶠ[nhds c] fun (c' : Fin r → ℂ) ↦
                    UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • φ c' := by
  intro X _ _ k r Φ U c hU hUO hc hs
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ U := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun c' ↦ (UpperTheory.Reformulated.B.Qe25.gaugeF k r c')⁻¹) U := fun x hx ↦
      ((UpperTheory.Reformulated.B.Qe25.gauge_smooth k r x (hUO hx)).inv
        (UpperTheory.Reformulated.B.Qe25.gauge_ne k r x (hUO hx))).contDiffWithinAt
    refine (h1.smul hs).congr fun x hx ↦ ?_
    simp only [Pi.smul_apply']
    rw [smul_smul, inv_mul_cancel₀ (UpperTheory.Reformulated.B.Qe25.gauge_ne k r x (hUO hx)), one_smul]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c hc
  let b : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hsupp : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball
  have heq : Φ =ᶠ[nhds c] fun x ↦ b x • Φ x := by
    filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]
  refine ⟨fun x ↦ b x • Φ x, ⟨fun x _ ↦ ?_, fun x hx ↦ ?_⟩, heq, ?_⟩
  · by_cases hxU : x ∈ U
    · exact (b.contDiff.contDiffAt.smul (hΦ.contDiffAt (hU.mem_nhds hxU))).contDiffWithinAt
    · have h0 : (b : (Fin r → ℂ) → ℝ) =ᶠ[nhds x] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hxU (hsupp h)
      have h1 : (fun x ↦ b x • Φ x) =ᶠ[nhds x] fun _ ↦ (0 : X) := by
        filter_upwards [h0] with y hy
        simp [hy]
      exact (contDiffAt_const.congr_of_eventuallyEq h1).contDiffWithinAt
  · have h0 : b x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hUO (hsupp h))
    simp [h0]
  · filter_upwards [heq] with x hx
    rw [← hx]
