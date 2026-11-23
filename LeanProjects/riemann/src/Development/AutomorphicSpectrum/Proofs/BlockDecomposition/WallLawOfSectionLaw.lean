import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

def cosMul {G : Type} [Group G] (P Γ : Subgroup G) (γ : Γ) : Cos P Γ ≃ Cos P Γ where
  toFun := Quotient.map (· * γ) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ) (y * γ)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  invFun := Quotient.map (· * γ⁻¹) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ⁻¹) (y * γ⁻¹)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]

theorem rep_mk {G : Type} [Group G] {P Γ : Subgroup G} (x : Γ) :
    ∃ δ : G, δ ∈ Γ ∧ δ ∈ P ∧ rep (Quotient.mk _ x : Cos P Γ) = δ * x := by
  have h : QuotientGroup.rightRel (P.subgroupOf Γ) (Quotient.out (Quotient.mk _ x : Cos P Γ)) x :=
    Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Γ)) x
  rw [QuotientGroup.rightRel_apply] at h
  refine ⟨((x * (Quotient.out (Quotient.mk _ x : Cos P Γ))⁻¹)⁻¹ : Γ), Subtype.property _, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp (inv_mem h))
  · simp [rep]

theorem tsum_rep_mul {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by
  rw [← Equiv.tsum_eq (cosMul P Γ ⟨γ, hγ⟩) (fun q : Cos P Γ => F (rep q * g))]
  refine tsum_congr fun q => ?_
  have hq : cosMul P Γ ⟨γ, hγ⟩ q = Quotient.mk _ (Quotient.out q * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := rep_mk (P := P) (Quotient.out q * (⟨γ, hγ⟩ : Γ))
  rw [hq, h3, mul_assoc δ, hF δ h1 h2]
  simp [rep, mul_assoc]

theorem norm_le_of_strip {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb h1 h2
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have := hB w hw.1.le hw.2.le
  simpa using this

theorem entire_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {f g : ℂ → X}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (R : ℝ) (h : ∀ z : ℂ, R < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  refine hfa.eq_of_eventuallyEq hga (z₀ := ((R + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {z : ℂ | R < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | R < z.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with z hz using h z hz

theorem bound_left {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hB hq]

theorem bound_right {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    B * q * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hA hp]

section Sec

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem sec_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have e := h w hw (δ * p) (mul_mem h2 hp) ⟨k, hk⟩
  have e' := h w hw p hp ⟨k, hk⟩
  simp only at e e'
  rw [← mul_assoc, e, e', hP.ch.mul δ h2 p hp, hP.ch.rat δ h1 h2, one_mul]

theorem sec_right (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) (x : G) (k : K) :
    sec K P c ρ (x * k) w = ρ k⁻¹ (sec K P c ρ x w) := by
  obtain ⟨p, hp, k', hk', rfl⟩ := hP.iwa x
  have e := h w hw p hp (⟨k', hk'⟩ * k)
  have e' := h w hw p hp ⟨k', hk'⟩
  simp only at e'
  have e2 : p * k' * (k : G) = p * (((⟨k', hk'⟩ : K) * k : K) : G) := by simp [mul_assoc]
  rw [e2, e, e', map_smul, mul_inv_rev, map_mul]
  rfl

theorem eis_mul_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by
  unfold eis
  refine tsum_rep_mul (fun x => Complex.exp (z * η x) • sec K P c ρ x w) ?_ hγ g
  intro δ h1 h2 x
  simp only [sec_left hP h hw h1 h2 x, hη.left δ h2 x, hη.rat δ h1 h2, zero_add]

theorem norm_term_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by
  rw [norm_smul, Complex.norm_exp, hΛ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x w) (Real.exp_pos _).le

theorem summable_term [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w :=
  Summable.of_norm_bounded ((hl g).mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem norm_eis_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    ‖eis Γ K P c ρ Λ g w‖ ≤ M * ‖w‖ * pos Γ P l g :=
  tsum_of_norm_bounded ((hl g).hasSum.mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem pos_nonneg (l : G → ℝ) (g : G) : 0 ≤ pos Γ P l g :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem eis_mul_right [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by
  have hs := summable_term (Γ := Γ) (l := fun g => z.re * η g) (Λ := fun x => z * η x) hb hc
    (by intro x; simp) g w
  unfold eis
  rw [(ρ k⁻¹).map_tsum hs]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc]
  beta_reduce
  rw [hη.right _ k k.2, sec_right hP h hw, map_smul]

end Sec

theorem wallLaw_of_secLaw : SecLaw → WallLaw := by
  intro hS
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P P' c η η' β L R D Op H hP hP' hη hη' hβ hW
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨h1, -, Ms, hb⟩ := hS G W K ρ hK hρ Γ P c hP
  obtain ⟨-, -, Ms', hb'⟩ := hS G W K ρ hK hρ Γ P' c hP'
  have hdiff : ∀ (g : G) (w : L), Differentiable ℂ fun z => H z g w := fun g w =>
    (hW.hol g).clm_apply (differentiable_const _)
  refine ⟨?_, ?_, ?_⟩
  · intro z γ hγ g
    refine ContinuousLinearMap.ext fun w => ?_
    have e : (fun z => H z (γ * g) w) = fun z => H z g w := by
      refine entire_eq (hdiff _ w) (hdiff _ w) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_left hP h1 hη (hW.le w.2) z hγ g]
    exact congrFun e z
  · intro z g k w
    have e : (fun z => H z (g * k) w) = fun z => ρ k⁻¹ (H z g w) := by
      refine entire_eq (hdiff _ w) ((ρ k⁻¹).differentiable.comp (hdiff g w)) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_right hP h1 hb hη (hW.le w.2) z (hW.convR _ hz) g k, map_smul]
    exact congrFun e z
  · intro a b ha hb₀
    obtain ⟨MD, hD⟩ := hW.dEnt.2 a a
    obtain ⟨MO, hO⟩ := hW.op.2 b b hb₀
    refine ⟨|MD| * |Ms| + |Ms'| * |MO|, ?_⟩
    intro z hz1 hz2 g
    have hab : b < a := by linarith [hW.pos]
    obtain ⟨U, hU, B, hB⟩ := hW.bdd b a g
    have hg : g ∈ U := mem_of_mem_nhds hU
    have hp := pos_nonneg (Γ := Γ) (P := P) (fun x => a * η x) g
    have hq := pos_nonneg (Γ := Γ) (P := P') (fun x => β x - b * η' x) g
    have hA : 0 ≤ |MD| * |Ms| := by positivity
    have hB' : 0 ≤ |Ms'| * |MO| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_strip (f := fun z => H z g w) (B := B * ‖w‖) (hdiff g w) hab ?_ ?_ ?_ hz1 hz2
    · intro u hu1 hu2
      exact ((H u g).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB u hu1 hu2 g hg) (norm_nonneg _))
    · intro u hu
      have hO' := hO u hu.ge hu.le
      have hu' : u.re < -R := by rw [hu]; exact hb₀
      have e2 := norm_eis_le (Γ := Γ) hb' (l := fun x => β x - b * η' x) (hW.convL b hb₀)
        (Λ := fun x => (β x : ℂ) - u * η' x) (by intro x; simp [hu]) g (Op u w : W)
      have e3 : ‖(Op u w : W)‖ ≤ |MO| * ‖w‖ := by
        have : ‖(Op u w : W)‖ = ‖Op u w‖ := rfl
        rw [this]
        exact ((Op u).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hO'.trans (le_abs_self _)) (norm_nonneg _))
      show ‖H u g w‖ ≤ _
      rw [hW.eqL u hu' g w]
      calc _ ≤ Ms' * ‖(Op u w : W)‖ * _ := e2
        _ ≤ |Ms'| * (|MO| * ‖w‖) * _ := by
            refine mul_le_mul_of_nonneg_right ?_ hq
            exact mul_le_mul (le_abs_self _) e3 (norm_nonneg _) (abs_nonneg _)
        _ = |Ms'| * |MO| * _ * ‖w‖ := by ring
        _ ≤ _ := bound_right hA hB' hp hq (norm_nonneg _)
    · intro u hu
      have hD' := hD u hu.ge hu.le
      have hu' : R < u.re := by rw [hu]; exact ha
      have e2 := norm_eis_le (Γ := Γ) hb (l := fun x => a * η x) (hW.convR a ha)
        (Λ := fun x => u * η x) (by intro x; simp [hu]) g (w : W)
      show ‖H u g w‖ ≤ _
      rw [hW.eqR u hu' g w, norm_smul]
      calc _ ≤ |MD| * (|Ms| * ‖w‖ * _) := by
            refine mul_le_mul (hD'.trans (le_abs_self _)) (e2.trans ?_) (norm_nonneg _) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ hp
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = |MD| * |Ms| * _ * ‖w‖ := by
            have : ‖w‖ = ‖(w : W)‖ := rfl
            ring
        _ ≤ _ := bound_left hA hB' hp hq (norm_nonneg _)

end GlobalTheory.CompanionTheory.RgEis
