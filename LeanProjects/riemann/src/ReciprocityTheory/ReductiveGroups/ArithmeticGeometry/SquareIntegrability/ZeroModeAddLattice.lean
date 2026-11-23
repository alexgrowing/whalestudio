import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddRealSpan

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

private theorem Hf_im_eq_zero_of_mem_IR_of_isSplit (hI : IsSplit P I) {x y : Vsp X.dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  have hadd : ∀ a b c : Vsp X.dim, (Hf (a + b) c).im = (Hf a c).im + (Hf b c).im := by
    intro a b c
    simp [Hf, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (r : ℝ) (a c : Vsp X.dim), (Hf (r • a) c).im = r * (Hf a c).im := by
    intro r a c
    simp [Hf, Finset.mul_sum, mul_assoc]
  have hzero : ∀ c : Vsp X.dim, (Hf 0 c).im = 0 := by
    intro c
    simp [Hf]
  have step1 : ∀ w ∈ I, ∀ v ∈ IR I, (Hf v w).im = 0 := by
    intro w hw v hv
    change v ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hv
    induction hv using Submodule.span_induction with
    | mem a ha => exact hI.iso a ha w hw
    | zero => exact hzero w
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  have step2 : (Hf y x).im = 0 := by
    change y ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hy
    induction hy using Submodule.span_induction with
    | mem a ha => rw [Hf_conj, Complex.conj_im, step1 a ha x hx, neg_zero]
    | zero => exact hzero x
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  rw [Hf_conj, Complex.conj_im, step2, neg_zero]

private theorem Hf_real_combination_left_im {κ : Type} [Fintype κ] (γ : Vsp X.dim) (r : κ → ℝ) (w : κ → Vsp X.dim) :
    (Hf (∑ k, r k • w k) γ).im = ∑ k, r k * (Hf (w k) γ).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem z_of_K (hI : IsSplit P I) (k : Fin (dK (IR I))) {b : Vsp X.dim} (hb : b ∈ IR I) :
    z (IR I) k b = ((inner ℝ (e (IR I) k) b : ℝ) : ℂ) := by
  have hek : e (IR I) k ∈ IR I := (ob (IR I) k).2
  apply Complex.ext
  · rw [Complex.ofReal_re]
    simp [z, Hf, real_inner_eq_re_inner, PiLp.inner_apply, Complex.mul_re, mul_comm]
  · rw [Complex.ofReal_im]
    exact Hf_im_eq_zero_of_mem_IR_of_isSplit hI hb hek

theorem sum_im_coord_mul (hI : IsSplit P I) (γ : Vsp X.dim) {b : Vsp X.dim} (hb : b ∈ IR I) :
    ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k b = ((Hf γ b).im : ℂ) := by
  have hexp : b = ∑ k, (inner ℝ (e (IR I) k) b) • e (IR I) k := by
    have h := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hR : ∑ k, (z (IR I) k γ).im * inner ℝ (e (IR I) k) b = (Hf γ b).im := by
    have h1 : (Hf γ b).im = -(Hf b γ).im := by
      rw [Hf_conj γ b, Complex.conj_im, neg_neg]
    rw [h1]
    conv_rhs => rw [hexp]
    rw [Hf_real_combination_left_im, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h2 : (Hf (e (IR I) k) γ).im = -(z (IR I) k γ).im := by
      simp only [z]
      rw [Hf_conj (e (IR I) k) γ, Complex.conj_im, neg_neg]
    rw [h2]
    ring
  simp_rw [z_of_K hI _ hb]
  exact_mod_cast hR

theorem gaugeExp_add_tb (hI : IsSplit P I) (γ v : Vsp X.dim) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) :
    gaugeExp I γ (v + tb hI t) = gaugeExp I γ v -
      2 * Real.pi * Complex.I * ∑ i, ((Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im : ℂ) * (t i : ℂ) := by
  have hmem : tb hI t ∈ IR I :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Ib hI i).2)
  have hzadd : ∀ k (x y : Vsp X.dim), z (IR I) k (x + y) = z (IR I) k x + z (IR I) k y := by
    intro k x y
    simp [z, Hf, add_mul, Finset.sum_add_distrib]
  have hcs : ∀ (r : ℝ) (x : Vsp X.dim), ((r : ℂ) • x) = r • x := by
    intro r x
    ext i
    simp [Complex.real_smul]
  have hp1 : ∀ w ∈ IR I, p1 (IR I) w = w := by
    intro w hw
    have hexp := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hexp
    simp only [p1]
    conv_rhs => rw [← hexp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [z_of_K hI k hw, hcs]
    all_goals rfl
  have hp1add : ∀ x y : Vsp X.dim, p1 (IR I) (x + y) = p1 (IR I) x + p1 (IR I) y := by
    intro x y
    simp only [p1, hzadd, add_smul, Finset.sum_add_distrib]
  have hp2 : p2 (IR I) (v + tb hI t) = p2 (IR I) v := by
    simp only [p2, hp1add, hp1 _ hmem]
    abel
  have him : (Hf γ (tb hI t)).im = ∑ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im * t i := by
    rw [Hf_conj (tb hI t) γ, Complex.conj_im]
    simp only [tb]
    rw [Hf_real_combination_left_im, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Hf_conj γ ((Ib hI i : IR I) : Vsp X.dim), Complex.conj_im]
    ring
  have hsplit : ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k (v + tb hI t) =
      ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v + ((Hf γ (tb hI t)).im : ℂ) := by
    rw [← sum_im_coord_mul hI γ hmem, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzadd, mul_add]
  unfold gaugeExp
  rw [hp2, hsplit, him]
  push_cast
  ring

theorem zmC_add (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {γ : Vsp X.dim} (hγ : γ ∈ X.L) (m : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (hm : ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i)
    (n : Fin (Module.finrank ℝ (IR I)) → ℤ) (v : Vsp X.dim) :
    zmC hI s n (v + γ) = (X.eps γ : ℂ) * Complex.exp (gaugeExp I γ v) * zmC hI s (n + m) v := by
  have hg : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      gaugeExp I γ (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) =
        gaugeExp I γ v - 2 * Real.pi * Complex.I * ∑ i, ((m i : ℤ) : ℂ) * (t i : ℂ) := by
    intro t
    have h := gaugeExp_add_tb hI γ v t
    simp only [tb] at h
    simp only [h, hm, Complex.ofReal_intCast]
  have hN : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ∑ i, (((n + m) i : ℤ) : ℂ) * (t i : ℂ) =
        ∑ i, ((n i : ℤ) : ℂ) * (t i : ℂ) + ∑ i, ((m i : ℤ) : ℂ) * (t i : ℂ) := by
    intro t
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  simp only [zmC]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  try dsimp only
  have hv : v + γ + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) =
      (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) + γ := by
    abel
  rw [hv, zmG_add hI hs hγ, hg t, hN t]
  simp only [mul_add, neg_add, Complex.exp_add, Complex.exp_neg, Complex.exp_sub]
  ring

theorem zeroMode_add_lattice (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {x : Vsp X.dim} (hx : x ∈ Col.Ip X I) (v : Vsp X.dim) :
    zmC hI s 0 (v + x) = (X.eps x : ℂ) *
      Complex.exp (Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) + Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2) *
        zmC hI s 0 v := by
  have hx' : x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := hx
  have hadd : ∀ a b c : Vsp X.dim, (Hf (a + b) c).im = (Hf a c).im + (Hf b c).im := by
    intro a b c
    simp [Hf, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (r : ℝ) (a c : Vsp X.dim), (Hf (r • a) c).im = r * (Hf a c).im := by
    intro r a c
    simp [Hf, Finset.mul_sum, mul_assoc]
  have hzero : ∀ c : Vsp X.dim, (Hf 0 c).im = 0 := by
    intro c
    simp [Hf]
  have hIm : ∀ a ∈ IR I, (Hf a x).im = 0 := by
    intro a ha
    change a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha
    induction ha using Submodule.span_induction with
    | mem b hb => rw [Hf_conj x b, Complex.conj_im, hx'.2 b hb, neg_zero]
    | zero => exact hzero x
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  have hzx : ∀ k, (z (IR I) k x).im = 0 := by
    intro k
    have hek : e (IR I) k ∈ IR I := (ob (IR I) k).2
    simp only [z]
    rw [Hf_conj (e (IR I) k) x, Complex.conj_im, hIm _ hek, neg_zero]
  have hg : ∀ w, gaugeExp I x w =
      Real.pi * Hf (p2 (IR I) w) (p2 (IR I) x) + Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2 := by
    intro w
    unfold gaugeExp
    simp only [hzx, Complex.ofReal_zero, zero_mul, mul_zero, Finset.sum_const_zero, neg_zero,
      zero_sub, sub_zero, zero_add]
    try ring
  have hzadd : ∀ k (a b : Vsp X.dim), z (IR I) k (a + b) = z (IR I) k a + z (IR I) k b := by
    intro k a b
    simp [z, Hf, add_mul, Finset.sum_add_distrib]
  have hcs : ∀ (r : ℝ) (a : Vsp X.dim), ((r : ℂ) • a) = r • a := by
    intro r a
    ext i
    simp [Complex.real_smul]
  have hp1 : ∀ w ∈ IR I, p1 (IR I) w = w := by
    intro w hw
    have hexp := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hexp
    simp only [p1]
    conv_rhs => rw [← hexp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [z_of_K hI k hw, hcs]
    all_goals rfl
  have hp1add : ∀ a b : Vsp X.dim, p1 (IR I) (a + b) = p1 (IR I) a + p1 (IR I) b := by
    intro a b
    simp only [p1, hzadd, add_smul, Finset.sum_add_distrib]
  have hp2 : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      p2 (IR I) (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) = p2 (IR I) v := by
    intro t
    have hmem : ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) ∈ IR I :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Ib hI i).2)
    simp only [p2, hp1add, hp1 _ hmem]
    abel
  simp only [zmC]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  try dsimp only
  have hv : v + x + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) =
      (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) + x := by
    abel
  rw [hv, zmG_add hI hs hx'.1, hg, hp2 t]
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
