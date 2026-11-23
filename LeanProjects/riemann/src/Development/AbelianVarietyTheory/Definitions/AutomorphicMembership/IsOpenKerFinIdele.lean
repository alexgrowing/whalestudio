import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped ContDiff

namespace GlobalTheory.CuspRep

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h1 : ‖(∑ k ∈ Finset.range n, z ^ k) - n‖ ≤ n / 2 := by
    have : (∑ k ∈ Finset.range n, z ^ k) - n = ∑ k ∈ Finset.range n, (z ^ k - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (h k).le).trans ?_
    simp; linarith
  have h2 : (n : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    have := norm_sub_norm_le (n : ℂ) (∑ k ∈ Finset.range n, z ^ k)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    linarith
  have h3 := h n
  rw [← geom_sum_mul, norm_mul] at h3
  rw [div_lt_iff₀ hp] at hn
  nlinarith

theorem isOpen_ker_finIdele (E : Type) [Field E] [NumberField E] (ψ : (FiniteAdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hψ : Continuous ψ) : IsOpen {u | ψ u = 1} := by
  have hV : {u | ‖((ψ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 E) E)ˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hψ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : FiniteAdeleRing (𝓞 E) E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : FiniteAdeleRing (𝓞 E) E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : FiniteAdeleRing (𝓞 E) E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  let P : Set (FiniteAdeleRing (𝓞 E) E) :=
    {c | ∃ a : FiniteAdeleRing (𝓞 E) E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ c = N • a}
  have hP : P ∈ 𝓝 0 := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN
  have hmul : ∀ x y : FiniteAdeleRing (𝓞 E) E, x - 1 ∈ P → y - 1 ∈ P → x * y - 1 ∈ P := by
    rintro x y ⟨a, ha, e⟩ ⟨b, hb, e'⟩
    refine ⟨a + b + N • (a * b), fun v => add_mem (add_mem (ha v) (hb v)) (nsmul_mem (mul_mem (ha v) (hb v)) N), ?_⟩
    rw [eq_add_of_sub_eq e, eq_add_of_sub_eq e']
    simp only [nsmul_eq_mul]; ring
  let H : Submonoid (FiniteAdeleRing (𝓞 E) E)ˣ :=
    { carrier := {u | (u : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P}
      one_mem' := ⟨by simpa using mem_of_mem_nhds hP, by simpa using mem_of_mem_nhds hP⟩
      mul_mem' := fun {x y} hx hy => ⟨hmul _ _ hx.1 hy.1, by rw [mul_inv, Units.val_mul]; exact hmul _ _ hx.2 hy.2⟩ }
  have hH : (H : Set (FiniteAdeleRing (𝓞 E) E)ˣ) ∈ 𝓝 1 := by
    refine Filter.inter_mem ?_ ?_
    · exact (Units.continuous_val.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
    · exact (Units.continuous_coe_inv.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
  have hk : ∀ u ∈ H, ψ u = 1 := by
    intro u hu
    apply Units.ext
    refine eq_one_of_pow_near fun n => ?_
    obtain ⟨⟨a, ha, e⟩, ⟨b, hb, e'⟩⟩ := pow_mem hu n
    have := hTV (a := u ^ n) (hTT ⟨?_, ?_⟩)
    · simpa using this
    · change ((u ^ n : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T1
      rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
    · change MulOpposite.op (((u ^ n)⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T2
      rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2
  exact ψ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hH hk)

variable {ι : Type} [Fintype ι]

def expU (z : ι → ℂ) : (ι → ℂ)ˣ :=
  ⟨fun i => Complex.exp (z i), fun i => Complex.exp (-z i),
    by funext i; simp [← Complex.exp_add], by funext i; simp [← Complex.exp_add]⟩

omit [Fintype ι] in

theorem expU_add (z z' : ι → ℂ) : expU (z + z') = expU z * expU z' :=
  Units.ext (funext fun i => Complex.exp_add (z i) (z' i))

omit [Fintype ι] in

theorem expU_zero : expU (0 : ι → ℂ) = 1 := Units.ext (funext fun _ => Complex.exp_zero)

omit [Fintype ι] in

theorem unit_ne_zero (u : (ι → ℂ)ˣ) (i : ι) : (u : ι → ℂ) i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrFun u.mul_inv i)

omit [Fintype ι] in

theorem expU_log (u : (ι → ℂ)ˣ) : expU (fun i => Complex.log ((u : ι → ℂ) i)) = u :=
  Units.ext (funext fun i => Complex.exp_log (unit_ne_zero u i))

omit [Fintype ι] in

theorem continuous_expU : Continuous (expU : (ι → ℂ) → (ι → ℂ)ˣ) :=
  Units.continuous_iff.2 ⟨continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i),
    continuous_pi fun i => Complex.continuous_exp.comp (continuous_apply i).neg⟩

theorem exists_lin (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ L : (ι → ℂ) →L[ℝ] ℂ, ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z) := by
  let f : C(ι → ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun z => ⟨(ψ (expU z) : ℂˣ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp continuous_expU)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, expU_zero]))
  have hF' : ∀ z, Complex.exp (F z) = (ψ (expU z) : ℂˣ) := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', expU_add, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

open Classical in

def extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (x : ι → ℂ) : ℂ := if h : IsUnit x then (ψ h.unit : ℂˣ) else 0

omit [Fintype ι] in

theorem extZero_unit (ψ : (ι → ℂ)ˣ →* ℂˣ) (u : (ι → ℂ)ˣ) : extZero ψ u = (ψ u : ℂˣ) := by
  simp [extZero]

theorem extZero_eventually {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℂ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℂ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Complex.log (x i / (u : ι → ℂ) i)) := by
  have h : ∀ᶠ x in 𝓝 (u : ι → ℂ), ∀ i, x i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually_ne (unit_ne_zero u i)
  filter_upwards [h] with x hx
  have e : x = ((u * expU fun i => Complex.log (x i / (u : ι → ℂ) i) : (ι → ℂ)ˣ) : ι → ℂ) := by
    funext i
    change x i = (u : ι → ℂ) i * Complex.exp (Complex.log (x i / (u : ι → ℂ) i))
    rw [Complex.exp_log (div_ne_zero (hx i) (unit_ne_zero u i)), mul_div_cancel₀ _ (unit_ne_zero u i)]
  conv_lhs => rw [e, extZero_unit, map_mul, Units.val_mul, hL]

theorem contDiffAt_extZero (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) (u : (ι → ℂ)ˣ) :
    ContDiffAt ℝ ∞ (extZero ψ) u := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  refine ContDiffAt.congr_of_eventuallyEq ?_ (extZero_eventually hL u)
  refine contDiffAt_const.mul (ContDiffAt.cexp (L.contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun i => ?_)))
  have h1 : ContDiffAt ℝ ∞ Complex.log ((u : ι → ℂ) i / (u : ι → ℂ) i) := by
    rw [div_self (unit_ne_zero u i)]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  exact h1.comp (f := fun x : ι → ℂ => x i / (u : ι → ℂ) i) _ ((contDiffAt_apply ℝ ℂ i _).div_const _)

theorem fderiv_extZero {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ} (hψ : Continuous ψ)
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) : fderiv ℝ (extZero ψ) 1 = L := by
  have h0 : DifferentiableAt ℝ (extZero ψ) 1 := (contDiffAt_extZero ψ hψ 1).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun z : ι → ℂ => fun i => Complex.exp (z i)) (ContinuousLinearMap.id ℝ _) 0 := by
    refine hasFDerivAt_pi'.2 fun i => ?_
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt (x := 0)).cexp
    simpa using this
  have h2 : HasFDerivAt (extZero ψ) (fderiv ℝ (extZero ψ) 1) (fun i : ι => Complex.exp ((0 : ι → ℂ) i)) := by
    have : (fun i : ι => Complex.exp ((0 : ι → ℂ) i)) = 1 := funext fun _ => Complex.exp_zero
    rw [this]; exact h0.hasFDerivAt
  have h3 := h2.comp 0 h1
  have h4 : HasFDerivAt (fun z => Complex.exp (L z)) L 0 := by
    simpa using (L.hasFDerivAt (x := 0)).cexp
  have h5 : (extZero ψ ∘ fun z : ι → ℂ => fun i => Complex.exp (z i)) = fun z => Complex.exp (L z) :=
    funext fun z => (extZero_unit ψ (expU z)).trans (hL z)
  rw [h5] at h3
  simpa using h3.unique h4

theorem exists_bound (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (u : (ι → ℂ)ˣ) (B : ℝ), 1 ≤ B → ‖(u : ι → ℂ)‖ ≤ B → ‖((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ)‖ ≤ B →
      ‖((ψ u : ℂˣ) : ℂ)‖ ≤ C * B ^ N := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖L‖
  refine ⟨Real.exp (N * Real.pi), N, (Real.exp_pos _).le, fun u B hB h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hz : ‖fun i => Complex.log ((u : ι → ℂ) i)‖ ≤ Real.pi + Real.log B := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, add_comm]
    refine add_le_add (Complex.abs_arg_le_pi _) (abs_le.2 ⟨?_, ?_⟩)
    · have e : ((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ) i = ((u : ι → ℂ) i)⁻¹ :=
        eq_inv_of_mul_eq_one_right (congrFun u.mul_inv i)
      have := Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u⁻¹ i)) ((norm_le_pi_norm _ i).trans h2)
      rw [e, norm_inv, Real.log_inv] at this
      linarith
    · exact Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u i)) ((norm_le_pi_norm _ i).trans h1)
  rw [← expU_log u, hL, Complex.norm_exp]
  have h3 : (L fun i => Complex.log ((u : ι → ℂ) i)).re ≤ N * (Real.pi + Real.log B) :=
    (Complex.re_le_norm _).trans ((L.le_opNorm _).trans (mul_le_mul hN hz (norm_nonneg _) (Nat.cast_nonneg _)))
  refine (Real.exp_le_exp.2 h3).trans_eq ?_
  rw [mul_add, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]

end GlobalTheory.CuspRep
