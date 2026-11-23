import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe

open MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisenbergL2

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def heisS (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f)

def derS (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f

theorem heisS_apply (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    heisS a L c t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)) * f (x + t • a) := by
  rw [heisS, SchwartzMap.smulLeftCLM_apply_apply (by
      rw [GlobalTheory.LinPhaseSeminorm.phase_eq]; exact GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c t),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add]

theorem derS_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    derS a L f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ) * f x := by
  have hL : Function.HasTemperateGrowth (fun x => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  rw [derS, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, smul_eq_mul]
  ring

theorem seminorm_heisS_sub_le (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (heisS a L c t f - f - (t : ℂ) • derS a L f) ≤ C * t ^ 2 := by
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : heisS a L c t f - f - (t : ℂ) • derS a L f =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [heisS, derS, ← hM, ← hP, ← hd, hX, hY, hZ, map_sub, map_sub, map_smul]
    module
  rw [e]
  have t1 : p (M X) ≤ |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by
    refine (hC3 t ht X).trans ?_
    calc C3 * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X
        ≤ |C3| * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      _ ≤ |C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| * t ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            (hC1 m t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))) (abs_nonneg _)
      _ = |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by rw [← Finset.sum_mul]; ring
  have t2 : p ((t : ℂ) • Y) ≤ |C2| * t ^ 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := hC2 t ht
    calc |t| * p Y ≤ 1 * (C2 * t ^ 2) := mul_le_mul ht h2 (apply_nonneg _ _) zero_le_one
      _ ≤ |C2| * t ^ 2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have t3 : p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) = 2 * Real.pi * p (P d) * t ^ 2 := by
    rw [map_smul_eq_mul]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_I,
      abs_of_pos Real.pi_pos, sq_abs]
    ring
  have t4 : p Z ≤ |C0| * t ^ 2 := (hC0 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have tri : p (M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z) ≤
      p (M X) + p ((t : ℂ) • Y) + p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) + p Z := by
    refine (map_add_le_add p _ _).trans (add_le_add ?_ le_rfl)
    refine (map_sub_le_add p _ _).trans (add_le_add ?_ le_rfl)
    exact map_add_le_add p _ _
  rw [t3] at tri
  nlinarith [t1, t2, t4, tri]

end Real

section L2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem toLp_heisS_sub_le (μ : Measure V) [μ.HasTemperateGrowth] (a : V) (L : V →L[ℝ] ℝ) (c : ℝ)
    (f : 𝓢(V, ℂ)) : ∃ K : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      ‖(heisS a L c t f - f - (t : ℂ) • derS a L f).toLp 2 μ‖ ≤ K * t ^ 2 := by
  obtain ⟨k, C, hC0, hC⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 2 μ
  choose K hK using fun p : ℕ × ℕ => seminorm_heisS_sub_le a L c f p.1 p.2
  refine ⟨C * ∑ p ∈ Finset.Iic (k, 0), |K p|, fun t ht => ?_⟩
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [Finset.sum_mul]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
  refine ((hK p t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t))).trans ?_
  exact Finset.single_le_sum (f := fun q => |K q| * t ^ 2) (fun _ _ => by positivity) hp

theorem norm_toLp_two (μ : Measure V) [μ.HasTemperateGrowth] (u : 𝓢(V, ℂ)) :
    ‖u.toLp 2 μ‖ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

theorem map_dHeis_of_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  intro V _ _ _ _ _ μ _ β T hT w w' hw f g hg x
  haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  let Lf : V × V → (V →L[ℝ] ℝ) := fun p => LinearMap.toContinuousLinearMap (β.flip p.2)
  have hLf : ∀ p y, Lf p y = β y p.2 := fun p y => rfl
  have hheis : ∀ (p : V × V) (F : 𝓢(V, ℂ)) (t : ℝ),
      ⇑(heisS p.1 (Lf p) (β p.1 p.2 / 2) t F) = GlobalTheory.GaussLine.heisFun β (t • p).1 (t • p).2 ⇑F := by
    intro p F t
    funext y
    rw [heisS_apply, GlobalTheory.GaussLine.heisFun_apply, hLf, Prod.smul_fst, Prod.smul_snd]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 3
    ring_nf
  have hder : ∀ (p : V × V) (F : 𝓢(V, ℂ)) y, derS p.1 (Lf p) F y = GlobalTheory.GaussLine.dHeis β p ⇑F y := by
    intro p F y
    rw [derS_apply, GlobalTheory.GaussLine.dHeis, hLf]
  have hgS : g = derS w.1 (Lf w) f := by
    ext y
    rw [hg, hder]
  set G := derS w'.1 (Lf w') (T f) with hG
  set c := β w.1 w.2 / 2
  set c' := β w'.1 w'.2 / 2
  have hHT : ∀ t : ℝ, T (heisS w.1 (Lf w) c t f) = heisS w'.1 (Lf w') c' t (T f) := fun t =>
    DFunLike.coe_injective ((hw t f _ (hheis w f t)).trans (hheis w' (T f) t).symm)
  obtain ⟨K, hK⟩ := toLp_heisS_sub_le μ w.1 (Lf w) c f
  obtain ⟨K', hK'⟩ := toLp_heisS_sub_le μ w'.1 (Lf w') c' (T f)
  set ℓ := SchwartzMap.toLpCLM ℂ ℂ 2 μ with hℓ
  have hiso : ∀ u, ‖ℓ (T u)‖ = ‖ℓ u‖ := by
    intro u
    rw [hℓ, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, norm_toLp_two, norm_toLp_two, hT]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖ℓ (T g - G)‖ ≤ (K + K') * t := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    have e1 : (t : ℂ) • (T g - G) = (heisS w'.1 (Lf w') c' t (T f) - T f - (t : ℂ) • G) -
        T (heisS w.1 (Lf w) c t f - f - (t : ℂ) • g) := by
      rw [map_sub, map_sub, map_smul, hHT, smul_sub]
      abel
    have h1 : ‖ℓ ((t : ℂ) • (T g - G))‖ = t * ‖ℓ (T g - G)‖ := by
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h2 : ‖ℓ ((t : ℂ) • (T g - G))‖ ≤ K' * t ^ 2 + K * t ^ 2 := by
      rw [e1, map_sub]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · have := hK' t hta
        rw [hℓ, SchwartzMap.toLpCLM_apply]
        exact this
      · rw [hiso, hgS, hℓ, SchwartzMap.toLpCLM_apply]
        exact hK t hta
    rw [h1] at h2
    have h3 : t * ‖ℓ (T g - G)‖ ≤ t * ((K + K') * t) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have ha : ‖ℓ (T g - G)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖ℓ (T g - G)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set a := ‖ℓ (T g - G)‖
    set M := |K + K'| + 1 with hMdef
    have hM : 0 < M := by positivity
    set t := min 1 (a / (2 * M)) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have h1 := key t ht0 (min_le_left _ _)
    have h2 : t ≤ a / (2 * M) := min_le_right _ _
    have h3 : (K + K') * t ≤ M * t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith)) ht0.le
    have h4 : M * t ≤ M * (a / (2 * M)) := mul_le_mul_of_nonneg_left h2 hM.le
    have h5 : M * (a / (2 * M)) = a / 2 := by field_simp
    linarith
  have h0 : (T g - G).toLp 2 μ = (0 : 𝓢(V, ℂ)).toLp 2 μ := by
    have := norm_eq_zero.1 ha
    rw [hℓ, SchwartzMap.toLpCLM_apply] at this
    rw [this]
    exact ((map_zero ℓ).symm.trans (SchwartzMap.toLpCLM_apply))
  have h00 : T g - G = 0 := SchwartzMap.injective_toLp 2 μ h0
  have := congrArg (fun u : 𝓢(V, ℂ) => u x) (sub_eq_zero.1 h00)
  rw [this, hG, hder]

end L2

end GlobalTheory.HeisenbergL2
