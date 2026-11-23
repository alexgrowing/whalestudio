import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLeStatement

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.HeisDer

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasDerivAt_of_bound (γ : ℝ → 𝓢(V, ℂ)) (b v : 𝓢(V, ℂ))
    (h : ∀ k n : ℕ, ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (γ t - b - (t : ℂ) • v) ≤ C * t ^ 2)
    (T : 𝓢(V, ℂ) →L[ℂ] ℂ) : HasDerivAt (fun t => T (γ t)) (T v) 0 := by
  have h0 : γ 0 = b := by
    obtain ⟨C, hC⟩ := h 0 0
    have h1 := hC 0 (by simp)
    simp only [Complex.ofReal_zero, zero_smul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero] at h1
    ext x
    have hx := SchwartzMap.norm_le_seminorm ℂ (γ 0 - b) x
    have h2 : ‖(γ 0 - b) x‖ = 0 := le_antisymm (hx.trans h1) (norm_nonneg _)
    rw [norm_eq_zero, SchwartzMap.sub_apply, sub_eq_zero] at h2
    exact h2
  subst h0
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  choose K hK using fun p : ℕ × ℕ => h p.1 p.2
  have hb : ∀ t : ℝ, |t| ≤ 1 → ‖T (γ t - γ 0 - (t : ℂ) • v)‖ ≤ (C * ∑ p ∈ s, |K p|) * t ^ 2 := by
    intro t ht
    have h1 := hC (γ t - γ 0 - (t : ℂ) • v)
    simp only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ C.2
    rw [Finset.sum_mul]
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
    refine ((hK p t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t))).trans ?_
    exact Finset.single_le_sum (f := fun q => |K q| * t ^ 2) (fun _ _ => by positivity) hp
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun t : ℝ => T (γ t) - T (γ 0) - (t - 0) • T v) =O[nhds 0] (fun t : ℝ => t ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (C * ∑ p ∈ s, |K p|) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have ht' : |t| ≤ 1 := by simpa [Real.dist_eq] using ht
    have e : T (γ t) - T (γ 0) - (t - 0) • T v = T (γ t - γ 0 - (t : ℂ) • v) := by
      rw [map_sub, map_sub, map_smul, sub_zero, Complex.real_smul, smul_eq_mul]
    rw [e, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    exact hb t ht'
  refine hO.trans_isLittleO ?_
  have := Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)
  simpa [sub_zero] using this

theorem hasDerivAt_heis (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => T (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
        (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f)))
      (T (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
        (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f)) 0 := by
  refine hasDerivAt_of_bound _ f _ (fun k n => ?_) T
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.schwartz_seminorm_smulLeft_linear_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : M (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f) - f - (t : ℂ) • (d - (2 * Real.pi * Complex.I) • P f) =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [hX, hY, hZ, map_sub, map_sub, map_smul]
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

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def trL (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem trL_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trL c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

variable (F) in

def evH : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evH_apply (a : AF F) : evH F a = evI F a := rfl

theorem evH_realAd (t : ℝ) : evH F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem realAd_snd (t : ℝ) : (realAd F t).2 = 0 := rfl

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c t : ℝ) :
    Function.HasTemperateGrowth (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) := by
  have e1 : (fun x : V => -(t * L x + t ^ 2 * c)) = ⇑(-(t • L)) + fun _ => -(t ^ 2 * c) := by
    funext x
    simp only [Pi.add_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h1 : Function.HasTemperateGrowth fun x : V => -(t * L x + t ^ 2 * c) := by
    rw [e1]
    exact (-(t • L)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
  have e2 : (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) =
      (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘ fun x : V => -(t * L x + t ^ 2 * c) := by
    funext x
    simp only [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [e2]
  exact GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h1

theorem evH_invOf_two [Invertible (2 : AF F)] :
    evH F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h2 : evH F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evH F) 2, ← map_mul, invOf_mul_self, map_one]
  calc evH F (⅟(2 : AF F)) = evH F (⅟(2 : AF F)) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (2 * (1 / 2)) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
    _ = (evH F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
        rw [map_mul, map_ofNat]; ring
    _ = _ := by rw [h2, one_mul]

theorem rho_pureA [Invertible (2 : AF F)] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : W) (t : ℝ) (f : SInf F κ)
    (g : (κ → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ) :
    d.rho ψ (realAd F t • u) (pureA F f g) =
      pureA F (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * trL (fun i => evI F ((d.e u).2 i)) x + t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evI F ((d.e u).1 i)) ⬝ᵥ (fun i => evI F ((d.e u).2 i)))) : ℝ) : ℂ)))
        (SchwartzMap.compSubConstCLM ℂ (-(t • fun i => evI F ((d.e u).1 i))) f)) g := by
  set a := (d.e u).1 with ha
  set b := (d.e u).2 with hb
  set X1 : κ → mixedEmbedding.mixedSpace F := fun i => evI F (a i) with hX1
  set Y : κ → mixedEmbedding.mixedSpace F := fun i => evI F (b i) with hY
  funext x
  have hsm : d.e (realAd F t • u) = realAd F t • d.e u := map_smul _ _ _
  simp only [Darboux.rho, schr, hsm, pureA]
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase _ _ _), SchwartzMap.compSubConstCLM_apply,
    smul_eq_mul]
  have hfin : (fun i => ((x + (realAd F t • d.e u).1) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + (realAd F t).2 * (a i).2 = _
    rw [realAd_snd, zero_mul, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • d.e u).1) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) - -(t • X1) := by
    funext i
    rw [sub_neg_eq_add]
    change evH F (x i + realAd F t * a i) = evH F (x i) + t • evH F (a i)
    rw [map_add, map_mul, evH_realAd, Algebra.smul_def]
  set A := x ⬝ᵥ (realAd F t • d.e u).2 + ⅟(2 : AF F) * ((realAd F t • d.e u).1 ⬝ᵥ (realAd F t • d.e u).2) with hAdef
  have hA : A = realAd F t * (x ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))) := by
    rw [hAdef]
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hAt : At (evI F) A := by
    intro v hv
    rw [smul_eq_mul, hA, ← mul_assoc]
    have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hv)
    have hvr : v * realAd F t = 0 :=
      Prod.ext (by change v.1 * (realAd F t).1 = 0; rw [hv1, zero_mul])
        (by change v.2 * (realAd F t).2 = 0; rw [realAd_snd, mul_zero])
    rw [hvr, zero_mul]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) =
      t * trL Y (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) +
        t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y)) := by
    have e1 : evI F A = algebraMap ℝ (mixedEmbedding.mixedSpace F) t * ((⇑(evH F) ∘ x) ⬝ᵥ (⇑(evH F) ∘ b) +
        algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) *
          (algebraMap ℝ (mixedEmbedding.mixedSpace F) t * ((⇑(evH F) ∘ a) ⬝ᵥ (⇑(evH F) ∘ b)))) := by
      rw [← evH_apply, hA, map_mul, map_add, map_mul, map_mul, evH_realAd, RingHom.map_dotProduct,
        RingHom.map_dotProduct, evH_invOf_two]
    rw [e1, trL_apply]
    simp only [← Algebra.smul_def, map_add, map_smul, smul_eq_mul]
    change t * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evH F (x i)) ⬝ᵥ Y) +
      1 / 2 * (t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y))) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evH F (x i)) ⬝ᵥ Y) +
        t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y))
    ring
  rw [hψ.2.2 A hAt, htr, hfin, harch]
  ring

end Adelic

open scoped Classical in

theorem derEx : GlobalTheory.RealLift.DerEx := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ
  let x₁ : Matrix α β (AE F E) → (κ → mixedEmbedding.mixedSpace F) := fun u i => evI F ((d.e u).1 i)
  let y : Matrix α β (AE F E) → (κ → mixedEmbedding.mixedSpace F) := fun u i => evI F ((d.e u).2 i)
  refine ⟨fun u => LineDeriv.lineDerivOpCLM ℂ (SInf F κ) (x₁ u) -
      (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((trL (y u) x : ℝ) : ℂ)), fun u _ f => ⟨?_, fun x => ?_⟩⟩
  · intro g hg l hl
    obtain ⟨T, hT⟩ := hl g hg
    have h := hasDerivAt_heis (x₁ u) (trL (y u))
      (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x₁ u ⬝ᵥ y u)) f T
    rw [hT]
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    · simp only
      rw [rho_pureA d ψ hψ u t f g, hT]
  · have htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((trL (y u) x : ℝ) : ℂ) :=
      (Complex.ofRealCLM.comp (trL (y u))).hasTemperateGrowth
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sub_apply,
      SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
    simp only [trL_apply, dotProduct, x₁, y]
    ring

end GlobalTheory.HeisDer
