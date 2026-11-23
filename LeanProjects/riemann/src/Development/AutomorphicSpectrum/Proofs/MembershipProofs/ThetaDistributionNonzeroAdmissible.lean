import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct Topology Classical

namespace GlobalTheory.CompanionTheory.AdelicHeis

open Complex in
theorem iteratedDeriv_exp_I (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => exp (I * t)) = fun t : ℝ => I ^ n * exp (I * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := (((hasDerivAt_id t).ofReal_comp.const_mul I).cexp).const_mul (I ^ n)
    simp only [id] at h
    rw [h.deriv]
    simp only [Complex.ofReal_one, mul_one]
    ring

open Complex in
theorem temperate_exp_I : (fun t : ℝ => exp (I * t)).HasTemperateGrowth := by
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_I, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

theorem temperate_char {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V → ℂ) (hc : Continuous g)
    (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1) (hadd : ∀ s t, g (s + t) = g s * g t) : g.HasTemperateGrowth := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(V, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : V →L[ℝ] ℝ := (AddMonoidHom.mk' L hLa).toRealLinearMap L.continuous
  have e : g = (fun t : ℝ => Complex.exp (Complex.I * t)) ∘ l := by
    funext t
    have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
    rw [h4, Circle.coe_exp, mul_comm]
    rfl
  rw [e]
  exact temperate_exp_I.comp l.hasTemperateGrowth

theorem mul_mem_SB {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {c : R → ℂ}
    (h : IsLocallyConstant c) {κ : Type} [Fintype κ] (y x₁ : κ → R) {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) :
    (fun x => c (x ⬝ᵥ y) * g (x + x₁)) ∈ SB (κ → R) := by
  have h1 : IsLocallyConstant fun x : κ → R => c (x ⬝ᵥ y) :=
    h.comp_continuous (f := fun x : κ → R => x ⬝ᵥ y) (by unfold dotProduct; fun_prop)
  have h2 : IsLocallyConstant fun x : κ → R => g (x + x₁) :=
    hg.1.comp_continuous (f := fun x : κ → R => x + x₁) (by fun_prop)
  have h3 : HasCompactSupport fun x : κ → R => g (x + x₁) := hg.2.comp_homeomorph (Homeomorph.addRight x₁)
  exact ⟨h1.mul h2, h3.mul_left⟩

variable {F : Type} [Field F] [NumberField F]

theorem norm_eq_one (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (hF : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) (x : AdeleRing (𝓞 F) F) : ‖ψ x‖ = 1 := by
  obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  have hD : IsCompact (C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :
      Set (AdeleRing (𝓞 F) F)) := hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F)
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hψ.continuousOn
  have hb : ∀ y, ‖ψ y‖ ≤ M := fun y => by
    obtain ⟨k, hk⟩ := hx y
    have := hM _ hk
    have e : ψ y = ψ (y - algebraMap F _ k) := by
      conv_lhs => rw [← sub_add_cancel y (algebraMap F _ k), AddChar.map_add_eq_mul, hF, mul_one]
    rwa [e]
  have hle : ∀ y, ‖ψ y‖ ≤ 1 := fun y => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.mp h)
    have := hb (n • y)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    linarith
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  have := hle x
  have := hle (-x)
  have := norm_nonneg (ψ x)
  nlinarith

theorem isLocallyConstant_fin (ψ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) :
    IsLocallyConstant ψ := by
  have hm : ∀ a, ψ a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) Circle :=
    { toFun := fun a => ⟨ψ a, hm a⟩
      map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => Subtype.ext (ψ.map_add_eq_mul a b) }
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_finiteChar_mul_eq_one χ (hψ.subtype_mk hm)
  set δ : F := algebraMap (𝓞 F) F d with hδdef
  have hδ : δ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) δ⁻¹ * (z - x)) ⁻¹'
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) ∈ 𝓝 x :=
    ((GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage (by fun_prop)).mem_nhds (by simp)
  filter_upwards [this] with z hz
  have h1 : ψ _ = 1 := congrArg Subtype.val (hd _ hz)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hδ, map_one, one_mul] at h1
  rw [← sub_add_cancel z x, AddChar.map_add_eq_mul, h1, one_mul]

theorem pure_mem {κ : Type} [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    (x₁ y : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun x => ψ (x ⬝ᵥ y) * pureA F f g (x + x₁)) ∈ schA F κ := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let a : (κ → mixedEmbedding.mixedSpace F) →+ AdeleRing (𝓞 F) F :=
    { toFun := fun u => (fun i => GroundTheory.Global.infiniteAdeleInl (GroundTheory.Global.mixedToInfinite F (u i))) ⬝ᵥ y
      map_zero' := by simp
      map_add' := fun u v => by simp [dotProduct, add_mul, Finset.sum_add_distrib] }
  have ha : Continuous a := by
    refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
    exact GroundTheory.Global.continuous_infiniteAdeleInl.comp
      (GroundTheory.Global.continuous_mixedToInfinite.comp (continuous_apply i))
  have hT : Function.HasTemperateGrowth fun u => ψ (a u) :=
    temperate_char _ (hψ.comp ha) (fun _ => hn _) (by simp) fun s t => by rw [map_add, AddChar.map_add_eq_mul]
  let ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ := ψ.compAddMonoidHom GroundTheory.Global.finiteAdeleInr
  have hf : IsLocallyConstant ψf :=
    isLocallyConstant_fin ψf (hψ.comp GroundTheory.Global.continuous_finiteAdeleInr) fun _ => hn _
  refine Submodule.subset_span ⟨SchwartzMap.smulLeftCLM ℂ (fun u => ψ (a u))
    (SchwartzMap.compSubConstCLM ℂ (-fun i => e (x₁ i).1) f),
    fun x => ψf (x ⬝ᵥ fun i => (y i).2) * g (x + fun i => (x₁ i).2), mul_mem_SB hf _ _ hg, ?_⟩
  funext x
  have k1 : x ⬝ᵥ y = a (fun i => e (x i).1) + GroundTheory.Global.finiteAdeleInr ((fun i => (x i).2) ⬝ᵥ fun i => (y i).2) := by
    show _ = (∑ i, _) + _
    simp only [dotProduct, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : GroundTheory.Global.mixedToInfinite F (e (x i).1) = (x i).1 := e.symm_apply_apply _
    rw [this]
    refine Prod.ext (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) ?_ ?_
    · simp [GroundTheory.Global.adeleRing_add_fst, GroundTheory.Global.infiniteAdeleInl_fst, GroundTheory.Global.finiteAdeleInr_fst]
    · simp [GroundTheory.Global.adeleRing_add_snd, GroundTheory.Global.infiniteAdeleInl_snd, GroundTheory.Global.finiteAdeleInr_snd]
  have k2 : (fun i => e ((x + x₁) i).1) = (fun i => e (x i).1) + fun i => e (x₁ i).1 :=
    funext fun i => map_add e (x i).1 (x₁ i).1
  have k3 : (fun i => ((x + x₁) i).2) = (fun i => (x i).2) + fun i => (x₁ i).2 := rfl
  unfold pureA
  rw [SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, k1,
    AddChar.map_add_eq_mul, k2, k3, smul_eq_mul]
  simp only [ψf, AddChar.compAddMonoidHom_apply, e]
  ring

theorem schr_mem_and_thetaSum : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → (∀ w, ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ) ∧ ∀ (w : (κ → F) × (κ → F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ), thetaSum F (schr ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) Φ) = thetaSum F Φ := by
  intro F _ _ _ _ κ _ ψ hψ _ hF
  refine ⟨fun w Φ hΦ => ?_, fun w Φ => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, g, hg, rfl⟩ := h
      have := (schA F κ).smul_mem (ψ (⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)))
        (pure_mem ψ hψ (norm_eq_one ψ hψ hF) w.1 w.2 f g hg)
      convert this using 1
      funext x
      simp only [schr, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul]
      ring
    | zero =>
      convert (schA F κ).zero_mem using 1
      funext x
      simp [schr]
    | add Φ Ψ _ _ h1 h2 =>
      convert (schA F κ).add_mem h1 h2 using 1
      funext x
      simp only [schr, Pi.add_apply]
      ring
    | smul c Φ _ h =>
      convert (schA F κ).smul_mem c h using 1
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
  · have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F _ 2⁻¹ := by
      apply invOf_eq_right_inv
      rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    unfold thetaSum
    rw [← (Equiv.addRight w.1).tsum_eq fun ξ : κ → F => Φ fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)]
    refine tsum_congr fun ξ => ?_
    have := hF (ξ ⬝ᵥ w.2 + 2⁻¹ * (w.1 ⬝ᵥ w.2))
    simp only [dotProduct, map_add, map_mul, map_sum] at this
    simp only [schr, dotProduct, h2]
    rw [this, one_mul]
    congr 1
    funext i
    simp

end GlobalTheory.CompanionTheory.AdelicHeis
