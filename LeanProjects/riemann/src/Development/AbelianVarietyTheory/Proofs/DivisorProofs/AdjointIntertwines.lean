import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SecLift

section Lin

theorem exists_lift_lin {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (he : Function.Injective e) (f : X →ₗ[ℂ] Z) (hf : ∀ x, ∃ y, e y = f x) :
    ∃ g : X →ₗ[ℂ] Y, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict (LinearMap.range e) hf, fun x => ?_⟩
  have := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict (LinearMap.range e) hf x)
  exact congrArg Subtype.val this

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

omit [FiniteDimensional ℂ X] in
theorem inner_of_norm (a : X →ₗ[ℂ] X) (ha : ∀ x, ‖a x‖ = ‖x‖) (x x' : X) : ⟪a x, a x'⟫_ℂ = ⟪x, x'⟫_ℂ :=
  (LinearIsometry.mk a ha).inner_map_map x x'

theorem adjoint_intertwines (th : X →ₗ[ℂ] Y) (a : X →ₗ[ℂ] X) (b : Y →ₗ[ℂ] Y) (ha : ∀ x, ‖a x‖ = ‖x‖) (hb : ∀ y, ‖b y‖ = ‖y‖)
    (hc : ∀ x, th (a x) = b (th x)) (y : Y) : LinearMap.adjoint th (b y) = a (LinearMap.adjoint th y) := by
  have hs : Function.Surjective a := LinearMap.injective_iff_surjective.1 (LinearIsometry.mk a ha).injective
  refine ext_inner_right ℂ fun x => ?_
  obtain ⟨x', rfl⟩ := hs x
  rw [LinearMap.adjoint_inner_left, hc, inner_of_norm b hb, inner_of_norm a ha, LinearMap.adjoint_inner_left]

theorem inner_central {G : Type} [Group G] [Fintype G] (ρ : Representation ℂ G Y) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (c : G → ℂ)
    (hc : ∀ g y, (∑ h, c h • ρ h) (ρ g y) = ρ g ((∑ h, c h • ρ h) y)) (y : Y) (hy : (∑ h, c h • ρ h) y = y) (w : Y) :
    ⟪y, (∑ h, c h • ρ h) w⟫_ℂ = ⟪y, w⟫_ℂ := by
  set E : Y →ₗ[ℂ] Y := ∑ h, c h • ρ h with hE
  have hadj : ∀ w, LinearMap.adjoint E w = ∑ h, star (c h) • ρ h⁻¹ w := fun w => by
    refine ext_inner_right ℂ fun x => ?_
    rw [LinearMap.adjoint_inner_left, hE, LinearMap.sum_apply, inner_sum, sum_inner]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← inner_of_norm (ρ h) (hρ h) (ρ h⁻¹ w),
      Representation.self_inv_apply]
    simp
  have hcomm : E (LinearMap.adjoint E y) = LinearMap.adjoint E y := by
    rw [hadj, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, hc, hy]
  have h0 : LinearMap.adjoint E y - y = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, LinearMap.adjoint_inner_left, map_sub, hcomm, hy, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 h0]

end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def evL (v : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem integral_four {X : Type} [MeasurableSpace X] {μ : Measure X} {f1 f2 f3 f4 : X → ℂ} (i1 : Integrable f1 μ)
    (i2 : Integrable f2 μ) (i3 : Integrable f3 μ) (i4 : Integrable f4 μ) (a : ℂ := Complex.I) :
    ∫ g, (f1 g - f2 g - a * f3 g + a * f4 g) ∂μ =
      ∫ g, f1 g ∂μ - ∫ g, f2 g ∂μ - a * ∫ g, f3 g ∂μ + a * ∫ g, f4 g ∂μ := by
  have j1 : Integrable (fun g => f1 g - f2 g) μ := i1.sub i2
  have j2 : Integrable (fun g => f1 g - f2 g - a * f3 g) μ := j1.sub (i3.const_mul a)
  rw [integral_add j2 (i4.const_mul a), integral_sub j1 (i3.const_mul a), integral_sub i1 i2, integral_const_mul,
    integral_const_mul]

theorem inner_eq_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec)
    (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    IntegrableOn (fun g => star (e x v g) * e y v g) 𝓕 μ ∧ inner ℂ x y = d * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hp : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv τ]; simp
  have diag : ∀ x, IntegrableOn (fun g => star (e x v g) * e x v g) 𝓕 μ ∧
      inner ℂ x x = d * ∫ g in 𝓕, star (e x v g) * e x v g ∂μ := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    have hc : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c := by
      by_contra hc
      apply hx
      rw [← inner_self_eq_zero (𝕜 := ℂ), hip, ipM, dif_neg hc, mul_zero]
    have := ipM_spec M μ 𝓕 _ _ hc v v
    rw [hp, mul_one] at this
    exact ⟨this.1, by rw [hip, this.2]⟩
  have key : (fun g => star (e x v g) * e y v g) = fun g => (1 / 4 : ℂ) *
      (star (e (x + y) v g) * e (x + y) v g - star (e (x - y) v g) * e (x - y) v g -
        Complex.I * (star (e (x + Complex.I • y) v g) * e (x + Complex.I • y) v g) +
        Complex.I * (star (e (x - Complex.I • y) v g) * e (x - Complex.I • y) v g)) := by
    funext g
    simp only [map_add, map_sub, map_smul, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (-(1/2 : ℂ) * ((starRingEnd ℂ) (e y v g) * e x v g - (starRingEnd ℂ) (e x v g) * e y v g)) * Complex.I_mul_I
  obtain ⟨i1, e1⟩ := diag (x + y)
  obtain ⟨i2, e2⟩ := diag (x - y)
  obtain ⟨i3, e3⟩ := diag (x + Complex.I • y)
  obtain ⟨i4, e4⟩ := diag (x - Complex.I • y)
  rw [key]
  refine ⟨(((i1.sub i2).sub (i3.const_mul _)).add (i4.const_mul _)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_four i1 i2 i3 i4]
  generalize (∫ g in 𝓕, star (e (x + y) v g) * e (x + y) v g ∂μ) = a1 at e1
  generalize (∫ g in 𝓕, star (e (x - y) v g) * e (x - y) v g ∂μ) = a2 at e2
  generalize (∫ g in 𝓕, star (e (x + Complex.I • y) v g) * e (x + Complex.I • y) v g ∂μ) = a3 at e3
  generalize (∫ g in 𝓕, star (e (x - Complex.I • y) v g) * e (x - Complex.I • y) v g ∂μ) = a4 at e4
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at e1 e2 e3 e4
  linear_combination (1 / 4 : ℂ) * (e1 - e2 - Complex.I * e3 + Complex.I * e4) +
    ((1/2 : ℂ) * (inner ℂ x y - inner ℂ y x)) * Complex.I_mul_I

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dif_pos hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

theorem exists_translate {Γ W H : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [Module ℂ H]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (a : ℂ) (k : Γ)
    (hu : ∀ y, ∃ y', (∀ h, e y' h = a • e y (h * k)) ∧ ‖y'‖ = ‖y‖) :
    ∃ b : H →ₗ[ℂ] H, (∀ y h, e (b y) h = a • e y (h * k)) ∧ ∀ y, ‖b y‖ = ‖y‖ := by
  obtain ⟨b, hb⟩ := exists_lift_lin e he (a • LinearMap.funLeft ℂ W (fun h => h * k) ∘ₗ e)
    fun y => (hu y).imp fun y' h => funext h.1
  have hb' : ∀ y h, e (b y) h = a • e y (h * k) := fun y h => congrFun (hb y) h
  refine ⟨b, hb', fun y => ?_⟩
  obtain ⟨y', h1, h2⟩ := hu y
  rw [← h2, he (funext fun h => (hb' y h).trans (h1 h).symm)]

end Act

end GlobalTheory.SecLift

end
