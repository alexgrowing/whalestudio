import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Generic

variable {B Hf W : Type} [Group B] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : B →* Hf) (Γ : Subgroup B)
  (ρ : B →* Module.End ℂ W) {J : Subgroup Hf} {χ : J →* ℂˣ}

theorem rho_mul (a b : B) (w : W) : ρ (a * b) w = ρ a (ρ b w) := by rw [map_mul]; rfl

theorem rho_rho_inv (a : B) (w : W) : ρ a (ρ a⁻¹ w) = w := by rw [← rho_mul, mul_inv_cancel, map_one]; rfl

theorem mem_adForms (s : Hf → B) (hs : ∀ u, π (s u) = u) (hρ : ∀ u, ρ (s u) = 1) (Ψ : B → W)
    (h : ∀ γ ∈ Γ, ∀ k (hk : π k ∈ J), ∀ x, Ψ (γ * x * k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (Ψ x)) :
    (fun u => Ψ (s u)) ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ := by
  intro γ u k
  have e : π (((γ : B) * s u)⁻¹ * s (π γ * u * k)) = k := by
    rw [map_mul, map_inv, map_mul, hs, hs, inv_mul_cancel_left]
  have h1 := h γ γ.2 _ (e ▸ k.2) (s u)
  rw [mul_inv_cancel_left] at h1
  have h2 : ∀ u, ρ (s u)⁻¹ = 1 := fun u => by
    have := map_mul ρ (s u)⁻¹ (s u)
    rwa [inv_mul_cancel, map_one, hρ, mul_one, eq_comm] at this
  refine h1.trans ?_
  have h3 : ρ (((γ : B) * s u)⁻¹ * s (π γ * u * k))⁻¹ = ρ γ := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, map_mul, h2, hρ, one_mul, mul_one]
  rw [h3]
  congr 3
  exact Subtype.ext e

theorem form_law {f : Hf → W} (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : B} (hγ : γ ∈ Γ) (k : B)
    (hk : π k ∈ J) (x : B) :
    ρ (γ * x * k)⁻¹ (f (π (γ * x * k))) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (ρ x⁻¹ (f (π x))) := by
  have h : f (π γ * π x * π k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ γ (f (π x)) := hf ⟨γ, hγ⟩ (π x) ⟨π k, hk⟩
  rw [map_mul π, map_mul π, h, map_smul, ← rho_mul, ← rho_mul]
  congr 3
  group

theorem vec_law (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {a b : W} {z : ℂ} (hz : ‖z‖ = 1) (k : B)
    (h : ∀ w, inner ℂ a w = z⁻¹ * inner ℂ b (ρ k w)) : a = z • ρ k⁻¹ b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [h, inner_smul_left, ← hρ k (ρ k⁻¹ b), ← rho_mul, mul_inv_cancel, map_one, Complex.inv_eq_conj hz]
  rfl

theorem exists_dual [FiniteDimensional ℂ W] (u : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, inner ℂ a w = u w :=
  haveI := FiniteDimensional.complete ℂ W
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap u), fun _ => InnerProductSpace.toDual_symm_apply⟩

theorem exists_linear_section {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X → Y → Prop)
    (h0 : p 0 0) (hadd : ∀ x x' y y', p x y → p x' y' → p (x + x') (y + y')) (hsm : ∀ (a : ℂ) x y, p x y → p (a • x) (a • y))
    (hex : ∀ x, ∃ y, p x y) : ∃ th : X →ₗ[ℂ] Y, ∀ x, p x (th x) := by
  let S : Submodule ℂ (X × Y) :=
    { carrier := {z | p z.1 z.2}
      add_mem' := fun h h' => hadd _ _ _ _ h h'
      zero_mem' := h0
      smul_mem' := fun a _ h => hsm a _ _ h }
  obtain ⟨g, hg⟩ := (LinearMap.fst ℂ X Y ∘ₗ S.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => (hex x).elim fun y hy => ⟨⟨(x, y), hy⟩, rfl⟩)
  refine ⟨LinearMap.snd ℂ X Y ∘ₗ S.subtype ∘ₗ g, fun x => ?_⟩
  have h1 : p (g x).1.1 (g x).1.2 := (g x).2
  have h2 : (g x).1.1 = x := LinearMap.congr_fun hg x
  rwa [h2] at h1

theorem scalar_of_form {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥)
    (Λ : ℂ) (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') = Λ * inner ℂ y y') :
    ∀ y ∈ U, th (LinearMap.adjoint th y) = ((‖Λ‖ : ℝ) : ℂ) • y := by
  obtain ⟨y₀, hy₀, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have e := h y₀ hy₀ y₀
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have hn : ((‖y₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have e1 : Λ = ((‖LinearMap.adjoint th y₀‖ ^ 2 / ‖y₀‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hn)]
    exact e.symm
  have e2 : Λ = ((‖Λ‖ : ℝ) : ℂ) := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  intro y hy
  refine ext_inner_right ℂ fun y' => ?_
  rw [← LinearMap.adjoint_inner_right, h y hy, inner_smul_left, Complex.conj_ofReal, ← e2]

end Generic

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)

include hω hc hφ hinf hlev in

theorem kernel_law {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V) (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (x : GA D V)
    (g : GA D W) (w : c.W) :
    Datum.thetaKO ω (γ * x * k) g (φ w) = (Lev.levChi V β L k)⁻¹ * Datum.thetaKO ω x g (φ (c.ρ k w)) := by
  obtain ⟨κ, h1, h2⟩ := exists_finLift V ((finHom V).rangeRestrict k)
  have h3 : finHom V κ = finHom V k := congrArg Subtype.val h2
  have h4 : Lev.finE V κ = Lev.finE V k := by rw [Lev.finE_eq, Lev.finE_eq, h3]
  have h5 : κ⁻¹ * k ∈ GinfC V := by
    change finHom V (κ⁻¹ * k) = 1
    rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h6 : c.ρ (κ⁻¹ * k) = c.ρ k := by rw [map_mul, hc.1 _ (inv_mem h1), one_mul]
  have h7 : Lev.levChi V β L κ = Lev.levChi V β L k := by unfold Lev.levChi; rw [h4]
  have e : ((γ * x * k, g) : GA D V × GA D W) = (γ, 1) * ((x, g) * ((κ, 1) * (κ⁻¹ * k, 1))) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul, mul_inv_cancel_left, mul_assoc]
  unfold Datum.thetaKO
  rw [e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinf _ h5, h6,
    hlev κ ⟨h1, show Lev.finE V κ ∈ _ from h4 ▸ hk⟩, map_smul, map_smul, Pi.smul_apply, smul_eq_mul,
    hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ (hφ _)), h7]

theorem thetaKO_smul (h : GA D V) (g : GA D W) (a : ℂ) (f : Datum.WO V W → ℂ) :
    Datum.thetaKO ω h g (a • f) = a * Datum.thetaKO ω h g f := by
  unfold Datum.thetaKO
  rw [map_smul]
  rfl

theorem norm_levChi (k : GA D V) : ‖Lev.levChi V β L k‖ = 1 := norm_levFn _ _ _

theorem ext_law {x : Bridge.Gf V → c.W}
    (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V)
    (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (h : GA D V) :
    c.ext x (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (c.ext x h) :=
  form_law (finHom V).rangeRestrict (GQ V) c.ρ hx hγ k ((mem_grpOf V β L k).2 hk) h

theorem ext_finLift (hc : c.Is) (x : Bridge.Gf V → c.W) (u : Bridge.Gf V) : c.ext x (finLift V u) = x u := by
  change c.ρ (finLift V u)⁻¹ (x ((finHom V).rangeRestrict (finLift V u))) = x u
  rw [hc.1 _ (inv_mem (finLift_mem V u)), finLift_spec]
  rfl

include hω hc hφ hinf hlev in

theorem theta_classSum {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) (g : GA D W) :
    ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext x h)) ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (finLift V (y j)) g (φ (x (y j))) := by
  rw [integral_eq_classSum V β L hν hy]
  · simp only [ext_finLift c hc]
  · intro γ hγ k hk h
    rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, ext_law c β L hx hγ k hk, (c.ρ k).map_smul,
      rho_rho_inv c.ρ k, φ.map_smul, thetaKO_smul]
    exact inv_mul_cancel_left₀ (Lev.levChi_ne_zero L k) _

include hω hc hφ hinf hlev in

theorem exists_upVec (μ : Measure (GA D W)) (𝓖 : Set (GA D W)) (F : GA D W → ℂ)
    (hint : ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (F g)) 𝓖 μ) :
    ∃ Ψ : GA D V → c.W, (∀ h w, inner ℂ (Ψ h) w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F) ∧
      ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
        Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h) := by
  have h1 : ∀ h, ∃ a : c.W, ∀ w, inner ℂ a w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F := fun h =>
    exists_dual
      { toFun := fun w => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F
        map_add' := fun w w' => by
          unfold l2 Lift.pet
          rw [← integral_add (hint w h) (hint w' h)]
          simp only [Datum.thetaKO, map_add, Pi.add_apply, add_mul]
        map_smul' := fun a w => by
          unfold l2 Lift.pet
          simp only [Datum.thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
          exact integral_const_mul _ _ }
  choose Ψ hΨ using h1
  refine ⟨Ψ, hΨ, fun γ hγ k hk h => vec_law c.ρ hc.2.1 (norm_levChi β L k) k fun w => ?_⟩
  rw [hΨ, hΨ]
  unfold l2 Lift.pet
  rw [← integral_const_mul]
  congr 1
  funext g
  beta_reduce
  rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, mul_assoc]

end Kernel

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {X I : Type} [MeasurableSpace X] [Fintype I] (μ : Measure X) (𝓖 : Set X) (w : I → ℂ) (k : I → X → ℂ) (F T : X → ℂ)
    (hT : ∀ g, T g = ∑ j, w j * k j g) (hi : ∀ j, IntegrableOn (fun g => k j g * starRingEnd ℂ (F g)) 𝓖 μ) :
    l2 μ 𝓖 T F = ∑ j, w j * l2 μ 𝓖 (k j) F := by
  unfold l2 Lift.pet
  simp only [hT, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun j _ => (hi j).const_mul _]
  simp only [integral_const_mul]

theorem l2_eq_star {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓖 : Set X) (F T : X → ℂ) :
    l2 μ 𝓖 T F = ∫ g in 𝓖, star (F g) * T g ∂μ := by
  unfold l2 Lift.pet
  simp only [mul_comm]
  rfl

end GlobalTheory.AdelicScalar

end
