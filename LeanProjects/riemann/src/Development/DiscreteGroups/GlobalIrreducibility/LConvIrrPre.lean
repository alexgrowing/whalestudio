import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def IsPsd (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop := (∀ x y, starRingEnd ℂ (B x y) = B y x) ∧ ∀ x, 0 ≤ (B x x).re

def Pre (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (_ : IsPsd B) : Type := M

variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

instance : AddCommGroup (Pre B hB) := inferInstanceAs (AddCommGroup M)
instance : Module ℂ (Pre B hB) := inferInstanceAs (Module ℂ M)

instance core : PreInnerProductSpace.Core ℂ (Pre B hB) where
  inner x y := B x y
  conj_inner_symm x y := hB.1 y x
  re_inner_nonneg x := hB.2 x
  add_left x y z := LinearMap.map_add₂ B x y z
  smul_left x y r := (LinearMap.map_smulₛₗ₂ B r x y).trans (smul_eq_mul _ _)

instance : SeminormedAddCommGroup (Pre B hB) := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (Pre B hB) := InnerProductSpace.ofCore (core B hB)

abbrev Hs := Completion (Pre B hB)

def iota : M →ₗ[ℂ] Hs B hB := (Completion.toComplL : Pre B hB →L[ℂ] Hs B hB).toLinearMap

theorem iota_apply (x : M) : iota B hB x = ((show Pre B hB from x : Pre B hB) : Hs B hB) := rfl

theorem inner_iota (x y : M) : ⟪iota B hB x, iota B hB y⟫_ℂ = B x y := by
  rw [iota_apply, iota_apply, Completion.inner_coe]; rfl

theorem re_B (x : M) : (B x x).re = ‖iota B hB x‖ ^ 2 := by
  have h := @inner_self_eq_norm_sq ℂ _ _ _ _ (iota B hB x)
  rw [inner_iota] at h
  simpa using h

theorem ind {p : Hs B hB → Prop} (hp : IsClosed {y | p y}) (h : ∀ x : M, p (iota B hB x)) (y : Hs B hB) :
    p y :=
  Completion.induction_on y hp fun a => h a

theorem ext_iota {T S : Hs B hB →L[ℂ] Hs B hB} (h : ∀ x, T (iota B hB x) = S (iota B hB x)) : T = S :=
  ContinuousLinearMap.ext fun y => ind B hB (p := fun y => T y = S y) (isClosed_eq T.continuous S.continuous) h y

variable {G : Type} [Group G] (ρ : Representation ℂ G M)

theorem rho_mul (g h : G) (x : M) : ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl
theorem rho_one (x : M) : ρ 1 x = x := by rw [map_one]; rfl
theorem rho_inv (g : G) (x : M) : ρ g⁻¹ (ρ g x) = x := by rw [← rho_mul, inv_mul_cancel, rho_one]

variable (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def rhoP (g : G) : Pre B hB →ₗ[ℂ] Pre B hB := ρ g

include hinv in
theorem norm_rhoP (g : G) (x : Pre B hB) : ‖rhoP B hB ρ g x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) x]
  rw [show ⟪rhoP B hB ρ g x, rhoP B hB ρ g x⟫_ℂ = ⟪x, x⟫_ℂ from hinv g x x]

def piF (g : G) : Hs B hB →L[ℂ] Hs B hB :=
  (LinearMap.mkContinuous (rhoP B hB ρ g) 1 fun x => by rw [one_mul, norm_rhoP B hB ρ hinv]).completion

theorem piF_iota (g : G) (x : M) : piF B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := by
  rw [iota_apply, piF, ContinuousLinearMap.completion_apply_coe]; rfl

def pi : G →* (Hs B hB →L[ℂ] Hs B hB) where
  toFun := piF B hB ρ hinv
  map_one' := ext_iota B hB fun x => by rw [piF_iota, rho_one]; rfl
  map_mul' g h := ext_iota B hB fun x => by
    rw [ContinuousLinearMap.mul_apply, piF_iota, piF_iota, piF_iota, rho_mul]

theorem pi_iota (g : G) (x : M) : pi B hB ρ hinv g (iota B hB x) = iota B hB (ρ g x) := piF_iota B hB ρ hinv g x

theorem norm_pi (g : G) (y : Hs B hB) : ‖pi B hB ρ hinv g y‖ = ‖y‖ :=
  ind B hB (p := fun y => ‖pi B hB ρ hinv g y‖ = ‖y‖)
    (isClosed_eq (continuous_norm.comp (pi B hB ρ hinv g).continuous) continuous_norm)
    (fun x => by rw [pi_iota, iota_apply, iota_apply, Completion.norm_coe, Completion.norm_coe]; exact norm_rhoP B hB ρ hinv g x) y

theorem pi_inner (g : G) (u v : Hs B hB) : ⟪pi B hB ρ hinv g u, pi B hB ρ hinv g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  let V : Hs B hB →ₗᵢ[ℂ] Hs B hB := { toLinearMap := (pi B hB ρ hinv g : Hs B hB →ₗ[ℂ] Hs B hB), norm_map' := norm_pi B hB ρ hinv g }
  V.inner_map_map u v

theorem inner_left (g : G) (v w : Hs B hB) : ⟪pi B hB ρ hinv g v, w⟫_ℂ = ⟪v, pi B hB ρ hinv g⁻¹ w⟫_ℂ := by
  rw [← pi_inner B hB ρ hinv g v, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem star_pi (g : G) : star (pi B hB ρ hinv g) = pi B hB ρ hinv g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [inner_left B hB ρ hinv g⁻¹, inv_inv]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
