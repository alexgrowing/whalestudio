import Mathlib

noncomputable section

namespace GlobalTheory.KCoh

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
variable {M M' M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

def IsOneCocycleOnSubgroup (ρ : Representation R G M) (H : Subgroup G) (a : G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + ρ g (a h)

def d1 (ρ : Representation R G M) (b : G → M) (g h : G) : M := ρ g (b h) - b (g * h) + b g

def IsTwoCocycleOnSubgroup (ρ : Representation R G M) (H : Subgroup G) (z : G → G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ k ∈ H, ρ g (z h k) - z (g * h) k + z g (h * k) - z g h = 0

def Cob (ρ : Representation R G M) (H : Subgroup G) (z : G → G → M) (η : G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, z g h = d1 ρ η g h

def Eqv (ρ : Representation R G M) (ρ' : Representation R G M') (f : M →ₗ[R] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def Eqv₂ (ρ : Representation R G M) (ρ' : Representation R G M') (ρ'' : Representation R G M'')
    (β : M →ₗ[R] M' →ₗ[R] M'') : Prop :=
  ∀ g m m', β (ρ g m) (ρ' g m') = ρ'' g (β m m')

def Triv (ρ : Representation R G M) (H : Subgroup G) : Prop := ∀ h ∈ H, ∀ m, ρ h m = m

def cup (ρ' : Representation R G M') (β : M →ₗ[R] M' →ₗ[R] M'') (a : G → M) (b : G → M') (g h : G) : M'' :=
  β (a g) (ρ' g (b h))

def edge (ρ : Representation R G M) (z : G → G → M) (η : G → M) (σ h : G) : M :=
  ρ σ (η (σ⁻¹ * h * σ)) - η h + z h σ - z σ (σ⁻¹ * h * σ)

def conj (ρ : Representation R G M) (σ : G) (φ : G → M) (h : G) : M := ρ σ (φ (σ⁻¹ * h * σ))

def tw (χ : G →* Rˣ) (ρ : Representation R G M) : Representation R G M where
  toFun g := (χ g : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext m
    simp [mul_smul, smul_comm (χ h : R) (χ g : R)]

def chr (χ : G →* Rˣ) : Representation R G R := tw χ (Representation.trivial R G R)

def sh (S : Type*) [MulAction G S] (ρ : Representation R G M) : Representation R G (S → M) where
  toFun g :=
    { toFun := fun f s => ρ g (f (g⁻¹ • s))
      map_add' := fun f f' => by funext s; simp
      map_smul' := fun c f => by funext s; simp }
  map_one' := by ext f s; simp
  map_mul' g h := by ext f s; simp [mul_smul]

def push {S S' : Type*} [Fintype S'] (π : S' → S) : (S' → M) →ₗ[R] (S → M) :=
  open Classical in
  { toFun := fun f s => ∑ s' ∈ Finset.univ.filter (fun s' => π s' = s), f s'
    map_add' := fun f f' => by funext s; simp [Finset.sum_add_distrib]
    map_smul' := fun c f => by funext s; simp [Finset.smul_sum] }

def pull {S S' : Type*} (π : S' → S) : (S → M) →ₗ[R] (S' → M) := LinearMap.funLeft R M π

def ptw (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') : (S → M) →ₗ[R] (S → M') →ₗ[R] (S → M'') :=
  LinearMap.mk₂ R (fun f f' s => β (f s) (f' s))
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)

def fam {S : Type*} (f : S → M →ₗ[R] M') : (S → M) →ₗ[R] (S → M') where
  toFun m s := f s (m s)
  map_add' _ _ := by funext s; simp
  map_smul' _ _ := by funext s; simp

def lg {Ω : Type*} [Field Ω] {N : ℕ} (ζ a b : Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, a = ζ ^ i.val * b then h.choose else 0

def kum {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ) (ζ : Ω)
    (θ : S → Ω) (g : Ω ≃ₐ[F] Ω) (s : S) : ZMod N :=
  lg ζ (g (θ (g⁻¹ • s))) (θ s)

def Roots {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ)
    (θ : S → Ω) : Prop :=
  (∀ s, θ s ≠ 0) ∧ ∀ (g : Ω ≃ₐ[F] Ω) s, θ (g • s) ^ N = g (θ s ^ N)

@[simp] theorem sh_apply (S : Type*) [MulAction G S] (ρ : Representation R G M) (g : G) (f : S → M) (s : S) :
    sh S ρ g f s = ρ g (f (g⁻¹ • s)) := rfl

@[simp] theorem tw_apply (χ : G →* Rˣ) (ρ : Representation R G M) (g : G) (m : M) :
    tw χ ρ g m = (χ g : R) • ρ g m := rfl

@[simp] theorem pull_apply {S S' : Type*} (π : S' → S) (f : S → M) (s : S') : pull (R := R) π f s = f (π s) := rfl

@[simp] theorem ptw_apply (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') (f : S → M) (f' : S → M') (s : S) :
    ptw S β f f' s = β (f s) (f' s) := rfl

@[simp] theorem fam_apply {S : Type*} (f : S → M →ₗ[R] M') (m : S → M) (s : S) : fam f m s = f s (m s) := rfl

example (ρ : Representation R G M) (H : Subgroup G) : IsTwoCocycleOnSubgroup ρ H 0 ∧ Cob ρ H 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp [d1]⟩

example (ρ : Representation R G M) (H : Subgroup G) (b : G → M) : Cob ρ H (d1 ρ b) b := fun _ _ _ _ => rfl

example {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ) :
    Roots (F := F) N (fun _ : S => (1 : Ω)) := ⟨fun _ => one_ne_zero, fun g s => by simp⟩

end GlobalTheory.KCoh
