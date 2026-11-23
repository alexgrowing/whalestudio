import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount

noncomputable section

namespace UpperTheory.V.Z.Sym

open MulAction

def gq {H Y : Type} [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient H Y, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ)

def gqOn {H G : Type} [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) : ℂ :=
  letI : MulAction H (G ⧸ U) := MulAction.compHom _ j
  gq H₀ k

structure Base (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] where
  ι : Γ →* G
  U : Subgroup G
  ω : U →* ℂˣ
  W : Representation ℂ Γ V
  Γ₀ : Subgroup Γ
  cenΓ : Γ₀ ≤ Subgroup.center Γ
  cenG : ∀ z ∈ Γ₀, ι z ∈ Subgroup.center G
  memU : ∀ z ∈ Γ₀, ι z ∈ U
  scal : ∀ z (hz : z ∈ Γ₀) v, W z v = (ω ⟨ι z, memU z hz⟩ : ℂ) • v

namespace Base

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V)

def Forms : Submodule ℂ (G → V) where
  carrier := {φ | (∀ γ g, φ (B.ι γ * g) = B.W γ (φ g)) ∧ ∀ g (u : B.U), φ (g * u) = (B.ω u : ℂ) • φ g}
  add_mem' := fun {a b} ha hb => ⟨fun γ g => by simp [ha.1, hb.1], fun g u => by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun γ g => by simp, fun g u => by simp⟩
  smul_mem' := fun c a ha => ⟨fun γ g => by simp [ha.1], fun g u => by simp [ha.2, smul_comm c]⟩

structure Fin : Prop where
  cls : ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ B.U, g = B.ι γ * s * u
  stab : ∀ g : G, B.Γ₀.relIndex ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) ≠ 0

structure Tw where
  θΓ : Γ ≃* Γ
  θ : G ≃* G
  Θ : V →ₗ[ℂ] V
  comm : ∀ γ, θ (B.ι γ) = B.ι (θΓ γ)
  int : ∀ γ v, Θ (B.W γ v) = B.W (θΓ γ) (Θ v)
  fix : ∀ z ∈ B.Γ₀, θΓ z = z

def Tw.one : B.Tw := ⟨.refl _, .refl _, .id, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

variable {B}

def Tw.mul (s₁ s₂ : B.Tw) : B.Tw where
  θΓ := s₂.θΓ.trans s₁.θΓ
  θ := s₂.θ.trans s₁.θ
  Θ := s₁.Θ ∘ₗ s₂.Θ
  comm γ := by simp [s₂.comm, s₁.comm]
  int γ v := by simp [s₂.int, s₁.int]
  fix z hz := by simp [s₂.fix z hz, s₁.fix z hz]

namespace Tw

variable (s : B.Tw)

structure IsTest (f : G → ℂ) : Prop where
  left : ∀ (u : B.U) y, f (u * y) = ((B.ω u)⁻¹ : ℂˣ) * f y
  right : ∀ (u : B.U) y, f (y * s.θ u) = ((B.ω u)⁻¹ : ℂˣ) * f y
  fin : {x : G ⧸ B.U | f (s.θ x.out) ≠ 0}.Finite

def opF (f : G → ℂ) (φ : G → V) (g : G) : V := ∑ᶠ x : G ⧸ B.U, f (s.θ x.out) • s.Θ (φ (s.θ.symm g * x.out))

open Classical in

def R (f : G → ℂ) : Module.End ℂ B.Forms :=
  if h : ∃ L : Module.End ℂ B.Forms, ∀ φ, (L φ).1 = s.opF f φ.1 then h.choose else 0

def conv (f₁ f₂ : G → ℂ) (y : G) : ℂ := ∑ᶠ x : G ⧸ B.U, f₁ (s.θ x.out) * f₂ (x.out⁻¹ * s.θ.symm y)

def Rel (δ δ' : Γ) : Prop := ∃ x : Γ, ∃ z ∈ B.Γ₀, δ' = x⁻¹ * δ * s.θΓ x * z

def Cent (δ : Γ) : Subgroup Γ where
  carrier := {x | ∃ z ∈ B.Γ₀, x⁻¹ * δ * s.θΓ x = δ * z}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨z, hz, h⟩ ⟨w, hw, h'⟩
    refine ⟨w * z, mul_mem hw hz, ?_⟩
    have hc := Subgroup.mem_center_iff.1 (B.cenΓ hz)
    calc (a * b)⁻¹ * δ * s.θΓ (a * b) = b⁻¹ * (a⁻¹ * δ * s.θΓ a) * s.θΓ b := by simp [mul_assoc]
      _ = (b⁻¹ * δ * s.θΓ b) * z := by rw [h, mul_assoc (b⁻¹ * δ) (s.θΓ b) z, hc (s.θΓ b)]; simp only [mul_assoc]
      _ = δ * (w * z) := by rw [h', mul_assoc]
  inv_mem' := by
    rintro a ⟨z, hz, h⟩
    refine ⟨z⁻¹, inv_mem hz, ?_⟩
    have hc := Subgroup.mem_center_iff.1 (B.cenΓ hz)
    have h1 : δ = a * (δ * z) * (s.θΓ a)⁻¹ := by rw [← h]; simp [mul_assoc]
    rw [eq_mul_inv_iff_mul_eq, inv_inv, map_inv, mul_assoc _ _ z, hc]
    conv_rhs => rw [h1]
    simp [mul_assoc]

def ker (f : G → ℂ) (δ : Γ) (y : G ⧸ B.U) : ℂ := f (y.out⁻¹ * B.ι δ * s.θ y.out)

def term (f : G → ℂ) (δ : Γ) : ℂ :=
  LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) *
    gqOn (B.ι.comp (s.Cent δ).subtype) (B.Γ₀.subgroupOf (s.Cent δ)) B.U (s.ker f δ)

end Tw

end Base

structure RPG {I : Type} (G : Type) [Group G] (Gv : I → Type) [∀ v, Group (Gv v)] (K : ∀ v, Subgroup (Gv v)) where
  p : ∀ v, G →* Gv v
  inj : ∀ g, (∀ v, p v g = 1) → g = 1
  ae : ∀ g, ∀ᶠ v in Filter.cofinite, p v g ∈ K v
  surj : ∀ x : ∀ v, Gv v, (∀ᶠ v in Filter.cofinite, x v ∈ K v) → ∃ g, ∀ v, p v g = x v

def RPG.box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) : Subgroup G := ⨅ v, (U v).comap (P.p v)

def FinOrb {T G : Type} [Group T] [Group G] (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : Prop :=
  ∃ S : Finset G, ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ s ∈ S, ∃ u ∈ U, y = ι t * s * u

def mass {H T : Type} [Group H] [Group T] (φ : H →* T) (H₀ : Subgroup H) (C : Subgroup T) : ℂ :=
  ((φ.range ⊔ C).index : ℂ) / (H₀.relIndex (C.comap φ) : ℂ)

def IsGenEig {Λ M : Type} [AddCommGroup M] [Module ℂ M] (u : Λ → Module.End ℂ M) (χ : Λ → ℂ) : Prop :=
  (⨅ a, (u a).maxGenEigenspace (χ a)) ≠ ⊥

example : Base PUnit PUnit ℂ := ⟨1, ⊤, 1, 1, ⊥, bot_le, fun _ _ => Subgroup.mem_center_iff.2 fun _ => rfl, fun _ _ => trivial, fun _ _ _ => by simp⟩

example : RPG (I := Unit) PUnit (fun _ => PUnit) fun _ => ⊤ := ⟨fun _ => 1, fun _ _ => rfl, fun _ => by simp, fun _ _ => ⟨1, fun _ => rfl⟩⟩

end UpperTheory.V.Z.Sym
