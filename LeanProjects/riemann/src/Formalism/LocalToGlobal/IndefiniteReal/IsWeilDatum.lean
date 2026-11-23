import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.IndefR.Heis

section Law

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def IsAlt (B : M →ₗ[R] M →ₗ[R] R) : Prop := ∀ w, B w w = 0

@[ext] structure HeisG (B : M →ₗ[R] M →ₗ[R] R) where

  w : M

  t : R

namespace HeisG

variable {B : M →ₗ[R] M →ₗ[R] R} [Invertible (2 : R)]

def mulH (x y : HeisG B) : HeisG B := ⟨x.w + y.w, x.t + y.t + ⅟2 * B x.w y.w⟩

instance : Mul (HeisG B) := ⟨mulH⟩

instance : One (HeisG B) := ⟨⟨0, 0⟩⟩

instance : Inv (HeisG B) := ⟨fun x => ⟨-x.w, -x.t⟩⟩

theorem mul_def (x y : HeisG B) : x * y = ⟨x.w + y.w, x.t + y.t + ⅟2 * B x.w y.w⟩ := rfl

theorem one_def : (1 : HeisG B) = ⟨0, 0⟩ := rfl

theorem inv_def (x : HeisG B) : x⁻¹ = ⟨-x.w, -x.t⟩ := rfl

end HeisG

end Law

@[reducible] def invTwoOf (K A : Type*) [Field K] [CharZero K] [CommRing A] [Algebra K A] : Invertible (2 : A) where
  invOf := algebraMap K A (1 / 2)
  invOf_mul_self := by
    rw [← map_ofNat (algebraMap K A) 2, ← map_mul]; norm_num
  mul_invOf_self := by
    rw [← map_ofNat (algebraMap K A) 2, ← map_mul]; norm_num

section Rat

variable {E : Type*} [Field E] [NumberField E] (c : E →+* E)

def IsConjXi (ξ₀ : E) : Prop := (∀ x, c (c x) = x) ∧ ξ₀ ≠ 0 ∧ c ξ₀ = -ξ₀

structure HermSp where

  n : ℕ

  J : Matrix (Fin n) (Fin n) E
  herm : J.transpose = J.map c
  nondeg : J.det ≠ 0

variable {c}

def hf (V : HermSp c) (v u : Fin V.n → E) : E := ∑ i, ∑ j, v i * V.J i j * c (u j)

def IsUnitary (V : HermSp c) (g : Matrix (Fin V.n) (Fin V.n) E) : Prop :=
  g.transpose * V.J * g.map c = V.J

abbrev WW (V W : HermSp c) : Type _ := Matrix (Fin W.n) (Fin V.n) E

def adj (V W : HermSp c) (y : WW V W) : Matrix (Fin V.n) (Fin W.n) E :=
  (V.J⁻¹).transpose * (y.map c).transpose * W.J.transpose

def hWW (V W : HermSp c) (x y : WW V W) : E := Matrix.trace (adj V W y * x)

def sympl (ξ₀ : E) (V W : HermSp c) (x y : WW V W) : ℚ := Algebra.trace ℚ E (ξ₀ * hWW V W x y)

def actQ (V W : HermSp c) (a : Matrix (Fin V.n) (Fin V.n) E) (b : Matrix (Fin W.n) (Fin W.n) E) (x : WW V W) :
    WW V W := b * x * a⁻¹

end Rat

section Ad

variable {𝔸 WA : Type*} [CommRing 𝔸] [AddCommGroup WA] [Module 𝔸 WA]

def IsStdPsi [Algebra ℚ 𝔸] (ψ : AddChar 𝔸 ℂ) (sInf : ℝ →+ 𝔸) : Prop :=
  (∀ q : ℚ, ψ (algebraMap ℚ 𝔸 q) = 1) ∧
    ∀ t : ℝ, ψ (sInf t) = Complex.exp (-(2 * Real.pi * Complex.I * t))

variable [Invertible (2 : 𝔸)] (ψ : AddChar 𝔸 ℂ) (B : WA →ₗ[𝔸] WA →ₗ[𝔸] 𝔸)

def IsQuasi (Γ : AddSubgroup WA) (f : WA → ℂ) : Prop :=
  ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (⅟2 * B w γ) * f w

def rho (w₀ : WA) (f : WA → ℂ) : WA → ℂ := fun w => ψ (⅟2 * B w w₀) * f (w + w₀)

def l2sq [MeasurableSpace WA] (μ : Measure WA) (𝓕 : Set WA) (f : WA → ℂ) : ℝ≥0∞ := ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

def Hsp [MeasurableSpace WA] (Γ : AddSubgroup WA) (μ : Measure WA) (𝓕 : Set WA) : Set (WA → ℂ) :=
  {f | IsQuasi ψ B Γ f ∧ MemLp f 2 (μ.restrict 𝓕)}

def Hsm [MeasurableSpace WA] [TopologicalSpace WA] (Γ : AddSubgroup WA) (μ : Measure WA) (𝓕 : Set WA) :
    Set (WA → ℂ) :=
  {f | f ∈ Hsp ψ B Γ μ 𝓕 ∧ Continuous f}

def Theta (f : WA → ℂ) : ℂ := f 0

def ratAct (a : WA ≃ₗ[𝔸] WA) (f : WA → ℂ) : WA → ℂ := fun w => f (a.symm w)

structure AdModel {E : Type*} [Field E] [NumberField E] {c : E →+* E} [Algebra ℚ 𝔸] (ξ₀ : E) (V W : HermSp c)
    (Γ : AddSubgroup WA) where

  incl : WW V W →+ WA
  inj : Function.Injective incl
  range : incl.range = Γ
  form : ∀ x y, B (incl x) (incl y) = algebraMap ℚ 𝔸 (sympl ξ₀ V W x y)
  span : Submodule.span 𝔸 (Set.range incl) = ⊤

end Ad

section D7

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hth (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := by
    refine ⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => ?_⟩, continuous_const, fun k L _ _ w => contDiff_const⟩
    funext w; simp [Heisenberg₂]
  add_mem' := by
    intro f g hf hg
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨U', hU', hUg⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U ⊓ U', ?_, fun u hu h0 => ?_⟩, hf.cont.add hg.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
    · rw [AddSubgroup.coe_inf]; exact hU.inter hU'
    · funext w
      have e1 := congrFun (hUf u hu.1 h0) w
      have e2 := congrFun (hUg u hu.2 h0) w
      simp only [Heisenberg₂, Pi.add_apply] at e1 e2 ⊢
      rw [mul_add, e1, e2]
    · exact (hf.smooth k L hL hL0 w).add (hg.smooth k L hL hL0 w)
  smul_mem' := by
    intro a f hf
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U, hU, fun u hu h0 => ?_⟩, continuous_const.mul hf.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]; ring
    · funext w
      have e1 := congrFun (hUf u hu h0) w
      simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [mul_left_comm, e1]
    · exact contDiff_const.mul (hf.smooth k L hL hL0 w)

structure IsWeilDatum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (Hth ψ V W)) : Prop where
  std : IsStdChar D ψ (-1)

  hecV : IsHeckeChar D χ

  hecW : IsHeckeChar D χ'

  resV : ResEta D χ V.rank

  resW : ResEta D χ' W.rank
  om_heis : ∀ g h w₀ (Φ Φ' : Hth ψ V W), (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W w₀ Φ →
    (ω (g, h) Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W (actHom V W g h w₀) (ω (g, h) Φ)
  om_aut : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ : Hth ψ V W, (ω (γ, γ') Φ : WA V W → ℂ) 0 = (Φ : WA V W → ℂ) 0
  om_cont : ∀ (Φ : Hth ψ V W) w, Continuous fun p : GA D V × GA D W => (ω p Φ : WA V W → ℂ) w
  om_unit : ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL V W) 𝓕 μ → ∀ p (Φ : Hth ψ V W),
      ∫⁻ w in 𝓕, ‖(ω p Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ
  om_split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : Hth ψ V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) →
        ∀ Φ Φ' : Hth ψ V W, (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W u Φ → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (ω (g, h) Φ) = (r : ℂ) * (splitFac V W χ χ' x y : ℂ) * ℓ Φ

def IsRatAct {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (Hth ψ V W)) : Prop :=
  ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ (Φ : Hth ψ V W) w,
    (ω (γ, γ') Φ : WA V W → ℂ) w = (Φ : WA V W → ℂ) (actHom V W γ⁻¹ γ'⁻¹ w)

def FinCovol (V W : HSp D) : Prop :=
  (∃ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) 𝓕 μ) ∧
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ → μ 𝓕 < ⊤

def thetaK {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))
    (g : GA D V) (h : GA D W) (Φ : Hth ψ V W) : ℂ :=
  (ω (g, h) Φ : WA V W → ℂ) 0

end D7

end Formalism.IndefR.Heis

end
