import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.V0

section Abs

variable {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]

def opE (ρ : Representation R G W) (a : G →₀ ℤ) : Module.End R W := a.sum fun g c => c • ρ g

def ePart (ρ : Representation R G W) (a : G →₀ ℤ) (N : ℕ) : Submodule R W := LinearMap.ker (opE ρ a - (N : Module.End R W))

structure IsE (K₀ K₁ : Subgroup G) (a : G →₀ ℤ) (N : ℕ) : Prop where
  supp : ∀ g ∈ a.support, g ∈ K₀
  norm : ∀ g ∈ K₀, ∀ u ∈ K₁, g⁻¹ * u * g ∈ K₁
  sq : ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W), ∀ v ∈ fixd ρ K₁,
    opE ρ a (opE ρ a v) = N • opE ρ a v

end Abs

section Loc

variable {k : Type} [Field k] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

def chr (ψ : AddChar k Circle) (t : Fin n → k) (u : GL (Fin n) k) : ℂ :=
  (ψ (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, t p.1 * (u : Matrix (Fin n) (Fin n) k) p.1 p.2) : ℂ)

def IsMirL (p : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 = n → (p : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) i j

def KirF (τ : Representation ℂ (GL (Fin n) k) W) (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) ∧ ∀ v, (∀ p, IsMirL p → l (τ p v) = 0) → v = 0

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Kir (τ : Representation ℂ (GL (Fin n) k) W) : Prop :=
  ∃ (ψ : AddChar k Circle) (l : W →ₗ[ℂ] ℂ), Continuous ψ ∧ ψ ≠ 1 ∧ KirF τ ψ (fun _ => 1) l

def Lev1 (ψ : AddChar k Circle) : Prop :=
  Continuous ψ ∧ (∀ x : k, valuation k x < 1 → ψ x = 1) ∧ ∃ x : k, valuation k x ≤ 1 ∧ ψ x ≠ 1

def isoPart (τ : Representation ℂ (GL (Fin n) k) W) (ψ : AddChar k Circle) (t : Fin n → k) : Submodule ℂ W :=
  fixd τ (Kc k n 1) ⊓ ⨅ (u : GL (Fin n) k) (_ : u ∈ unipB k (Fin n) ∧ u ∈ KO k (Fin n)), Module.End.eigenspace (τ u) (chr ψ t u)

end Loc

def KirMove : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), Kir τ → ∀ (ψ : AddChar k Circle) (t : Fin n → k), Continuous ψ → ψ ≠ 1 →
    (∀ i, t i ≠ 0) → ∃ l, KirF τ ψ t l

def IsoNe : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), GlobalTheory.PRep.IsSmooth τ → ∀ (ψ : AddChar k Circle) (t : Fin n → k)
    (l : W →ₗ[ℂ] ℂ), Lev1 ψ → (∀ i, valuation k (t i) = 1) → KirF τ ψ t l → fixd τ (Kc k n 1) ≠ ⊥ → isoPart τ ψ t ≠ ⊥

def IsoLe : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W) (ψ : AddChar k Circle) (t : Fin n → k)
    (l : W →ₗ[ℂ] ℂ), Lev1 ψ → (∀ i, valuation k (t i) = 1) → KirF τ ψ t l → ∀ v ∈ isoPart τ ψ t, l v = 0 → v = 0

def EOp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    ∃ (ψ : AddChar k Circle) (a : GL (Fin n) k →₀ ℤ) (j : ℕ) (T : Finset (Fin n → k)), Lev1 ψ ∧
      IsE (KO k (Fin n)) (Kc k n 1) a (Nat.card 𝓀[k] ^ j) ∧ T.Nonempty ∧ (∀ t ∈ T, ∀ i, valuation k (t i) = 1) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W),
        Module.rank ℂ ↥(fixd τ (Kc k n 1) ⊓ ePart τ a (Nat.card 𝓀[k] ^ j)) = ∑ t ∈ T, Module.rank ℂ (isoPart τ ψ t)

def LocE : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    ∃ (a : GL (Fin n) k →₀ ℤ) (j D : ℕ), IsE (KO k (Fin n)) (Kc k n 1) a (Nat.card 𝓀[k] ^ j) ∧ 0 < D ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), GlobalTheory.PRep.IsSmooth τ → Kir τ →
        fixd τ (Kc k n 1) ≠ ⊥ → Module.rank ℂ ↥(fixd τ (Kc k n 1) ⊓ ePart τ a (Nat.card 𝓀[k] ^ j)) = D

def KirCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → Kir σ.ρ

end UpperTheory.V.Z.Desc.V0
