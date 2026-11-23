import Mathlib

noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices

abbrev mat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ)

def slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ∑ i ∈ Finset.range (w + 1),
    (LinearMap.toSpanSingleton ℂ ℂ[X]
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i))).comp (lcoeff ℂ i)

def Z1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) where
  carrier := {z | (∀ γ, z γ ∈ degreeLT ℂ (w + 1)) ∧
    ∀ γ δ : Γ, z (γ * δ) = slP w (mat δ) (z γ) + z δ}
  add_mem' := by
    rintro z z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => Submodule.add_mem _ (h1 γ) (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add]
    abel
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    refine ⟨fun γ => Submodule.smul_mem _ c (h1 γ), fun γ δ => ?_⟩
    simp only [Pi.smul_apply, h2, map_smul, smul_add]

def B1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) :=
  LinearMap.range ((LinearMap.pi fun γ : Γ => slP w (mat γ) - LinearMap.id).comp (degreeLT ℂ (w + 1)).subtype)

def IsDCReps (Γ : Subgroup SL(2, ℤ)) (α : Matrix (Fin 2) (Fin 2) ℤ) {ι : Type} (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    Prop :=
  (∀ i, ∃ γ₁ γ₂ : Γ, δ i = mat γ₁ * α * mat γ₂) ∧
    ∀ γ₁ γ₂ : Γ, ∃! i, ∃ γ : Γ, mat γ₁ * α * mat γ₂ = mat γ * δ i

open Classical in

def hk (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    (Γ → ℂ[X]) →ₗ[ℂ] (Γ → ℂ[X]) :=
  LinearMap.pi fun γ : Γ =>
    if h : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) then
      ∑ i, (slP w (δ (h.choose i))).comp (LinearMap.proj (h.choose_spec i).choose)
    else 0

def dg (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, b]

def Lev (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def IsDiam (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) : Prop :=
  σ ∈ CongruenceSubgroup.Gamma0 (N * l) ∧ ((mat σ 1 1 : ℤ) : ZMod N) = d

def tqFam (q : ℕ) (σ : SL(2, ℤ)) : Fin (q + 1) → Matrix (Fin 2) (Fin 2) ℤ := fun i =>
  if (i : ℕ) < q then !![1, (i : ℤ); 0, (q : ℤ)] else mat σ * dg q 1

def ulFam (l : ℕ) : Fin l → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]

def TqZ (Γ : Subgroup SL(2, ℤ)) (w q : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (tqFam q σ)

def UlZ (Γ : Subgroup SL(2, ℤ)) (w l : ℕ) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (ulFam l)

def DdZ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) :=
  hk Γ w (fun _ : Unit => mat σ)

def toGL (g : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : g.det = 0 then 1 else
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix g)
      (by rw [← RingHom.map_det]; simpa using h)

open scoped ModularForm in

def hkF (k : ℤ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ∑ i, f ∣[k] toGL (δ i)

def TqF (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (tqFam q σ) f

def UlF (k : ℤ) (l : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (ulFam l) f

def DdF (k : ℤ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  hkF k (fun _ : Unit => mat σ) f

def eichler (w : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∑ j ∈ Finset.range (w + 1),
    C ((w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) * X ^ j

def per (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : UpperHalfPlane → ℂ) : Γ → ℂ[X] := fun γ =>
  slP w (mat γ) (eichler w f ((γ : SL(2, ℤ)) • UpperHalfPlane.I))

def cj {Γ : Type} (z : Γ → ℂ[X]) : Γ → ℂ[X] := fun γ => (z γ).map (starRingEnd ℂ)

end GlobalTheory.HeckeFamilyMatrices
