import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

variable {X Z : Scheme.{0}}

def secsSub {E : X.Modules} (S : Subobject E) (V : X.Opens) : Submodule Γ(X, V) Γ(E, V) where
  carrier := secs S V
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

def pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [Z.Over (Spec (.of A))]
    (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E) (e : ℕ) :
    Subobject ((Scheme.Modules.pullback φ).obj E) :=
  imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) ⊔ powSub I _ (e + 1)

def adjMap (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    E ⟶ (Scheme.Modules.pushforward φ).obj (cokernel B.arrow) :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E (cokernel B.arrow) (cokernel.π B.arrow)

def adjKer (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    Subobject E :=
  kernelSubobject (adjMap φ B)

def ChartIn (φ : Z ⟶ X) (V : X.Opens) {N : Type} [AddCommGroup N] [Module Γ(X, V) N]
    (T : Submodule Γ(X, V) N) (x : N) : Prop :=
  ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range (T.subtype.rTensor Γ(Z, U))

def powIdeal (J₀ : X.IdealSheafData) (m : ℕ) : X.IdealSheafData where
  ideal U := J₀.ideal U ^ m
  map_ideal_basicOpen U f := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl

end GlobalTheory.CompanionTheory.GE
