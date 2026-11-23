import Mathlib
import GroundTheory.AutomorphicForms.UnitaryGroupScheme
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.MemRangeIffIsIntegral
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

open NumberField GroundTheory.Automorphic Module TensorProduct Matrix FunctionalEquationAlt

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

section Rational

variable (B : HermitianForm F E V)

def perp (W : Submodule E V) : Submodule E V := W.orthogonalBilin B.toSesq

def nn (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | (∀ u v, B.toSesq (X u) v + B.toSesq u (X v) = 0) ∧ (∀ y, X y ∈ perp B W) ∧
    (∀ y ∈ perp B W, X y ∈ W) ∧ ∀ y ∈ W, X y = 0}

def zz (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | X ∈ nn B W ∧ ∀ y ∈ perp B W, X y = 0}

def NR (W : Submodule E V) : Set (V ≃ₗ[E] V) :=
  {g | g ∈ B.unitaryGroup ∧ (∀ y, g y - y ∈ perp B W) ∧ (∀ y ∈ perp B W, g y - y ∈ W) ∧
    ∀ y ∈ W, g y = y}

def nexp (X : V →ₗ[E] V) : V →ₗ[E] V := 1 + X + (2⁻¹ : E) • (X * X)

def IsIntegralMul (L : Submodule (𝓞 E) V) (c : E) (X : V →ₗ[E] V) : Prop :=
  ∀ y ∈ L, ∃ l ∈ L, X y = c • l

def Gam (L : Submodule (𝓞 E) V) (W : Submodule E V) (g : ℕ) : Set (V ≃ₗ[E] V) :=
  {γ | γ ∈ NR B W ∧ (∀ y, γ y ∈ L ↔ y ∈ L) ∧
    IsIntegralMul L (g : E) ((γ : V →ₗ[E] V) - 1)}

def nnImage (W : Submodule E V) (X : V →ₗ[E] V) : perp B W →ₗ[E] V :=
  X.domRestrict (perp B W)

def hhR (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | (∀ y, T y ∈ W) ∧ ∀ y : perp B W, (y : V) ∈ W → T y = 0}

def Lam1 (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | T ∈ hhR B W ∧ ∀ y : perp B W, (y : V) ∈ L → T y ∈ L}

def Sig (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | X ∈ zz B W ∧ IsIntegralMul L 1 X}

end Rational

section Algebras

variable (B : HermitianForm F E V) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
variable (k : Type) [CommRing k] [Algebra F k]

def coordK (y : V) : ι → k ⊗[F] E :=
  fun i => (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E) (b.repr y i)

def subK (W : Submodule E V) : Submodule (k ⊗[F] E) (ι → k ⊗[F] E) :=
  Submodule.span (k ⊗[F] E) (coordK b k '' (W : Set V))

def gramK : Matrix ι ι (k ⊗[F] E) :=
  (gram B.toSesq b).map (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E)

def nnK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | (X.map (conjBase F E k))ᵀ * gramK B b k + gramK B b k * X = 0 ∧
    (∀ y, X *ᵥ y ∈ subK b k (perp B W)) ∧ (∀ y ∈ subK b k (perp B W), X *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, X *ᵥ y = 0}

def zzK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | X ∈ nnK B b k W ∧ ∀ y ∈ subK b k (perp B W), X *ᵥ y = 0}

def NRK (W : Submodule E V) : Set (GL ι (k ⊗[F] E)) :=
  {g | g ∈ unitaryPoints F E (gram B.toSesq b) k ∧
    (∀ y, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k (perp B W)) ∧
    (∀ y ∈ subK b k (perp B W), ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y = 0}

def nexpK (X : Matrix ι ι (k ⊗[F] E)) : Matrix ι ι (k ⊗[F] E) :=
  1 + X + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X)

end Algebras

def UnipotentAlgebra.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (R : Submodule (𝓞 E) V), IsIsotropic B R →
  let W := espan R
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
    (k : Type) [CommRing k] [Algebra F k],
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, ∀ X'' ∈ nnK B b k W, X * X' * X'' = 0) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      (∀ y ∈ subK b k (perp B W), (X * X') *ᵥ y = 0) ∧ ∀ y, (X * X') *ᵥ y ∈ subK b k W) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, X * X' - X' * X ∈ zzK B b k W) ∧
    (∀ Z ∈ zzK B b k W, ∀ X ∈ nnK B b k W, Z * X = X * Z) ∧
    Set.BijOn (nexpK k) (nnK B b k W)
      ((fun g : GL ι (k ⊗[F] E) => (g : Matrix ι ι (k ⊗[F] E))) '' NRK B b k W) ∧
    ∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      nexpK k X * nexpK k X' =
        nexpK k (X + X' + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X' - X' * X))

def ExpIntegral.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, IsIsotropic B R → ∀ g : ℕ, 1 ≤ g →
  ∀ X ∈ nn B (espan R), IsIntegralMul L (2 * g : E) X →
    ∃ γ ∈ Gam B L (espan R) g, (γ : V →ₗ[E] V) = nexp X

def Lifting.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, SatIn R L → IsIsotropic B R →
    (∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L 1 X ∧ nnImage B (espan R) X = (2 : E) • T) ∧
    ∀ g : ℕ, 1 ≤ g → ∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L (2 * g : E) X ∧ nnImage B (espan R) X = (4 * g : E) • T

section Example

variable (F E)

def hypPlaneSesq : (Fin 2 → E) →ₛₗ[conjHom F E] (Fin 2 → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E (x 0) * y 1 + conj F E (x 1) * y 0)
    (by intros; simp only [Pi.add_apply, map_add]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [show ∀ c, conjHom F E c = conj F E c from fun _ => rfl]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem hypPlaneSesq_apply (x y : Fin 2 → E) :
    hypPlaneSesq F E x y = conj F E (x 0) * y 1 + conj F E (x 1) * y 0 := rfl

def hypPlane : HermitianForm F E (Fin 2 → E) where
  toSesq := hypPlaneSesq F E
  isSymm := ⟨fun x y => by
    change conj F E (hypPlaneSesq F E x y) = hypPlaneSesq F E y x
    simp only [hypPlaneSesq_apply, map_add, map_mul, conj_conj]
    ring⟩
  nonsingular := by
    refine ⟨fun x x' h => ?_, fun φ => ?_⟩
    · have h0 := LinearMap.congr_fun h (Pi.single 1 1)
      have h1 := LinearMap.congr_fun h (Pi.single 0 1)
      simp only [hypPlaneSesq_apply, Pi.single_apply] at h0 h1
      norm_num at h0 h1
      have e0 : x 0 = x' 0 := by simpa using congrArg (conj F E) h0
      have e1 : x 1 = x' 1 := by simpa using congrArg (conj F E) h1
      funext i
      fin_cases i
      · exact e0
      · exact e1
    · refine ⟨![conj F E (φ (Pi.single 1 1)), conj F E (φ (Pi.single 0 1))], ?_⟩
      refine LinearMap.ext fun y => ?_
      have hy : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
        funext i; fin_cases i <;> simp
      conv_rhs => rw [hy]
      simp only [hypPlaneSesq_apply, map_add, map_smul, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, conj_conj]
      ring

def hypLine : Submodule E (Fin 2 → E) := Submodule.span E {Pi.single 0 1}

def hypZ (δ : E) : (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
  δ • (LinearMap.single E (fun _ : Fin 2 => E) 0 ∘ₗ LinearMap.proj 1)

end Example

end UnitaryReduction

end GroundTheory.Heights₂.Theta
