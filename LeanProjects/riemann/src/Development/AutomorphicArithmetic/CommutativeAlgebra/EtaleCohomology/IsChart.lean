import Mathlib
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
import GroundTheory.FunctionField.PlaceBridge

noncomputable section
open GroundTheory.FunctionField
open scoped TensorProduct

namespace UpperTheory.Et.Sel

def SelAll (k K : Type) [Field k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) : Set Kˣ :=
  {f | ∀ v : Place k K, (q : ℤ) ∣ v.ord (f : K)}

def FinCls {K : Type} [Field K] (q : ℕ) (S : Set Kˣ) : Prop :=
  ∃ T : Finset Kˣ, ∀ f ∈ S, ∃ t ∈ T, ∃ u : Kˣ, f = t * u ^ q

abbrev inc {k K : Type} [Field k] [Field K] [Algebra k K] (L : Type) [Field L] [Algebra k L] (B : Subalgebra k K) :
    L ⊗[k] B →ₐ[k] L ⊗[k] K :=
  Algebra.TensorProduct.map (AlgHom.id k L) B.val

def LocPow {k K : Type} [Field k] [Field K] [Algebra k K] (q : ℕ) (L : Type) [Field L] [Algebra k L] (B : Subalgebra k K)
    (m : Ideal (L ⊗[k] B)) (F : L ⊗[k] K) : Prop :=
  ∃ s t a b : L ⊗[k] B, s ∉ m ∧ t ∉ m ∧ a ≠ 0 ∧ b ≠ 0 ∧ F * inc L B (s * b ^ q) = inc L B (t * a ^ q)

def IsChart {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) : Prop :=
  Algebra.FiniteType k B ∧ IsDedekindDomain B ∧ ¬ IsField B ∧ IsFractionRing B K ∧
    ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], IsDedekindDomain (L ⊗[k] B) ∧ ¬ IsField (L ⊗[k] B)

def Charts (k K : Type) [Field k] [Field K] [Algebra k K] (q : ℕ) : Prop :=
  ∃ (n : ℕ) (B : Fin n → Subalgebra k K), (∀ i, IsChart (B i)) ∧
    ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L] (F : L ⊗[k] K), F ≠ 0 →
      (∀ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsMaximal → LocPow q L (B i) m F) →
      ∃ (f : Kˣ) (a b : L ⊗[k] K), a ≠ 0 ∧ b ≠ 0 ∧ F * b ^ q = (1 : L) ⊗ₜ[k] (f : K) * a ^ q

def Spz {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] (R : Subalgebra k L) (φ : R →ₐ[k] k)
    (y : L ⊗[k] A) (a : A) : Prop :=
  ∃ y' : R ⊗[k] A, Algebra.TensorProduct.map R.val (AlgHom.id k A) y' = y ∧
    Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) y') = a

end UpperTheory.Et.Sel

end
