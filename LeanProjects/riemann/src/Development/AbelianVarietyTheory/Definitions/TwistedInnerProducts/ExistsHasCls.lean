import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData

open NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TrEll

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} (P : PPol σ r)

def HasCls (k : Type) [CommRing k] [Algebra F k] (J : Matrix (Fin n) (Fin n) E) (γ : HA k σ J) (q : Cls P k) : Prop :=
  ∃ (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ),
    QuotientGroup.mk x = q ∧ gam h = γ

def MapsCls {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (q : Cls P k)
    (q' : Cls P k') : Prop :=
  ∃ (x : plusUnits P k) (x' : plusUnits P k'), QuotientGroup.mk x = q ∧ QuotientGroup.mk x' = q' ∧
    x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1

theorem HasCls.mem {k : Type} [CommRing k] [Algebra F k] {J : Matrix (Fin n) (Fin n) E} {γ : HA k σ J} {q : Cls P k}
    (h : HasCls P k J γ q) : q ∈ XSet P k J := by
  obtain ⟨x, φ, hφ, hq, -⟩ := h
  exact ⟨x, φ, hq, hφ⟩

theorem exists_hasCls {k : Type} [CommRing k] [Algebra F k] {J : Matrix (Fin n) (Fin n) E} {q : Cls P k}
    (h : q ∈ XSet P k J) : ∃ γ, HasCls P k J γ q := by
  obtain ⟨x, φ, hq, hφ⟩ := h
  exact ⟨gam hφ, x, φ, hφ, hq, rfl⟩

variable [NumberField F] [NumberField E]

def polKernel (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ) (x : GAd σ J) : ℂ :=
  ∑ᶠ δ : {δ : GRat σ J // δ.1.1.charpoly = P.1}, f (x⁻¹ * ratEmb σ J δ.1 * x)

end GlobalTheory.TrEll
