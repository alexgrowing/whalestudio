import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem coord_unit_smul {F : Type} [Field F]
    (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      (τ ((ε : 𝓞 F) : F) : ℂ) * _root_.GlobalTheory.HilbFam.coord b a x τ := by
  have hsmul : ∀ j, (ε • x) j = ((ε : 𝓞 F) : F) * x j := fun j => rfl
  simp only [_root_.GlobalTheory.HilbFam.coord, hsmul, map_mul, Complex.ofReal_mul]
  ring

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.gTerm_unit_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (σ : ℂ) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (ε : (𝓞 F)ˣ) (x : Fin 2 → F), Even k → _root_.GlobalTheory.HilbFam.gTerm k σ b a (ε • x) = _root_.GlobalTheory.HilbFam.gTerm k σ b a x := by
  intro F _ _ _ k σ b a ε x hk
  have hprod : ∏ τ, _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.HilbFam.coord b a x τ := by
    simp only [coord_unit_smul, Finset.prod_mul_distrib]
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb]
  have hN : Algebra.norm ℚ ((ε : 𝓞 F) : F) = 1 ∨ Algebra.norm ℚ ((ε : 𝓞 F) : F) = -1 :=
    abs_eq (zero_le_one) |>.mp (NumberField.Units.norm F ε)
  unfold _root_.GlobalTheory.HilbFam.gTerm
  rw [hprod]
  rcases hN with hN | hN <;> simp [hN, hk.neg_pow]

end GlobalTheory.HilbFam
