import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem span_natCast_pow_eq_bot_of_isNilpotent (p : ℕ) (R : Type) [CommRing R]
    (h : IsNilpotent (p : R)) : ∃ N : ℕ, Ideal.span {(p : R)} ^ N • (⊤ : Submodule R R) = ⊥ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [Ideal.span_singleton_pow, hN, smul_eq_mul, Ideal.mul_top]
  simp

theorem isAdicComplete_span_natCast_of_isNilpotent :
    ∀ (p : ℕ) (R : Type) [CommRing R], IsNilpotent (p : R) →
      IsAdicComplete (Ideal.span {(p : R)}) R := by
  intro p R _ h
  obtain ⟨N, hN⟩ := span_natCast_pow_eq_bot_of_isNilpotent p R h
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have := hx N
    rwa [hN, SModEq.bot] at this
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have h1 := hf hn
      rw [hN, SModEq.bot] at h1
      rw [h1]
end GlobalTheory
