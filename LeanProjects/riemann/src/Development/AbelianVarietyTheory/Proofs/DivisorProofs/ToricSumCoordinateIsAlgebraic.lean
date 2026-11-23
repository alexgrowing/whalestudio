import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.ToricCoordAlg

theorem isAlgebraic_coordIn : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ)
    (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  intro hA K _ _ d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV
  classical
  obtain ⟨hQ, hχ, hfin, S, hS, rfl⟩ := hV
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, GlobalTheory.TwistedTransportProof.coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) =
      ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [GlobalTheory.TwistedTransportProof.coordIn_eq d s κ Ω₀ (S q 0)]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h3 : IsAlgebraic ℚ ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ)) :=
    (GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hχ.2.2.1 htriv q.out).mul
      (GlobalTheory.TwistedTransportProof.isAlgebraic_modF_pow q.out s)
  refine mul_mem (inv_mem ?_) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.ToricCoordAlg
