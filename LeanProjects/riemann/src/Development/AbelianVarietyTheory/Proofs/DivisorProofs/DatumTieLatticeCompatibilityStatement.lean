import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieLatticeCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_tie_lattice_compatibility : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → ∀ (q : ℕ) (y : Fin q → P.V) (g' : Matrix (Fin q) (Fin q) C), Module.finrank C (P.eigW ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) = q → Submodule.span O (Set.range y) = P.wRec ((embO P.integers ψ).comp (starRingEnd (𝓞 E))) → IsLatBasis C (P.latTSub ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j) → ∃ (m : Fin q → Fin h → C) (k : Matrix (Fin q) (Fin q) C), IsBasisOf C (filQuot C D σ) m ∧ IsBasisOf C (alQuot C D σ) (fun i => ∑ j, k i j • m j) ∧ k.det * g'.det = 1 := by
  first | exact @GlobalTheory.DetInv.Duality.fil_al_dual | exact GlobalTheory.DetInv.Duality.fil_al_dual | (intros; apply GlobalTheory.DetInv.Duality.fil_al_dual <;> assumption)
