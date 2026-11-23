import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_tie_number_field_point : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actT D) σ) = ⊤ ∧ (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actH D) σ) = ⊤ ∧ (∀ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, ∃ ψ : E →+* C, σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ) ∧ ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → (P.eigV (embO P.integers ψ)).map (φ : P.V →ₗ[C] (Fin h → C)) = eig C (actT D) σ ∧ (P.wRec (embO P.integers ψ)).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = lieSub C D σ ∧ (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = eigPart C (actT D) σ ⊤ ∧ D.lieRank σ = Module.finrank C (P.eigW (embO P.integers ψ)) := by
  first | exact @GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie | exact GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie | (intros; apply GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie <;> assumption)
