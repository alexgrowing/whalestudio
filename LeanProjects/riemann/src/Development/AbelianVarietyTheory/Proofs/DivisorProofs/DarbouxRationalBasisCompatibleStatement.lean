import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxRationalBasisCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_rational_basis_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β κ : Type) [Fintype α] [Fintype β]
  [Fintype κ] [DecidableEq κ] (Bf : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d₀ d₂ : Darboux Bf κ),
  Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₀.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₂.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
    ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  first | exact @GlobalTheory.RatDarboux.exists_rat_symplectic | exact GlobalTheory.RatDarboux.exists_rat_symplectic | (intros; apply GlobalTheory.RatDarboux.exists_rat_symplectic <;> assumption)
