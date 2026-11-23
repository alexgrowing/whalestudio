import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaExponentHnfGL
import GroundTheory.AutomorphicForms.SphericalIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardHermiteDataPowerQStatement
import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries

open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

instance finite_deg (k : ℕ) : Finite {l : Fin n → ℕ // ∑ i, l i = k} := by
  refine Finite.of_injective (fun l => (⟨l.1, Finset.Nat.mem_antidiagonalTuple.2 l.2⟩ :
    (Finset.Nat.antidiagonalTuple n k : Set (Fin n → ℕ)))) ?_
  intro x y h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

instance finite_hdata (l : Fin n → ℕ) : Finite (HData F n l) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [GlobalTheory.T.card_hermite_data_power_q F n l]
  exact pow_ne_zero _ (Spherical.qF_pos (F := F)).ne'

instance finite_hdataDeg (k : ℕ) : Finite (HDataDeg F n k) := inferInstance

end GlobalTheory.HermCount
