import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.PZ

def ColmezLT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
      IsCrys (P.PD K) (lineRep (K := K) (LL := K) χ⁻¹) ∧
      ∃ e ∈ Dcris (P.PD K) (lineRep (K := K) (LL := K) χ⁻¹),
        Submodule.span ↥K.1 (Set.range fun c : ↥(K0 K) =>
            mulVB (Qp := ℚ_[l]) (K₀ := ↥(K0 K)) (B := P.R.B) (LL := ↥K.1) (V := Fin 1 → ↥K.1) c e) =
          Dcris (P.PD K) (lineRep (K := K) (LL := K) χ⁻¹) ∧
        (φVB (P.PD K) (LL := ↥K.1) (V := Fin 1 → ↥K.1) ^ Module.finrank ℚ_[l] ↥(K0 K)) e = ((π : ↥K.1)) • e

end GlobalTheory.PZ

end
