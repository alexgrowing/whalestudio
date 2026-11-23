import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdapt

noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {K : Type} [Field K] (O : Subring K) {r k : ℕ}

def colv (c : Idx r k → Idx r k → K) (y : Fin k → Idx r k → K) : Idx r k → Idx r k → K
  | Sum.inr (Sum.inl (Sum.inl i)) => y i
  | Sum.inl a => c (Sum.inl a)
  | Sum.inr (Sum.inl (Sum.inr u)) => c (Sum.inr (Sum.inl (Sum.inr u)))
  | Sum.inr (Sum.inr b) => c (Sum.inr (Sum.inr b))

def ofCols (v : Idx r k → Idx r k → K) : Matrix (Idx r k) (Idx r k) K := fun i j => v j i

section Gen

open Classical in

def coefv (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) (i : Fin k) : Idx r k → K :=
  fun t => if IsW t then 0 else g * o (dlH t) i * (l (dlH t))⁻¹

def nMat (o : Idx r k → Fin k → K) (l : Idx r k → K) (g : K) : Matrix (Idx r k) (Idx r k) K :=
  ofCols (colv (fun _ => 0) (fun i => coefv o l g i))

def IntO (M : Matrix (Idx r k) (Idx r k) K) : Prop := ∀ i j, M i j ∈ O

end Gen

end PIW.MassDataColumns
