import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LetterHeightDifferenceBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letter_height_difference_bounded : ∀ (D : D7) (O : Setup D), ∃ C : ℝ, ∀ (c : O.s.Comp) (x : (O.var c).X)
    (j : Fin (letters O.S.Dw).length),
    |(adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (((fun _ => false), none, .inr (j : ℕ)) : Sym D.host.E) 1)).ht x -
      (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single (((fun _ => false), none,
        .inl (((letters O.S.Dw).get j).1, (((letters O.S.Dw).get j).2 : ℕ))) : Sym D.host.E) 1)).ht x| ≤ C := by
  first | exact @GlobalTheory.ConcatStep.step | exact GlobalTheory.ConcatStep.step | (intros; apply GlobalTheory.ConcatStep.step <;> assumption)
