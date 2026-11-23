import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
import Development.EtaleCohomology.WeilConjectures.ContinCut
import Development.EtaleCohomology.WeilConjectures.FinQCut
import Development.EtaleCohomology.WeilConjectures.AdicKerPf
import Development.EtaleCohomology.EtaleDuality.FinAdicFin
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.G3

theorem vFin_holds : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hT : ∀ a m, Finite (Ht (l ^ a) (sch.obj X) m i) := fun a m => by
    have : NeZero (l ^ a) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact UpperTheory.Et.etale_finiteness_of_duality (l ^ a) k (by rw [Nat.cast_pow]; exact hl.pow a) p m i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l _ n i (fun a => hT a n)
      (LateralTheory.EWeil.AdicKerPf.AdicKer_of GlobalTheory.EtC.RedCoef.a11 l _ i
        (fun b => LateralTheory.Fin.AdicFin.etale_bockstein_sequence_adic_finiteness GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 l b _ i
          (LateralTheory.EWeil.FinQCut.inv_of_over hl p)) hT n)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.G3

end
