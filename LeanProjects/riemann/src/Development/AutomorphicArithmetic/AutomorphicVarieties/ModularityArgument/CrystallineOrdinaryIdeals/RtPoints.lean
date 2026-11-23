import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.OrdLoc.rtPoints : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG 3 B), GlobalTheory.OrdLoc.On D U r → (∀ a b, QCont l fun g => (r g).mat a b) ∧ D.IsLCr r := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ r hr
  obtain ⟨f, rfl, hf⟩ := hr
  have hle : GlobalTheory.OrdLoc.Icr D U ≤ GlobalTheory.OrdLoc.It D U := le_sInf fun P hP => hP.1.1.2
  have hY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f :=
    (Ideal.le_radical.trans hle).trans hf
  have hC : ∀ a b, QCont l fun g => (push f U.r.hom g).mat a b := fun a b =>
    (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  exact ⟨hC, (GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus hP D U).1 B f hY⟩
