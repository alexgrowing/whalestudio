import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

def lstd (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) where
  carrier := {y | ∀ i, y i ∈ intLoc F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  neg_mem' hx i := neg_mem (hx i)

def HWFin : Prop :=
  ∀ (D : D7) (n : ℕ) (w : G D n), mat w = blk4 0 1 (-1) 0 → ∀ nb : hermA D n → G D n, PositivityTheory.PfSWUS.IsNMap nb →
  ∀ (b : hermA D n) (p k : G D n), p ∈ P D n → k ∈ K D n → w * nb b = p * k →
  ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 →
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)),
    lam.IsAddHaarMeasure →
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (lstd D.host.F D.host.E n v) (lstd D.host.F D.host.E n v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) =
      ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ)⁻¹

def HWInf : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (w : G D n), mat w = blk4 0 1 (-1) 0 →
  ∀ nb : hermA D n → G D n, PositivityTheory.PfSWUS.IsNMap nb →
  ∀ (b : hermA D n) (p k : G D n), p ∈ P D n → k ∈ K D n → w * nb b = p * k →
  ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 →
    (((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ)) *
      PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (fun _ => 1) (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1) = 1

def LstdStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (lstd F E n v)) ∧
    ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      (lstd F E n v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v

end PositivityTheory.PfSWUS.SwFockk

end
