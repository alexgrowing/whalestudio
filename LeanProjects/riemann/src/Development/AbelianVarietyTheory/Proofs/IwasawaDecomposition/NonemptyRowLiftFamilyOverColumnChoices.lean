import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HdExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFactorisationScalarReferenceTupleEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeightsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.PkExist

theorem rowPk_nonempty : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), Inputs (w.D Z₀) → (w.D Z₀).host.F = maximalRealSubfield (w.D Z₀).host.E → Seed.FrmC.StdLat (Yc (w.D Z₀) 0) → (∀ i, Seed.FrmC.StdLat (Wc (w.D Z₀) i)) → Holds z₀.R z₀.F → (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → Nonempty (RowPk w z₀) := by
  intro B f T w Z₀ hX Wt z₀ hIn hF hY hW hH hWt
  classical
  letI : Algebra z₀.core.Q.c.F (w.D Z₀).what₂.LL := z₀.alg
  let tupT : w.I.ι → TupU w.I (usedOf w.I T Wt) := fun a =>
    if h : ∃ t, ixOf w.I (usedOf w.I T Wt) t = a then h.choose else mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))
  have htt : ∀ t, tupT (ixOf w.I (usedOf w.I T Wt) t) = t := fun t => by
    have h : ∃ t', ixOf w.I (usedOf w.I T Wt) t' = ixOf w.I (usedOf w.I T Wt) t := ⟨t, rfl⟩
    simp only [tupT, dif_pos h]
    exact ixOf_injective w.I _ h.choose_spec
  obtain ⟨y, hy, -⟩ := HdExist.hd_exists (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG z₀.pins hF hY hW
    (ixOf w.I (usedOf w.I T Wt)) tupT htt (ixOf_mu0F w.I _)
  obtain ⟨hLA, hLL⟩ := GlobalTheory.T.definiteFormsAllTuples_coordinateLaws (w.st Z₀) w.px w.I hX z₀.Xg z₀.tr w.ok z₀.good.irr
  have hU := GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq (w.st Z₀) w.px w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr
  have hO : ∀ o : (w.D Z₀).what₂.O, ∃ k : z₀.core.Q.c.F, algebraMap z₀.core.Q.c.F (w.D Z₀).what₂.LL k = (w.D Z₀).what₂.OtoLL o :=
    fun o => z₀.Ks_le _ (SetLike.coe_mem _)
  obtain ⟨p, hpL, ⟨t⟩⟩ := GlobalTheory.T.exists_rowLiftReading_definiteFormCoordinates (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG hO hIn z₀.pins hH y
    (mAU (w.st Z₀) w.I hX z₀.Xg z₀.tr) (mLU (w.st Z₀) w.I hX z₀.Xg z₀.tr) hLA hLL
    (fun b t => by rw [hy]; exact (hU t).1 b) (fun i t => by rw [hy]; exact (hU t).2 i)
  obtain ⟨d, ⟨per⟩⟩ := GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel B f T w Z₀ hX z₀.Xg z₀.tr p (fun a => t.tA true a)
  obtain ⟨W₀, hmu, hkap, hsha⟩ := GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights B f T w hX Wt hWt
  obtain ⟨n, hn⟩ := exists_nums_numOK B w.C (Gc B w.px) p d W₀
  exact ⟨{
    y := y
    tup := fun t => (by rw [hy])
    p := p
    t := t
    mL := fun a j => (by rw [hpL])
    e := d
    per := per
    W₀ := W₀
    mu := hmu
    sha := hsha
    n := n
    kap := fun η hη V S N G' => hkap (p.what₂ d W₀ n η hη) rfl rfl V S N G'
    num := hn }⟩

end GlobalTheory.Mem.R3.Rw.PkExist
