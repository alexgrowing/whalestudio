import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevResXi

theorem xiR_eq_map_resChar : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ (t : TupU I U) (PP : HeightOneSpectrum (𝓞 X.B.fields.E)), PP ∈ Formalism.L2.Col.QE I.sel t.1 →
      ∀ c : (𝓞 X.B.fields.E ⧸ PP.asIdeal)ˣ, L.xiR t PP c = Units.map X.toD7.what₂.embLL.toMonoidHom
        (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) PP c) := by
  intro X px I U L hI hV hL t PP hPP c
  have hQ : PP ∈ L.Q t := by
    rw [hL.Q t]
    change PP ∈ Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t))
    rw [tup_ixOf]
    exact hPP
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ PP.asIdeal)
  have hn : b ∉ PP.asIdeal := fun hm => c.ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 hm)
  have h0 : (b : X.B.fields.E) ≠ 0 := fun e => hn ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  have h1 := hL.is.xiR t PP hQ b (Units.mk0 _ h0) c rfl hb.symm
  have ht : ∀ P, (I.xi (ixOf I U t)).TameAt P := fun P => hL.xiH t ▸ hL.is.xi_tame t P
  have h2 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads (ixOf I U t)) ht PP c b (Units.mk0 _ h0) rfl hb
  rw [tup_ixOf] at h2
  rw [hL.xiH t] at h1
  refine Units.ext ?_
  rw [h1]
  exact h2.symm

end GlobalTheory.Mem.LevResXi
