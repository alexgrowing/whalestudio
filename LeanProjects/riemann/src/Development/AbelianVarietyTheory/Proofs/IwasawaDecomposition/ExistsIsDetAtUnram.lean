import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem det_mem_intAE (V : HSp D) (g : GA D V)
    (h : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V),
      finMat D.sp.cm.sig V.gram g *ᵥ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  obtain ⟨L, hL, hfg, hsp⟩ := GlobalTheory.SplitHeckeLabel.exists_coord_lattice V
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  rw [← hL] at h
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hfg hsp h

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add, RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

theorem exists_isDetAt_unram : ∀ (D : D7) (V : HSp D) (ε : AF D.host.F) (e : AE D), IsSplitIdem D e → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∀ g ∈ KsphC V ∅, ∃ x, IsDetAt e V g x ∧ ∀ χ : (AE D)ˣ →* Circle, UnramAt ε χ → χ x = 1 := by
  intro D V ε e he hε g hg
  obtain ⟨h1, h0, -⟩ := he
  have hm : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hf : finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
    change (finHom V g).1 * (finHom V g⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have i1 := det_mem_intAE V g fun y hy => (hg.2.1 y).1 hy
  have i2 := det_mem_intAE V g⁻¹ fun y hy => (hg.2.1 _).2 (by rw [Matrix.mulVec_mulVec, hf, Matrix.one_mulVec]; exact hy)
  generalize (Formalism.L2.Theta.mt V g⁻¹).det = d' at hd i2
  have hx : (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination e * e * hd + (2 - (Formalism.L2.Theta.mt V g).det - d') * h1
  refine ⟨⟨_, _, hx, (mul_comm _ _).trans hx⟩, rfl, fun χ hχ => hχ _ ?_ (part_mem_intAE h1 i1) (part_mem_intAE h1 i2)⟩
  rw [← hε]
  change (e + cA D e) * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
  linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * h1 + ((Formalism.L2.Theta.mt V g).det - 1) * h0

end GlobalTheory.Mem.DetUnit
