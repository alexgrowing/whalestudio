import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LevelInLatStab

theorem mulVec_mem_of_integral {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B)
    (β : GL (Fin n) B) {P : AddSubgroup (Fin n → A)}
    (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ P, m *ᵥ z ∈ P := by
  intro z hz
  rw [hP] at hz ⊢
  intro i
  rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)

theorem lev_le_latLev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  intro D V β Λ L hβ x hx
  have hp := Formalism.L2.DIV.lev_le_parLev hx
  have hUA := Formalism.L2.DIV.parLev_UA hp
  have hSt := Formalism.L2.DIV.parLev_St hp
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
  obtain ⟨t, ht⟩ := hSt
  let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
  let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
  have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
    simp only [g, MulEquiv.apply_symm_apply, u]
  have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
    have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
    rw [← hg]
    exact h1.symm
  refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
  refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
  constructor
  · intro hy
    exact mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
      (by rw [hmat, ← ht]; rfl) y hy
  · intro hy
    let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
    have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
      ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
      apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
      have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
        (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
      have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
      refine (e.trans ?_).trans e1.symm
      change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
      rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
      (by rw [hm', ← ht']; rfl) _ hy
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LevelInLatStab
