import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.FinPl.LastInhab

open GlobalTheory.Unf.Inhab

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem eventually_charUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : Pl D in Filter.cofinite, CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ intAt D (· = v) := by
    refine ⟨Ideal.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun w => ?_⟩, ?_⟩
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, h1, sub_self]
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, GlobalTheory.FinPl.compAt, RingHom.comp_apply, h2 _ w.2, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]; exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  obtain ⟨y, hy, hye⟩ : ∃ y, y ∈ intAt D (· = v) ∧ (x : AE D) - 1 = N • y := ⟨_, hv _ ha, e⟩
  refine hker x ⟨h1, h3, h4⟩ ⟨finPart D y, hy.2, ?_⟩
  rw [← RingHom.map_one (finPart D), ← RingHom.map_sub, hye]
  exact (finPart D).toAddMonoidHom.map_nsmul _ _

end GlobalTheory.FinPl.LastInhab

end
