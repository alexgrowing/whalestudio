import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct Matrix

namespace GlobalTheory.RowLev

open Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin IsDedekindDomain

theorem redMat0_of_actsAs : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  intro I N p w fr x hx M hM
  have hp : p.Prime := fr.prime
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p :=
    (Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)
  have h1 : ∀ u ∈ lamAf (F := I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by
    refine fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu
    rw [DictLat.iv_smulE]
    exact Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)
  have h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')
    refine Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha
    · rintro z ⟨b, hb, e⟩
      show (z : I.E ⊗[I.F] Af I.F) • v ∈ _
      rw [e]
      exact smul_mem I w hb hv
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]; exact add_mem ha hb
    · intro s a _ ha
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s ha
  have hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F := I.F) (wLat0 I w) :=
    fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩
  choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)
  choose b hbL hb using fun i => dense I w hp hcard (y i).2
  let B : Fin N → I.Lf := fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩
  have hB : ∀ i, fr.c (B i) = Pi.single i 1 := by
    intro i
    have e : fr.c (y i - B i) = 0 := (hz _).2 (hb i)
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  have hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_intCast]
  have hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_natCast]
  refine ⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩
  · let Z : I.Lf := ⟨iv I z, DictLat.iv_mem I hz'⟩
    let c : Fin N → ℤ := fun j => ((fr.c Z j).val : ℤ)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero]
      simp only [hci, hB]
      funext k
      simp [c, Finset.sum_apply, Pi.single_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    simp [Z, B, Submodule.coe_sum]
    rfl
  · let V : I.Lf := ⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩
    have hV : fr.c V = M *ᵥ Pi.single i 1 := by rw [← hB i]; exact hM (B i) V.2
    have e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero, hV]
      simp only [hcn, hB, ZMod.natCast_zmod_val]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)
    rw [SubringClass.coe_natCast]
    rfl

end GlobalTheory.RowLev
