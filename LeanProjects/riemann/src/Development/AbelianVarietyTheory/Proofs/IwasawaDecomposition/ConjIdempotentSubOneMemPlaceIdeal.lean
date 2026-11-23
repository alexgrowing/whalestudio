import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

theorem smul_mem_wLf_of_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ wInt X w) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    c • y ∈ Formalism.L2.SG.RowDict.wLf X w := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ha, rfl⟩ := hc
    exact GlobalTheory.Mem.SymFrame.inclE_smul_mem_wLf X w a ha hy
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r ha

theorem mem_wInt_of_mem_idS (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {s : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E}
    (hs : s ∈ idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal) :
    (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  let J : Ideal (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :=
    { carrier := {s | (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [Subring.coe_add]; exact add_mem ha hb
      zero_mem' := by
        show ((0 : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [ZeroMemClass.coe_zero]; exact zero_mem _
      smul_mem' := fun r {a} ha => by
        show ((r * a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        exact (wInt X w).smul_mem r ha }
  have hle : idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show ((oToS X.B.I.F X.B.I.E a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :
      X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
    refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, rfl⟩, ?_⟩
    rw [oToS_coe]
    rfl
  exact hle hs

end GlobalTheory.Mem.SymChar

namespace GlobalTheory.Mem.SymChar

theorem sigA_ew_sub_one_mem_wInt : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ kv hg hne
  set w := D.naut.plGw kv.1 kv.2 with hw
  have h1 : 1 - X.ew - sigA X.B.I X.ew ∈ wInt X w :=
    wInt_of_zmod X kv.1 hg (Formalism.L2.SG.Pf.SatGram.one_sub_ew X)
  let PP := Formalism.L2.SG.Pf.RowDictPf.wB X w
  let e : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  have hidem : e * (1 - e) = 0 := by
    apply Subtype.ext
    show X.ew * (1 - X.ew) = 0
    rw [mul_sub, mul_one, X.ew_idem, sub_self]
  have hr : resS X.B.I.F PP e * resS X.B.I.F PP (1 - e) = 0 := by rw [← map_mul, hidem, map_zero]
  have he : X.ew ∈ wInt X w := by
    rcases mul_eq_zero.1 hr with h | h
    · exact mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP e).1 h)
    · exfalso
      apply hne
      intro y hy
      have := mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP (1 - e)).1 h)
      exact smul_mem_wLf_of_mem_wInt X w this hy
  have e2 : sigA X.B.I X.ew - 1 = -X.ew - (1 - X.ew - sigA X.B.I X.ew) := by ring
  rw [e2]
  exact sub_mem (neg_mem he) h1

end GlobalTheory.Mem.SymChar
