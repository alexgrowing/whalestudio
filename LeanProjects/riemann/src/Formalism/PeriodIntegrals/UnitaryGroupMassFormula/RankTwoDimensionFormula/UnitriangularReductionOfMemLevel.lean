import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def NCong (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1})) ∧
    (X.B.I.fmat x - 1) *ᵥ X.z0 ∈ Mo X.B.I X.B.g (Set.range X.e0)

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  calc TR.res v ⟨X.ew, X.ew_int⟩
      = TR.res v ⟨X.ew * ((1 : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
          (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : IntAf X.B.I.F X.B.I.E).2⟩ := by
        congr 1
        ext
        simp
    _ = TR.res v 1 := TR.res_ew v 1
    _ = 1 := map_one _

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  by_cases hb : b
  · rw [if_pos hb] at hZ ⊢
    have hmem : c - X.ew ∈ IntAf X.B.I.F X.B.I.E := sub_mem hc X.ew_int
    have hk := (TR.res_ker ⟨c - X.ew, hmem⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v
    have e : (⟨c - X.ew, hmem⟩ : IntAf X.B.I.F X.B.I.E) = ⟨c, hc⟩ - ⟨X.ew, X.ew_int⟩ := rfl
    rw [e, map_sub, res_ew_one, sub_eq_zero] at hk
    exact hk
  · rw [if_neg hb, sub_zero] at hZ
    rw [if_neg hb]
    exact (TR.res_ker ⟨c, hc⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  obtain ⟨hK, -, -, hc3⟩ := hk
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  have hbb : ∀ i j : Fin D.R.k, i ≠ j → ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.bw j)) := by
    intro i j hij
    have h := X.bw_dual i j
    rwa [if_neg hij, sub_zero] at h
  have key : ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
    intro i j hji
    have hmv : X.B.I.fmat x *ᵥ X.bw j ∈ X.B.I.Lf := K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1
    have hc : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
      hA_int X.B.I (hbwd i) hmv
    have hsub : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤ Qs X.B.I X.B.g (X.bwd i) :=
      le_trans (Mo_mono X.B.I (Set.union_subset_union_right _
          (Set.image_mono (lt_sub (Fin.le_iff_val_le_val.mp hji)))))
        (Mb_Q X.B.I X.B.g X.e0 X.bw X.bwd hbwd (fun i a => dual_beta_reference_congruence i a) hbb i)
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) := hsub (hc3 j)
    have hZ : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
      have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - (if i = j then X.ew else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) +
            hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
        ring
      rw [e]
      exact Z_add X.B.I X.B.g (X.bw_dual i j) h2
    show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
    rw [resT_of_mem TR v hc]
    exact res_of_Z_delta TR v hc (i = j) hZ
  show (∀ i : Fin D.R.k, ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i i = 1) ∧
    ∀ i j : Fin D.R.k, j < i →
      ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
  rw [levi_coe TR hx v]
  exact ⟨fun i => by rw [key i i le_rfl, if_pos rfl],
    fun i j hji => by rw [key i j hji.le, if_neg (ne_of_lt hji).symm]⟩

end K2iff

end PI.UnitaryDimensionFormula.NormCutK
