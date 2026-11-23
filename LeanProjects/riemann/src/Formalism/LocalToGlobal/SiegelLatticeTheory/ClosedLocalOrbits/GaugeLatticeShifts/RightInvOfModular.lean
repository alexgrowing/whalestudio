import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EqOneOfZpowMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.RealPlaceAnalysis.FinalF

noncomputable section

open MeasureTheory Topology Filter Matrix
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem inS_pres {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  intro y hy
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : ℕ) < a := hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
    refine Submodule.span_mono ?_ (hg.1 b)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_trans hc hb', rfl⟩
  exact hle hy

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ v : Fin n → ℂ, (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := fun v => by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _,
    by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _⟩

def SG : Subgroup (Formalism.REAL.UJ ε) where
  carrier := SLoc ε e z
  one_mem' := inS_one e z
  mul_mem' {a b} ha hb := inS_mul e z ha hb
  inv_mem' {a} ha := Formalism.L2.SG.RealObj.InfCut.inS_inv _ _ (Formalism.MainNotions.S.uMat a) (Formalism.MainNotions.S.uMat a⁻¹)
    (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' a) ha

theorem coe_SG : (SG ε e z : Set (Formalism.REAL.UJ ε)) = SLoc ε e z := rfl

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  ((Formalism.REAL.uJEmb n ε).1).continuous

theorem SG_closed : IsClosed (SG ε e z : Set (Formalism.REAL.UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (SG ε e z : Set (Formalism.REAL.UJ ε)) =
      (⋂ a : Fin r, (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ e a) ⁻¹' (spanLt e a.1 : Set (Fin n → ℂ))) ∩
        (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ z) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_SG, SLoc, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [e1]
  exact (isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional _).preimage (hc _)).inter
    ((Submodule.closed_of_finiteDimensional _).preimage (hc _))

section Sub

variable {ε e z}

local notation "SS" => (SG ε e z)

instance instLCSG : LocallyCompactSpace SS := (SG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instSCSG : SecondCountableTopology SS := Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem rightInv_of_modular (hΔ : ∀ s : SS, Measure.modularCharacterFun s = 1)
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsHaarS (SLoc ε e z) μ) :
    ∀ s ∈ SLoc ε e z, μ.map (· * s) = μ := by
  intro s hs
  obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hμ
  have hSm : MeasurableSet (SG ε e z : Set (Formalism.REAL.UJ ε)) := (SG_closed ε e z).measurableSet
  have memb : MeasurableEmbedding (Subtype.val : SS → Formalism.REAL.UJ ε) := MeasurableEmbedding.subtype_coe hSm
  set ν : Measure SS := μ.comap Subtype.val with hν
  have hrestr : μ.restrict (SG ε e z : Set (Formalism.REAL.UJ ε)) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hcompl
  have hmapν : ν.map Subtype.val = μ := by
    rw [hν, memb.map_comap, Subtype.range_coe, hrestr]
  have himg : ∀ (t : SS) (A : Set SS), Subtype.val '' ((fun x => t * x) ⁻¹' A) =
      (fun x => (t : Formalism.REAL.UJ ε) * x) ⁻¹' (Subtype.val '' A) := by
    intro t A
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨t * y, hy, rfl⟩
    · rintro ⟨a, ha, hax⟩
      have hxS : x ∈ SS := by
        have : x = ((t⁻¹ * a : SS) : Formalism.REAL.UJ ε) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hax]; group
        rw [this]; exact (t⁻¹ * a).2
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      show t * ⟨x, hxS⟩ ∈ A
      have : t * ⟨x, hxS⟩ = a := Subtype.ext (by simpa using hax.symm)
      rw [this]; exact ha
  have hνinv : ν.IsMulLeftInvariant := by
    refine ⟨fun t => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul t) hA, hν, memb.comap_apply, memb.comap_apply, himg,
      ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]
  have hνfin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hν, memb.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have hνeq : ν = ν.haarScalarFactor Measure.haar • Measure.haar := Measure.isMulLeftInvariant_eq_smul ν Measure.haar
  have hνright : ν.map (· * ⟨s, hs⟩) = ν := by
    rw [hνeq, Measure.map_smul, Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.map_right, hΔ, one_smul]
  calc μ.map (· * s) = (ν.map Subtype.val).map (· * s) := by rw [hmapν]
    _ = (ν.map (· * ⟨s, hs⟩)).map Subtype.val := by
        rw [Measure.map_map (measurable_mul_const s) measurable_subtype_coe,
          Measure.map_map measurable_subtype_coe (measurable_mul_const _)]
        rfl
    _ = μ := by rw [hνright, hmapν]

end Sub

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
