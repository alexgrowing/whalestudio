import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppGrp

open GlobalTheory.FinPl

theorem placeIdem_mem_idAt {D : D7} {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (P : Pl D → Prop) (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h2⟩ := h
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · exact TensorProduct.zero_tmul _ (1 : D.host.E)
  · have hu : u.1 ≠ v := fun e => u.2 (e ▸ hP)
    show (evalV D.host.F u.1 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h2 u.1 hu, TensorProduct.zero_tmul]

theorem mem_congGrp {D : D7} (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (h : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have h1 := h i j
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
  have : Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this] at h1
  exact h1

theorem mem_grpAt_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  intro D k _ _ _ _ q V g hg P hP
  obtain ⟨ε, h1, h2⟩ := q.above
  refine mem_congGrp V _ g fun i j => ?_
  have h3 := hg i j
  rw [h2] at h3
  rw [← h3]
  exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt h1 P hP)

end GlobalTheory.SuppGrp
