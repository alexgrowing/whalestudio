import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel Topology

namespace GlobalTheory.CompanionTheory.LFNe

open Ad3 Ad3.LFS

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def lev (m : ℕ) : Fin 3 → ℤ := ![(m : ℤ), (m : ℤ), 0]

variable (F) in

def tBox (m : ℕ) : Set (Matrix (Fin 2) (Fin 3) F) :=
  {X | ∀ i j, X i j - blk (0 : Fin 2 → F) i j ∈ valBall F (lev m j)}

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_det_eq_one {h : GL (Fin 2) F} (hh : h ∈ GLnLocal.integralGL F 2) (s : ℂ) :
    mp (GeneralLinearGroup.det h) s = 1 := by
  have : modulus ((GeneralLinearGroup.det h : Fˣ) : F) = 1 :=
    modulus_eq_one_iff.2 ⟨Units.ne_zero _, GodementSectionLocal.ord_det_eq_zero hh⟩
  unfold mp
  rw [this]
  simp

variable (F) in

def cong (m : ℕ) : Set (GL (Fin 2) F) :=
  {h | ∀ i j, (h : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F m}

theorem volume_unit_box_ne_zero (ψ : AddChar F Circle) :
    (vol2 ψ).real (GodementSectionLocal.box F 0 : Set (Fin 2 → F)) ≠ 0 := by
  have : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  refine (ENNReal.toReal_ne_zero).2 ⟨?_, (GodementSectionLocal.isCompact_box 0).measure_lt_top.ne⟩
  exact (GodementSectionLocal.isClopen_box 0).isOpen.measure_ne_zero _ ⟨0, zero_mem _⟩

end

end GlobalTheory.CompanionTheory.LFNe
