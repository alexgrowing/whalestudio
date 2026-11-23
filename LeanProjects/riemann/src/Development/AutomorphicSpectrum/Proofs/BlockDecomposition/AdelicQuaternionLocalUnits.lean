import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.LocalUnit

variable {F : Type} [Field F] [NumberField F] {d β : F}

open Classical in

theorem proj_sum_inc (T : Finset (Pl F)) (c : (u : Pl F) → Kp u) (u : Pl F) :
    proj u (∑ t ∈ T, inc t (c t)) = if u ∈ T then c u else 0 := by
  rw [map_sum]
  by_cases h : u ∈ T
  · rw [if_pos h, Finset.sum_eq_single_of_mem u h]
    · exact proj_inc_same u _
    · intro b _ hb
      exact proj_inc_ne (Ne.symm hb) _
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun t ht => proj_inc_ne (fun e : u = t => h (by rwa [e])) _

theorem q_ext {a b : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) a = qmap (proj u) b) : a = b := by
  ext
  · exact adele_ext fun u => congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imK (h u)

def glue (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + ∑ t ∈ T, inc t ((y t).re - 1), ∑ t ∈ T, inc t (y t).imI, ∑ t ∈ T, inc t (y t).imJ,
    ∑ t ∈ T, inc t (y t).imK⟩

theorem qmap_glue_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F} (h : u ∈ T) :
    qmap (proj u) (glue T y) = y u := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = (y u).re
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_pos h]
    ring
  · change proj u (∑ t ∈ T, inc t (y t).imI) = (y u).imI
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = (y u).imJ
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = (y u).imK
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_pos h]

theorem qmap_glue_not_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F}
    (h : u ∉ T) : qmap (proj u) (glue T y) = 1 := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = 1
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_neg h, add_zero]
  · change proj u (∑ t ∈ T, inc t (y t).imI) = 0
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = 0
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = 0
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_neg h]

theorem exists_adelic_unit : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F))
    (y : (u : Pl F) → (Q d β (Kp u))ˣ),
    ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
      ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  intro F _ _ d β T y
  classical
  have hl : glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).mul_inv
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  have hr : glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).inv_mul
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  exact ⟨⟨_, _, hl, hr⟩, fun u h => qmap_glue_mem T _ h, fun u h => qmap_glue_not_mem T _ h⟩

end GlobalTheory.CompanionTheory.PlaneSA.LocalUnit
