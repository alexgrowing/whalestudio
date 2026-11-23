import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SemiDefs

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem stabilizer_fixes_frame_vector {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [S0, mem_stabT] at hg
  have := hg (Fin.castSucc a)
  simpa [F0, Fin.snoc_castSucc] using this

theorem stabilizer_fixes_frame_span {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P)
    (x : Fin M → R ⊗[F] E) (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J g x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, _, rfl⟩ := hy
    exact stabilizer_fixes_frame_vector R σ J P hg a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem norm_gen {r : ℕ} (P : Frame E M r) (h : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (n : HA R σ J) (hn : n ∈ FrameUnipotentSubgroup R σ J P) : h * n * h⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by
  have hHS := heisenberg_le_stabilizer R σ J P hh
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf] at hn ⊢
  have hS : h * n * h⁻¹ ∈ S0 R σ J P :=
    (S0 R σ J P).mul_mem ((S0 R σ J P).mul_mem hHS hn.2) ((S0 R σ J P).inv_mem hHS)
  refine ⟨?_, hS⟩
  have hnN := hn.1
  show UniC R σ J P.e (h * n * h⁻¹) ∧ ∀ v, InXperp R σ J P v →
    lin R σ J (h * n * h⁻¹) v - v ∈ spanR (F := F) R P.e Set.univ
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [stabilizer_fixes_frame_vector R σ J P hS b, sub_self]
    exact Submodule.zero_mem _
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      have e1 := stabilizer_fixes_frame_vector R σ J P ((S0 R σ J P).inv_mem hHS) a
      rw [← e1, hR_lin]
      exact hv a
    have hnu : lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v ∈ spanR (F := F) R P.e Set.univ :=
      hnN.2 _ hu
    have key : lin R σ J (h * n * h⁻¹) v - v =
        lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) := by
      rw [map_sub, lin_mul, lin_mul, lin_lin_inv]
    rw [key, stabilizer_fixes_frame_span R σ J P hHS _ hnu]
    exact hnu

end Gen

theorem normal_subgroup_holds : NormStep := by
  intro F E _ _ _ _ _ σ _ M J _ r P T _ _ h hh n hn
  exact norm_gen (AF F) σ J P h hh n hn

end PI.VolSemiDirect.W
