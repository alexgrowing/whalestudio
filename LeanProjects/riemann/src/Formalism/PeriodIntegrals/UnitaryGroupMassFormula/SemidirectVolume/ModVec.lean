import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianIsotropicProjComplement

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable (D : Dat A n r)

def L (w : Fin r → n → A) (s : Fin r → Fin r → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ b, (D.hL (D.e b)).smulRight (w b + ∑ a, s a b • D.e a) -
    ∑ a, ((D.hL (w a)).comp D.pW).smulRight (D.e a)

theorem L_apply (w : Fin r → n → A) (s : Fin r → Fin r → A) (v : n → A) :
    D.L w s v = v + ∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) (D.pW v) • D.e a := by
  simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply]
  rfl

def PerpX (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e)

variable {D}

theorem pX_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    D.pX x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [pX_apply]
    simp [fe H]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem h_W_e (H : D.Hyp) {w : n → A} (hw : IsW D w) (a : Fin r) : D.h w (D.e a) = 0 := by
  rw [h_symm H (D.e a) w, hw.1 a, map_zero]

theorem h_W_span (H : D.Hyp) {w : n → A} (hw : IsW D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h_W_e H hw a
  | zero =>
    change D.hL w 0 = 0
    exact map_zero _
  | add x y _ _ hx hy =>
    change D.hL w (x + y) = 0
    rw [map_add]
    change D.h w x + D.h w y = 0
    rw [hx, hy, add_zero]
  | smul c x _ hx =>
    change D.hL w (c • x) = 0
    rw [map_smul]
    change c • D.h w x = 0
    rw [hx, smul_zero]

theorem N_f (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r) :
    S (D.f b) = D.f b + D.pW (S (D.f b)) + ∑ a, D.h (D.f a) (S (D.f b)) • D.e a := by
  have hpW : D.pW (S (D.f b)) = S (D.f b) - D.pU (S (D.f b)) := by simp [pW]
  have hXv : D.pXv (S (D.f b)) = D.f b := by
    rw [pXv_apply]
    have he : ∀ a, D.h (D.e a) (S (D.f b)) = if a = b then 1 else 0 := fun a => by
      rw [← hS.1 a, hU, H.ef]
    simp [he]
  have hz0 : D.h D.z (S (D.f b)) = 0 := by
    rw [← hS.2, hU, h_symm H, H.fz, map_zero]
  have hz : D.pz (S (D.f b)) = 0 := by
    rw [pz_apply, hz0, mul_zero, zero_smul]
  rw [hpW, pU_apply, hXv, hz, pX_apply]
  abel

end Dat

end PI.VolSemiDirect.W.PG
