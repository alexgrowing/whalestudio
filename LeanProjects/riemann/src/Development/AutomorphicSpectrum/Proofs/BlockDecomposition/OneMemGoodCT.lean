import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

abbrev lev (R : Type) [CommRing R] (r s : ℕ) : GL (Fin r) R × GL (Fin s) R →* GL (Fin (r + s)) R :=
  GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s)))) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {F | (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) ∧
    (∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      F.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = F.1 g) ∧
    (∀ k ∈ L, finRep E (r + s) k F = F) ∧
    (∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    (∀ g : GA E (r + s), ∃ (C : ℝ) (N : ℕ), ∀ y, ‖F.1 (g * infGL E (r + s) y)‖ ≤ C * height y ^ N) ∧
    ∀ z ∈ J, z F = 0}
  add_mem' := by
    rintro F G ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a1, b1]
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a2, b2]
    · rw [map_add, a3 k hk, b3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).add_mem (a4 g) (b4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      obtain ⟨C', N', h'⟩ := b5 g
      refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
      have hy := one_le_height y
      have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p1 : 0 ≤ height y ^ N := by positivity
      have p2 : 0 ≤ height y ^ N' := by positivity
      change ‖F.1 _ + G.1 _‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      rw [add_mul]
      refine add_le_add ((h y).trans ?_) ((h' y).trans ?_)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p1).trans
          (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C') p2).trans
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    · rw [map_add, a6 z hz, b6 z hz, add_zero]
  zero_mem' := by
    refine ⟨fun x g => rfl, fun γ g => rfl, fun k _ => map_zero _, fun g => ?_, fun g => ⟨0, 0, fun y => ?_⟩,
      fun z _ => map_zero z⟩
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).zero_mem using 1
      funext k
      simp
    · simp
  smul_mem' := by
    rintro c F ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change c • F.1 _ = c • F.1 _
      rw [a1]
    · change c • F.1 _ = c • F.1 _
      rw [a2]
    · rw [map_smul, a3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).smul_mem c (a4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      refine ⟨‖c‖ * C, N, fun y => ?_⟩
      change ‖c • F.1 _‖ ≤ _
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)
    · rw [map_smul, a6 z hz, smul_zero]

theorem one_mem_goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) :
    oneFn E (r + s) ∈ goodCT L (Representation.trivial ℂ (Kinf E (r + s)) ℂ) ∅ := by
  refine ⟨fun x g => rfl, fun γ g => rfl, fun k _ => rfl, fun g => Submodule.subset_span ⟨LinearMap.id, 1, rfl⟩,
    fun g => ⟨1, 0, fun y => ?_⟩, fun z hz => hz.elim⟩
  simp [oneFn]

end GlobalTheory.CompanionTheory.CTFin

end
