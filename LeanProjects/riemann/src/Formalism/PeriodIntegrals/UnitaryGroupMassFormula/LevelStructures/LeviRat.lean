import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.StabilizerPreservesComplement

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def LeviComp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w),
      ∀ u, InXperp (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) u →
        lin _ X.B.I.cm.sig X.B.I.J s u - lin _ X.B.I.cm.sig X.B.I.J h u ∈
          spanR (F := X.B.I.F) (Fv X.B.I.F p.1) (frameOf X w).e Set.univ

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem parabolic_unipotent_on_flag {r : ℕ} (P : Frame E n r) {s : HA R σ J} (hs : s ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J s (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e {a | a < b} := by
  have h := hs (Fin.castSucc b)
  have e : F0 P (Fin.castSucc b) = P.e b := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  have hne : a ≠ Fin.last r := fun hl => by
    rw [hl] at ha
    exact absurd ha (not_lt.2 (Fin.castSucc_lt_last b).le)
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 hne
  have ha' : a' < b := Fin.castSucc_lt_castSucc_iff.1 ha
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e {a | a < b}
  rw [e']
  exact Submodule.subset_span ⟨a', ha', rfl⟩

theorem mul_inv_mem_Nsub_of_same_perp_action {r : ℕ} (P : Frame E n r) {s h : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hh : h ∈ Hsub R σ J P)
    (hsh : ∀ u, InXperp R σ J P u → lin R σ J s u - lin R σ J h u ∈ spanR (F := F) R P.e Set.univ) :
    s * h⁻¹ ∈ Nsub R σ J P := by
  have hh' : h⁻¹ ∈ Hsub R σ J P := inv_mem hh
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, stabilizer_fixes_isotropic_e P hh' b]
    exact parabolic_unipotent_on_flag P hs b
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      rw [← stabilizer_fixes_isotropic_e P hh' a, hR_lin]
      exact hv a
    have := hsh _ hu
    rw [lin_lin_inv] at this
    rw [lin_mul]
    exact this

end Gen

theorem leviRat_of (hc : LeviComp) : LeviRat := by
  intro D X w p s hs
  obtain ⟨h, hh, hsh⟩ := hc X w p s hs
  exact ⟨s * h⁻¹, h, mul_inv_mem_Nsub_of_same_perp_action (frameOf X w) hs hh hsh, hh, by group⟩

theorem locLevi_of_comp (hc : LeviComp) (hN : UnipotentIntegralInLevel) : LocLevi :=
  locLevi_of (leviRat_of hc) leviIntH hN

end MassDataLevelSSteps
