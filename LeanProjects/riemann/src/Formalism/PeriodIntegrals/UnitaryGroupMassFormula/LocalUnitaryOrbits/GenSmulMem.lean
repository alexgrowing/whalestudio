import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem gen_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem gen_mul_mem (a : 𝓞 E) (y : Fv F v ⊗[F] E) (hy : y ∈ OEv (E := E) v) :
    inclR (F := F) (Fv F v) (a : E) * y ∈ OEv (E := E) v := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    rw [← map_mul]
    exact_mod_cast gen_mem v (a * b)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSub : OSub (E := E) v := by
  refine ⟨?_, ?_⟩
  · have := gen_mem (E := E) v 1
    simpa using this
  · intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, -, rfl⟩ := hz
      exact gen_mul_mem v b y hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem gen_smul_mem (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : 𝓞 E) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    inclR (F := F) (Fv F v) (a : E) • x ∈ latLoc (E := E) v Λ := by
  obtain ⟨L, -, rfl⟩ := hL
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hal : a • l ∈ L := L.smul_mem a hl
    have : inclR (F := F) (Fv F v) (a : E) • ratV (F := F) (Fv F v) l = ratV (F := F) (Fv F v) (a • l) := by
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul, ← map_mul]
      rfl
    rw [this]
    exact Submodule.subset_span ⟨_, hal, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSmul : OSmul v Λ := by
  intro hL c hc x hx
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, -, rfl⟩ := hz
    exact gen_smul_mem v Λ hL b x hx
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ hc hc' => rw [add_smul]; exact Submodule.add_mem _ hc hc'
  | smul r c _ hc => rw [smul_assoc]; exact Submodule.smul_mem _ r hc

end PI.OmLocU.Orb
