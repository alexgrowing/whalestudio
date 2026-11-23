import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

namespace NormalFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem adjoint_apply_eq_zero {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) {v : E}
    (hv : S v = 0) : LinearMap.adjoint S v = 0 := by
  have e : S (LinearMap.adjoint S v) = LinearMap.adjoint S (S v) := LinearMap.congr_fun h.eq v
  rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, e, hv, map_zero, inner_zero_left]

theorem apply_eq_zero_of_pow {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) (k : ℕ) {v : E}
    (hv : (S ^ k) v = 0) : S v = 0 := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    rw [this, map_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hv
    have h1 := adjoint_apply_eq_zero h (ih hv)
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← LinearMap.adjoint_inner_left, h1, inner_zero_left]

theorem adjoint_sub_smul (T : Module.End ℂ E) (a : ℂ) :
    LinearMap.adjoint (T - a • (1 : Module.End ℂ E)) =
      LinearMap.adjoint T - (starRingEnd ℂ a) • (1 : Module.End ℂ E) := by
  rw [map_sub, LinearEquiv.map_smulₛₗ]
  congr 2
  exact star_one (Module.End ℂ E)

theorem commute_sub_smul {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    Commute (T - a • (1 : Module.End ℂ E)) (LinearMap.adjoint (T - a • (1 : Module.End ℂ E))) := by
  rw [adjoint_sub_smul]
  exact (h.sub_right ((Commute.one_right T).smul_right _)).sub_left ((Commute.one_left _).smul_left a)

theorem maxGenEigenspace_eq {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    T.maxGenEigenspace a = T.eigenspace a := by
  ext v
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨k, hk⟩
    have := apply_eq_zero_of_pow (commute_sub_smul h a) k hk
    simpa [sub_eq_zero] using this
  · intro hv
    exact ⟨1, by simp [hv]⟩

theorem eigenspace_isOrtho {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) {a b : ℂ}
    (hab : a ≠ b) : T.eigenspace a ⟂ T.eigenspace b := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  rw [Module.End.mem_eigenspace_iff] at hv hw
  have h0 : (T - a • (1 : Module.End ℂ E)) v = 0 := by simp [hv]
  have h1 := adjoint_apply_eq_zero (commute_sub_smul h a) h0
  have h2 : inner ℂ v ((T - a • (1 : Module.End ℂ E)) w) = 0 := by
    rw [← LinearMap.adjoint_inner_left, h1, inner_zero_left]
  have h3 : (T - a • (1 : Module.End ℂ E)) w = (b - a) • w := by simp [hw, sub_smul]
  rw [h3, inner_smul_right, mul_eq_zero] at h2
  exact h2.resolve_left (sub_ne_zero.2 hab.symm)

end NormalFamily

theorem normalFamily_orthogonal_decomposition :
    ∀ {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (op : I → Module.End ℂ E), PairComm op → (∀ i, ∃ i', op i' = LinearMap.adjoint (op i)) → (∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i)) ∧ (⨆ x, eigAt op x) = ⊤ ∧ ∀ x x', x ≠ x' → eigAt op x ⟂ eigAt op x' := by
  intro E I _ _ _ op hc hadj
  have hn : ∀ i, Commute (op i) (LinearMap.adjoint (op i)) := fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    rw [← hi']
    exact hc i i'
  have h1 : ∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i) := fun x =>
    iInf_congr fun i => NormalFamily.maxGenEigenspace_eq (hn i) (x i)
  refine ⟨h1, iSup_eigAt_eq_top hc fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i), ?_⟩
  intro x x' hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  rw [h1, h1]
  exact (NormalFamily.eigenspace_isOrtho (hn i) hi).mono (iInf_le _ i) (iInf_le _ i)

end GlobalTheory
