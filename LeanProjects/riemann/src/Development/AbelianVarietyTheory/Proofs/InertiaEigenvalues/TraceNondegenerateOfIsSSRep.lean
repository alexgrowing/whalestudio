import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceFormNondegenerate
open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem trace_nondegenerate_of_isSSRep {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ spanAlg ρ)
    (htr : ∀ g, (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).trace = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4; revert Γ k h_2 h_3 h_4 n ρ hρ x hx htr; exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate)
  | exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | (apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate ..)

theorem isSSRep_mapRep :
    ∀ (Γ k k' : Type) [Group Γ] [Field k] [Field k'] [CharZero k] (ι : k →+* k') (n : ℕ)
      (ρ : Γ →* GL (Fin n) k), IsSSRep ρ → IsSSRep (mapRep ι ρ) := by
  intro Γ k k' _ _ _ _ ι n ρ hρ
  let _ : Algebra k k' := ι.toAlgebra
  have hφι : ∀ (φ : k' →ₗ[k] k) (c : k') (r : k), φ (c * ι r) = φ c * r := by
    intro φ c r
    rw [mul_comm c, mul_comm (φ c), ← smul_eq_mul r, ← map_smul]
    rfl
  have hent : ∀ g i j, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') i j =
      ι (((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := fun _ _ _ => rfl
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  have hmem : ∀ φ : k' →ₗ[k] k, x.map φ ∈ spanAlg ρ := by
    clear htr
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro φ
      have : ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k').map φ =
          φ 1 • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
        ext i j
        rw [Matrix.map_apply, hent, Matrix.smul_apply, smul_eq_mul, ← hφι, one_mul]
      rw [this]
      exact (spanAlg ρ).smul_mem (Submodule.subset_span ⟨g, rfl⟩) _
    | zero =>
      intro φ
      have : (0 : Matrix (Fin n) (Fin n) k').map φ = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      intro φ
      have : (y + z).map φ = y.map φ + z.map φ := by ext i j; simp
      rw [this]; exact add_mem (hy φ) (hz φ)
    | smul c y _ hy =>
      intro φ
      exact hy (φ ∘ₗ LinearMap.mulLeft k c)
  have hzero : ∀ φ : k' →ₗ[k] k, x.map φ = 0 := by
    intro φ
    refine trace_nondegenerate_of_isSSRep ρ hρ _ (hmem φ) fun g => ?_
    have := congrArg φ (htr g)
    rw [map_zero] at this
    rw [← this]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, hent, hφι, Matrix.map_apply]
  ext i j
  rw [Matrix.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  exact congrFun (congrFun (hzero φ) i) j

end GlobalTheory.TraceSemisimple
