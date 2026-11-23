import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.SSCont

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem mem_imAlg_iff (r : Γ →* GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ PI.SSAscent.UnitaryGroupMassFormula.imAlg r ↔
      x ∈ Submodule.span k (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) := by
  have h : (Submonoid.closure (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) :
      Set (Matrix (Fin n) (Fin n) k)) = Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) := by
    have e : (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) =
        (MonoidHom.mrange ((Units.coeHom _).comp r) : Set (Matrix (Fin n) (Fin n) k)) := by
      ext y
      simp
    rw [e, Submonoid.closure_eq]
  rw [PI.SSAscent.UnitaryGroupMassFormula.imAlg, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, h]

theorem exists_linear_of_trace [CharZero k] (r : Γ →* GL (Fin n) k) (hr : IsSSRep r) :
    ∃ (m : ℕ) (c : Fin m → Γ) (ψ : (Fin m → k) →ₗ[k] Matrix (Fin n) (Fin n) k),
      ∀ g, (r g : Matrix (Fin n) (Fin n) k) =
        ψ fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ n r hr
  set S : Set (Matrix (Fin n) (Fin n) k) := Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) with hS
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose c hc using hf
  let φ : Submodule.span k S →ₗ[k] (Fin (Module.finrank k (Submodule.span k S)) → k) :=
    LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ (LinearMap.mulRight k (f i)) ∘ₗ
      (Submodule.span k S).subtype
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x.1 ((mem_imAlg_iff r _).2 x.2) fun y hy => ?_
    have hy' := (mem_imAlg_iff r _).1 hy
    rw [← hS, ← hspan] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [φ] using congrFun hx i
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨_, c, (Submodule.span k S).subtype ∘ₗ ψ, fun g => ?_⟩
  let x : Submodule.span k S := ⟨r g, Submodule.subset_span ⟨g, rfl⟩⟩
  have h1 : (fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) = φ x := by
    funext i
    simp [φ, x, ← hc i]
  have h2 : ψ (φ x) = x := LinearMap.congr_fun hψ x
  rw [h1, LinearMap.comp_apply, h2]
  rfl

theorem continuous_of_continuous_trace : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsSSRep r → Continuous (fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → Continuous r := by
  intro Γ k _ _ _ _ _ _ _ n r hr ht
  obtain ⟨m, c, ψ, h⟩ := exists_linear_of_trace r hr
  have hc : Continuous fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [funext h]
    exact ψ.continuous_on_pi.comp (continuous_pi fun i => ht.comp (continuous_mul_const (c i)))
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

end GlobalTheory.SSCont
