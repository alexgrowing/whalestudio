import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

section TraceFormSpan

variable {ι K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}

theorem map_mem_span_map_of_mem_span (A : ι → Matrix (Fin a) (Fin a) K)
    {x : Matrix (Fin a) (Fin a) K} (hx : x ∈ Submodule.span K (Set.range A)) :
    x.map (algebraMap K L) ∈
      Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map (algebraMap K L) = algebraMap K L c • y.map (algebraMap K L) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem map_linearForm_mem_span_of_mem_span_map (A : ι → Matrix (Fin a) (Fin a) K)
    {y : Matrix (Fin a) (Fin a) L}
    (hy : y ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)))
    (φ : L →ₗ[K] K) : y.map φ ∈ Submodule.span K (Set.range A) := by
  induction hy using Submodule.span_induction generalizing φ with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    have : ((A g).map (algebraMap K L)).map φ = φ 1 • A g := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
    beta_reduce
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ (hy φ) (hz φ)
  | smul c y _ hy =>
    have : (c • y).map φ = y.map (φ ∘ₗ LinearMap.mulLeft K c) := by
      ext i j; simp
    rw [this]
    exact hy _

theorem trace_map_linearForm_mul (φ : L →ₗ[K] K) (y : Matrix (Fin a) (Fin a) L)
    (m : Matrix (Fin a) (Fin a) K) :
    (y.map φ * m).trace = φ ((y * m.map (algebraMap K L)).trace) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (y i j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem traceForm_span_nondegenerate_map_iff (A : ι → Matrix (Fin a) (Fin a) K) :
    (∀ x ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)),
      (∀ g, (x * (A g).map (algebraMap K L)).trace = 0) → x = 0) ↔
    (∀ x ∈ Submodule.span K (Set.range A), (∀ g, (x * A g).trace = 0) → x = 0) := by
  constructor
  · intro h x hx htr
    have h0 := h _ (map_mem_span_map_of_mem_span A hx) fun g => by
      rw [← Matrix.map_mul, ← AddMonoidHom.map_trace, htr g, map_zero]
    ext i j
    have := congrFun (congrFun h0 i) j
    simpa using this
  · intro h y hy htr
    ext i j
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
    have h0 := h _ (map_linearForm_mem_span_of_mem_span_map A hy φ) fun g => by
      rw [trace_map_linearForm_mul, htr g, map_zero]
    simpa using congrFun (congrFun h0 i) j

end TraceFormSpan

theorem traceForm_span_rep_nondegenerate_mapRep_iff :
    ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K L _ _ _ f a ρ
  letI := f.toAlgebra
  exact traceForm_span_nondegenerate_map_iff (L := L)
    (fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))

end GlobalTheory
