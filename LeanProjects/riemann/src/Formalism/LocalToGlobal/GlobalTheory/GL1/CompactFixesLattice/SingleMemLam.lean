import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lam {k : ℕ} (L : Submodule (SS F E) (Fin k → AE F E)) : Submodule (𝓞 E) (Fin k → E) where
  carrier := {x | (fun i => inclE (F := F) (AF F) (x i)) ∈ L}
  add_mem' := by
    intro a b ha hb
    have h : (fun i => inclE (F := F) (AF F) ((a + b) i)) =
        (fun i => inclE (F := F) (AF F) (a i)) + (fun i => inclE (F := F) (AF F) (b i)) := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((a + b) i)) ∈ L
    rw [h]
    exact L.add_mem ha hb
  zero_mem' := by
    have h : (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) = 0 := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) ∈ L
    rw [h]
    exact L.zero_mem
  smul_mem' := by
    intro r x hx
    have h : (fun i => inclE (F := F) (AF F) ((r • x) i)) =
        (⟨inclE (F := F) (AF F) (r : E), incl_mem_SS ⟨r, rfl⟩⟩ : SS F E) •
          (fun i => inclE (F := F) (AF F) (x i)) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun i => inclE (F := F) (AF F) ((r • x) i)) ∈ L
    rw [h]
    exact L.smul_mem _ hx

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
