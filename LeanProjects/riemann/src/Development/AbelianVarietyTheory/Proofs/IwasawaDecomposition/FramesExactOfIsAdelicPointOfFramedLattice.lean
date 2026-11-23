import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem frExact_of_isPtOf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Θ q hQ g p hp
  have h1 : IsPtOf hc (g * 1) p := by rwa [mul_one]
  have hres : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 (((1 : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (((1 : DiaG E ST) P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) else 0) := by
    intro P r j _
    rw [inv_one, Units.val_one]
    by_cases h : j = r
    · subst h
      rw [Matrix.one_apply_eq, map_one, if_pos rfl]
      simpa using hasRes_coe P.1 1
    · rw [Matrix.one_apply_ne (Ne.symm h), map_zero, if_neg h]
      simpa using hasRes_coe P.1 0
  obtain ⟨hU, hd⟩ := GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul F E hc n ST SG Q g 1 p 1 h1 ⟨DecoF.base E n ∅ ∅ ∅, isPtOf_base hc, rfl⟩
    (fun w _ => map_one _) hres
  rw [DecoSet.dia_one] at hd
  refine ⟨hU, hd, fun P => Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [qdf_at_val]
  show qPi q P ((g : Matrix (Fin n) (Fin n) _) i j) = q.phi P (((qGL n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [qsp_toGLm_apply]
  exact GlobalTheory.T.splitLocalLevel_firstFactor_reads_component hc n q P (hQ P) _ _ (hp.fr P i j)

end GlobalTheory.Mem.Col2.ChEx
