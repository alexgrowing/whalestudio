import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.LocalToGlobal.Columns.RecLevelStep

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

def bar {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (q : PtY ST SG Q y) (w : SG) :
    Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :=
  {v | ∃ z ∈ q.1.2, v = q.1.1.deco.1.be w ((qOf w.1 : X.E) • z)}

def setStab {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {h | ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  inv_mem' {a} ha v := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.MemChart
