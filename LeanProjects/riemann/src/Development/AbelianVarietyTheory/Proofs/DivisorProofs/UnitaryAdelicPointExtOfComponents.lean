import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem finiteAdeleRingAway_eq_of_forall_eval_eq {p : ℕ} {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  RestrictedProduct.ext (R := fun v : AwayP p => v.1.adicCompletion ℚ) _ h

theorem basV_repr_map {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (x : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) x) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem ext_of_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf),
    (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  intro p _ G g g' h
  have h1 : ∀ v : AwayP p, Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) =
      Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C))) (h v)
  have h2 : ∀ v : AwayP p, AfP.eval v (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) =
      AfP.eval v (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v))) (h v)
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).ext_elem
    intro i
    apply finiteAdeleRingAway_eq_of_forall_eval_eq
    intro v
    rw [← basV_repr_map, ← basV_repr_map, h1 v]
  · apply Units.ext
    exact finiteAdeleRingAway_eq_of_forall_eval_eq h2

end GlobalTheory.OrbFinAf
