import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_sub_tower {B : ℕ → Type} [∀ n, AddCommGroup (B n)] (r : ∀ n, B (n + 1) → B n)
    (hr : ∀ n, Function.Surjective (r n)) (a : ∀ n, B n) :
    ∃ h : ∀ n, B n, ∀ n, a n = h n - r n (h (n + 1)) := by
  choose s hs using hr
  refine ⟨fun n ↦ Nat.rec (motive := B) 0 (fun n x ↦ s n (x - a n)) n, fun n ↦ ?_⟩
  simp only [hs, sub_sub_cancel]

theorem nonempty_dat (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) : Nonempty (Dat t c) := by
  obtain ⟨f, hf⟩ := CatCoh.H1.mk_surjective _ c.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R A f (by rw [hf]; exact c.2)
  obtain ⟨h, hh⟩ := exists_sub_tower (B := fun n ↦ G.A n) (fun n ↦ G.res n) (fun n ↦ G.res_surjective n)
    (fun n ↦ fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))
  exact ⟨⟨f, hf, g, hg, h, hh⟩⟩

end GlobalTheory.PtExt
