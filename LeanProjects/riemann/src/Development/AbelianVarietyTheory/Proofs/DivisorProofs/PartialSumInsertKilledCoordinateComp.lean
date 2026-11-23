import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumCancel

theorem padd_comp_of_kill {S : Scheme.{0}} {B B₂ T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B₂]
    [IsCommMonObj B₂] (p : B ⟶ B₂) [IsMonHom p] (a s : T ⟶ B) (ha : a ≫ p = toUnit T ≫ η[B₂]) :
    padd B a s ≫ p = s ≫ p := by
  unfold padd
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, ha, lift_comp_one_left]

theorem psum_insert_zero_comp : ∀ (S : Scheme.{0}) (B B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₂]
    [IsCommMonObj B₂] (p : B ⟶ B₂) (x : Fin 2 → (T ⟶ B)), IsMonHom p → x 0 ≫ p = toUnit T ≫ η[B₂] →
    ∀ I : Finset (Fin 2), psum B x I ≫ p = psum B x (insert 0 I) ≫ p := by
  intro S B B₂ T _ _ _ _ p x hp hx I
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  all_goals first
    | rw [Finset.insert_eq_of_mem (by decide)]
    | (simp only [psum, List.foldr_cons, List.foldr_nil, show (List.finRange 2) = [0, 1] by decide,
          List.filter_cons, List.filter_nil]
       try simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, decide_true, decide_false,
          Fin.isValue, zero_ne_one, one_ne_zero, or_true, true_or, or_false, if_true, if_false]
       try exact (padd_comp_of_kill p _ _ hx).symm)

end GlobalTheory.MumProd.PsumCancel
