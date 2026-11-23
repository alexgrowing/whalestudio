import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.DirScale

variable {R : Type} [CommRing R] {d : ℕ}

theorem dof_smul_dir (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (f : PS R 1 d) :
    Dof F (c • u) f = C c * Dof F u f := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem dof_iter_C_mul (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (r : R) (f : PS R 1 d) :
    (Dof F u)^[n] (C r * f) = C r * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GE.dof_C_mul, ih]

theorem dof_iter_smul_dir (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    (Dof F (c • u))^[n] f = C (c ^ n) * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, dof_smul_dir, dof_iter_C_mul,
      pow_succ, map_mul, mul_assoc]

theorem foldr_smul_dir (F : Fin d → PS R 2 d) {ι : Type} (c : ι → R) (u : ι → Fin d → R)
    (m : ι → ℕ) (f : PS R 1 d) (L : List ι) :
    L.foldr (fun l g => (Dof F (c l • u l))^[m l] g) f =
      C (L.map fun l => c l ^ m l).prod * L.foldr (fun l g => (Dof F (u l))^[m l] g) f := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, dof_iter_smul_dir, dof_iter_C_mul, map_mul, mul_assoc]

theorem dmonOf_smul_dir : ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (ι : Type)
    [Fintype ι] (c : ι → R) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d),
    DmonOf F (fun l => c l • u l) m f = C (∏ l, c l ^ m l) * DmonOf F u m f := by
  intro R _ d F ι _ c u m f
  unfold DmonOf
  have h : ((Finset.univ : Finset ι).toList.map fun l => c l ^ m l).prod = ∏ l, c l ^ m l :=
    Finset.prod_map_toList _ _
  rw [← h]
  exact foldr_smul_dir F c u (fun l => m l) f _

end GlobalTheory.DirScale
