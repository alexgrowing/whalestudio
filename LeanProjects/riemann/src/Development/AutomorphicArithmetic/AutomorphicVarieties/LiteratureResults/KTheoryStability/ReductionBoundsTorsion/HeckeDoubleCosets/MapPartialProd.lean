import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

variable {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction H Y]

theorem map_partialProd {M M' : Type} [Monoid M] [Monoid M'] (f : M →* M') {m : ℕ} (g : Fin m → M)
    (j : Fin (m + 1)) : f (Fin.partialProd g j) = Fin.partialProd (fun i => f (g i)) j := by
  induction j using Fin.inductionOn with
  | zero => simp
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, map_mul, ih]

theorem ev_eq (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ F y z = Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun j => ρ (Fin.partialProd g j) • y) z := by
  simp [ev, Finsupp.linearCombination_apply, smul_eq_mul]

theorem ev_add (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z z' : Chn G m) :
    ev ρ F y (z + z') = ev ρ F y z + ev ρ F y z' := by
  simp only [ev_eq, map_add]

theorem ev_sub (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z z' : Chn G m) :
    ev ρ F y (z - z') = ev ρ F y z - ev ρ F y z' := by
  simp only [ev_eq, map_sub]

theorem ev_smul (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (c : ℝ) (z : Chn G m) :
    ev ρ F y (c • z) = c * ev ρ F y z := by
  rw [ev_eq, ev_eq, map_smul, smul_eq_mul]

theorem ev_zero (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) : ev ρ F y 0 = 0 := by
  simp [ev]

theorem ev_single (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (g : Fin m → G) (a : ℝ) :
    ev ρ F y (Finsupp.single g a) = a * F fun j => ρ (Fin.partialProd g j) • y := by
  simp [ev]

theorem ev_cmap (ρ : G →* H) (f : K →* G) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn K m) :
    ev ρ F y (cmap f m z) = ev (ρ.comp f) F y z := by
  simp only [cmap, Finsupp.lmapDomain_apply, ev]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  exact Finsupp.sum_congr fun g _ => by simp [MonoidHom.comp_apply, map_partialProd]

end PositivityTheory.KB.AffineStabilizerVanishing

end
