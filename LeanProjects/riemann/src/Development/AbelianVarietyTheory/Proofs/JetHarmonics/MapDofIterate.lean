import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.InvDerMap

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d : ℕ} (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_Dof {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) :
    MvPowerSeries.map φ (Dof F u f) =
      Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [Dof, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_Dof_iterate {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ ((Dof F u)^[n] f) =
      (Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)))^[n] (MvPowerSeries.map φ f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_Dof, ih]

end GlobalTheory.InvDerMap

namespace GlobalTheory

theorem map_dmonOf (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (F : Fin d → PS R 2 d)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ (DmonOf F u m f) =
      DmonOf (fun i => MvPowerSeries.map φ (F i)) (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, InvDerMap.map_Dof_iterate, ih]

end GlobalTheory
