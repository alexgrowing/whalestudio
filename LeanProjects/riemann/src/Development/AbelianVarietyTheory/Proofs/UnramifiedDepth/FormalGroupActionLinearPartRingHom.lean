import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_comp_single {R : Type} [CommRing R] {d : ℕ} (φ ψ : Pt R 1 d)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (comp1 φ ψ) = lin φ * lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 1) ![ψ] (by intro k l; fin_cases k; exact hψ l) (φ i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at h
  rw [Matrix.mul_apply]
  exact h

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_formal_add {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (φ ψ : Pt R 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (F.add φ ψ) = lin φ + lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 2) ![φ, ψ]
    (by intro k l; fin_cases k; exacts [hφ l, hψ l]) (F.F i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [formal_group_coeff_first_linear, formal_group_coeff_second_linear, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.trans (congrArg₂ (· + ·) (_root_.one_mul _) (_root_.one_mul _))

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_zero_point {R : Type} [CommRing R] {d : ℕ} : lin (pt R (n := 1) d 0) = 1 := by
  ext i j
  change MvPowerSeries.coeff _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d) = _
  rw [coeff_X_single, Matrix.one_apply]
  simp [eq_comm]

theorem linPart_act_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  intro R _ d F OE _ act S _ β
  let ρ₀ : OE →+* Matrix (Fin d) (Fin d) R := RingHom.mk'
    { toFun := fun a => lin (act.act a)
      map_one' := by rw [act.one_act, linear_part_zero_point]
      map_mul' := fun a b => by rw [act.mul_act, linear_part_comp_single _ _ (act.const b)] }
    (fun a b => by
      change lin (act.act (a + b)) = lin (act.act a) + lin (act.act b)
      rw [act.add_act, linear_part_formal_add _ _ _ (act.const a) (act.const b)])
  refine ⟨(β.mapMatrix).comp ρ₀, fun a => ⟨?_, rfl⟩⟩
  ext i j
  change β (MvPowerSeries.coeff _ (act.act a i)) =
    MvPowerSeries.coeff _ (MvPowerSeries.map β (act.act a i))
  rw [MvPowerSeries.coeff_map]

end GlobalTheory.ChF
