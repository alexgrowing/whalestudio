import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}

theorem rho_ff_eq_unit_mul [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (s : ℕ) (hs : s < ell) :
    ∃ ε : (PowerSeries (KsW W s))ˣ, rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g) =
      (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s := by
  obtain ⟨u, hu⟩ := filtration_shape_holds O (baseIdOf hR).Bs ell j M g hj (frobenius_uniformizer_identity hR)
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hε' : rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X := hε
  have hX : IsUnit (rhoL hR c s PowerSeries.X) := (hU s hs).1
  have hp : ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')) := (hU s hs).2
  have hV : IsUnit (rhoL hR c s (u : PowerSeries O) * rhoL hR c s PowerSeries.X ^ M *
      ∏ s' ∈ (Finset.range ell).erase s,
        rhoL hR c s ((baseIdOf hR).Bs.p s' ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s')) := by
    refine ((u.isUnit.map (rhoL hR c s)).mul (hX.pow M)).mul
      (Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_)
    rw [map_pow]
    exact (hp s' (Finset.mem_range.1 (Finset.mem_of_mem_erase hs')) (Finset.ne_of_mem_erase hs')).pow _
  refine ⟨hV.unit * ε ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s, ?_⟩
  rw [hu, map_mul, map_mul, map_pow, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_pow,
    hε', Units.val_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val]
  ring

theorem rho_sub_mem [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) (s : ℕ) (hs : s < ell) :
    ∀ z ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)),
      ∃ y ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0),
        z = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g)) • y := by
  intro z hz
  obtain ⟨ε, hε⟩ := rho_ff_eq_unit_mul Hy hk1b hU hj s hs
  have hle : ordF ell j (baseIdOf hR).Bs.ℓ M g s ≤ ((baseIdOf hR).Bs.ℓ - 1) * M := by
    unfold ordF
    split_ifs <;> omega
  have hTw : (fun i : ℤ => Tw (LL := LL) (D := Dc W T c) 0 (i + -((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ))) =
      Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) := by
    funext i
    unfold Tw
    by_cases h : ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) ≤ i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hz' : tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z ∈
      Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0) :=
    (xi_shift_holds LL (KsW W s) (Dc W T c) _ _ z).2 (by rw [hTw]; exact hz)
  refine ⟨HahnSeries.ofPowerSeries ℤ (KsW W s) ((↑ε⁻¹ : PowerSeries (KsW W s)) *
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) •
      (tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z),
    xi_module_structure LL (KsW W s) (Dc W T c) _ (tw_mono 0) _ _ hz', ?_⟩
  have hmul : (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s *
      ((↑ε⁻¹ : PowerSeries (KsW W s)) *
        PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) =
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M) := by
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [hε, ← mul_smul, ← map_mul, hmul, ← mul_smul, HahnSeries.ofPowerSeries_X_pow, tp,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
