import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_KapUnit_prod (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (e : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ e s'))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem kapUnit_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) := by
  intro s hs
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hΛ := Pf_KapUnit_prod hR c ell H s hp
  have hP := Pf_KapUnit_prod hR c ell (fun _ => m) s hp
  rw [hκ, map_mul, map_mul]
  refine IsUnit.mul ?_ hP
  rw [Formalism.ExponentWindows.abelian₂]
  exact hΛ

end Formalism.MainNotions.N.Ln03.Pf
