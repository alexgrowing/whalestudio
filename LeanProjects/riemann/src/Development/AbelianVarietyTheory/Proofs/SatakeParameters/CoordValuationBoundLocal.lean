import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GenProj

def baseOfGBase {p : ℕ} [Fact p.Prime] {D : Datum p} (gb : GBase D.toG ℂ) : Base D ℂ where
  unit k hk := by
    refine isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr ?_)
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.mp hk)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    haveI : CharZero k := (RingHom.charZero_iff β.injective).mp inferInstance
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (CharP.cast_eq_zero k p)

theorem isProjOver_genModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ X : GenModel gb N, IsProjOver X.s := by
  intro p _ D hC gb N hN hNp X
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D ℂ (baseOfGBase gb) N hN hNp
  have hM : IsProjOver M.s := GlobalTheory.UPel.HT.Model.isProjOver_of_compactB p D ℂ (baseOfGBase gb) N hN hNp hC M
  obtain ⟨j, _, hj, hjs, _⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D ℂ (baseOfGBase gb) ℂ (RingHom.id ℂ) gb rfl (fun _ => rfl) N hN hNp M X
  rw [← hjs]
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id ℂ) hM)

end GlobalTheory.UPel.HT.GenProj
