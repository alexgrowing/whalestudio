import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.GlFirstLineDividedPowers
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.SwappedHighestWeightNeZero
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Spread
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Descent
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Ascent
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Assemble

namespace Formalism.InvariantFactorPaths.INST.Top

theorem spreadTop : SpreadTop := spread_top_holds
theorem spreadSquare : SpreadSquare := spread_square_holds
theorem rowGlOne : RowGlOne := gl_one_first_line_action
theorem rowGlDiv : RowGlDiv := gl_first_line_divided_powers
theorem swpWt : SwpWt := swap_weight_compat
theorem swpPol : SwpPol := swap_polynomial_compat
theorem swpInt : SwpInt := swpInt_statement
theorem coreQp : CoreQp := coreQp_of rowGlOne rowGlDiv swpWt swpPol swpInt
theorem descentZ : DescentZ := descent_over_integers
theorem ascentDomain : AscentDomain := ascent_domain_holds
theorem unitsOfLocal : UnitsOfLocal := by
  intro p hp O _ _ hpu c hc
  by_contra hcu
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime (p : ℤ) c := by
    first
    | exact (Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hc
    | exact (Prime.coprime_iff_not_dvd hpz).2 hc
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (u : O) * (p : O) + (v : O) * (c : O) = 1 := by
    have := congrArg (fun z : ℤ => (z : O)) huv
    push_cast at this
    exact this
  have hmp : (p : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hmc : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hcu
  have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmp) (Ideal.mul_mem_left _ _ hmc)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
theorem sandwichZp : SandwichZp := by
  intro p hp r n hn ν hν l hL x hx
  have hS : Spread (Padic p) r n ν l := by
    rcases hL with h | ⟨rfl, h⟩
    · exact spreadTop _ r n ν l h
    · exact spreadSquare _ _ ν l h
  exact coreQp p r n hn ν hν l hS x hx
theorem sandwichZ : SandwichZ := by
  intro p hp r n hn ν hν l hL f hf
  exact descentZ p r n hn ν hν (sExp p r l) (sandwichZp p r n hn ν hν l hL) f hf
theorem sandwichDomain : SandwichDomain := sandwichDomain_of sandwichZ ascentDomain
theorem sandwichLocal : SandwichLocal := by
  intro p hp r n hn ν hν l hL O _ _ _ hpu
  exact sandwichDomain p r n hn ν hν l hL O (unitsOfLocal p O hpu)
theorem sandwichModel : SandwichModel := by
  intro p hp O Kf _ _ _ _ hO m lam hlam
  have hanti : Antitone (fun t : Fin (m + 1) => (lam t - lam (Fin.last m)).toNat) := by
    intro s t hst
    exact Int.toNat_le_toNat (sub_le_sub_right (hlam hst) _)
  have hL : LBound (m + 1) (fun t : Fin (m + 1) => (lam t - lam (Fin.last m)).toNat)
      ((lam 0 - lam (Fin.last m)).toNat) := by
    left
    intro t
    exact Int.toNat_le_toNat (sub_le_sub_right (hlam (Fin.zero_le t)) _)
  obtain ⟨h1, h2⟩ := sandwichDomain p (m + 1) (m + 1) le_rfl _ hanti _ hL O hO
  refine ⟨?_, Submodule.map_mono h2⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨_, h1 y hy, ?_⟩
  rw [map_smul]
  all_goals rfl
theorem sandwichModelLocal : SandwichModelLocal := by
  intro p hp O Kf _ _ _ _ _ hpu m lam hlam
  exact sandwichModel p O Kf (unitsOfLocal p O hpu) m lam hlam

end Formalism.InvariantFactorPaths.INST.Top
