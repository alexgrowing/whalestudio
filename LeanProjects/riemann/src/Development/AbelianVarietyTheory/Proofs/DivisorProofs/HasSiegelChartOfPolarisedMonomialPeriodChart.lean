import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg

theorem hasChart_of_hasPolChart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o)
    (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) (hn : n ≠ 0) (h : HasPolChart F s j e φ BD d x) :
    HasChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, ⟨hc, hz, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨hM, hX, hδ, hdef, hmon⟩, ha, hBD⟩ := h
  have hCN : IsCN R := ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2, hc, hz⟩
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := ht.2 (Pi.single i 1) (by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
      simp [h0]) i
    simp at this
  have hsym : ∀ i y z, ((n : ℤ) • δ i) y z = ((n : ℤ) • δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem i)) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg i y)
  have hpos : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    exact ⟨i, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hi⟩
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data R Q m t (fun i => (n : ℤ) • δ i) hCN hmon ht.1 ht0 hsym hnn hpos
  obtain ⟨G', _, _, π, A, U, hU⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  let ϑ : Fin m → LinearMap.BilinForm ℤ D.toPre.X := fun i => pull ε.toIntLinearEquiv.toLinearMap (δ i)
  have hϑ : ∀ (k : ℤ) i, pull ε.toIntLinearEquiv.toLinearMap (k • δ i) = k • ϑ i := fun k i =>
    LinearMap.ext₂ fun y z => by simp [ϑ]
  refine ⟨R, inferInstance, inferInstance, b, ξ, m, t, R', inferInstance, inferInstance, inferInstance, ρ, r, G', inferInstance,
    inferInstance, π, D, A, U, ϑ, a, ⟨hc, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨⟨hCN'.1, inferInstance, hCN'.2.1, hCN'.2.2.1⟩, hCN'.2.2.2, hinj, hfin, hloc, hr⟩,
    ⟨hU, ?_, hδ.pull_equiv ε.toIntLinearEquiv, ?_⟩, fun i => ?_, hBD⟩
  · rw [LinearEquiv.finrank_eq ε.toIntLinearEquiv]; exact hX
  · convert hmon' using 2 with i
    rw [hϑ, ← mul_smul]
  · rw [ha i, ← hϑ, evalZ_pull φ ε.toIntLinearEquiv.surjective]

end GlobalTheory.PolDeg
