import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.VanishingOfLadder
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel.Van

theorem dividedPowerFiltration_eq_bot {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hJ : J = ⊥) {r : ℕ} (hr : 1 ≤ r) :
    pdP δ r = ⊥ := by
  subst hJ
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact δ.dpow_eval_zero h0

theorem van_on {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (hI : I = ⊥) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {e : ℕ}
    (c : Coord q V e) (d : ℕ) (he : e ≤ d) (j : ℕ) :
    Subsingleton (CH.H (sq (sFil (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V}) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  obtain ⟨c', -, -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart γ p hp hn q κ c
  have hgood := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQ : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, h⟩
    exact h
  have hD : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} c'.D := ⟨trivial, V, rfl, c'.inV⟩
  obtain ⟨hpow, -⟩ := GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' hgood _ hQ hD
  obtain ⟨PQ, hPQ⟩ := CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {V}
  refine CrystallineSemistableComparison.Pb.vanishing_of_ladder e PQ (a := sFil _) (b := fun _ => IdF.bot _) (c'.frame hgood _ hQ hD) ((d : ℤ) + 1)
    ⟨fun r' T x hx => ?_, fun r' _ => (hPQ r').1, fun r' _ => (hPQ r').2.1⟩ (fun r' h1 _ x hx => ?_) j
  · have h0 : x = 0 := hx
    rw [h0]
    exact Ideal.zero_mem _
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow r'.toNat := hx
    rw [hpow, dividedPowerFiltration_eq_bot γ hI (by omega), Ideal.map_bot] at h2
    exact h2

theorem Im_one_eq_bot (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] : Wc.Im l k 1 = ⊥ := by
  refine (Ideal.map_eq_bot_iff_le_ker _).2 ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem nat_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] :
    ((l : ℕ) : Wc.Wm l k 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem witt_level_one_filtration_vanish : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  intro l _ k _ _ _ O _ X q ρ U d hd j
  have hp : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [nat_eq_zero]
    exact IsNilpotent.zero
  refine (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)) ((d : ℤ) + 1)) (IdF.bot _))
    (⊤ : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)))) U.U 0).2.1 (fun S hS j => ?_) j
  obtain ⟨α, hα⟩ := id hS
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα) (U.inter S hS)
  exact van_on (Wc.pd l k 1) (Im_one_eq_bot l k) l hp hn q _ c' d (hd α) j

end GlobalTheory.CompanionTheory.WittLevel.Van
