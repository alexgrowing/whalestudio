import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBoundAllPlaces
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagModStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagModOfDvdStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialFlagAtPrimeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
namespace GlobalTheory.CompanionTheory.Ar.Num

def zpLocSubalg (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subalgebra ℤ Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      · exact hb h
      · exact hb' h
    · push_cast
      rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      · exact hb h
      · exact hb' h
    · rw [div_add_div _ _ hb0 hb0']
      push_cast
      ring
  algebraMap_mem' := by
    intro a
    refine ⟨a, 1, fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h), ?_⟩
    simp

theorem mem_range_zpLocSubalg (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zpLocSubalg Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_chartRing_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) {ι' : Type} (z : ι' → Ω) (s : ι')
    {w : Ω} (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing o z s) : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing o' z s := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at *
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem trivFlagMod_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (ϖ : o) (ϖ' : o')
    (hϖ : algebraMap o' Ω ϖ' = algebraMap o Ω ϖ) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ)
    (h : TrivFlagMod o ϖ x N b) : TrivFlagMod o' ϖ' x N b := by
  obtain ⟨g, h1, h2⟩ := h
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, e, he, r, hr', heq⟩ := h1 s hs
    exact ⟨fun i j => mem_chartRing_of_range_le hr _ _ (hg i j), e, mem_chartRing_of_range_le hr _ _ he, r,
      mem_chartRing_of_range_le hr _ _ hr', by rw [hϖ]; exact heq⟩
  · obtain ⟨m, U, Z, hU, hZ, hlow, hdiag, hgs, heq⟩ := h2 s t hs ht
    exact ⟨m, U, Z, fun i j => mem_chartRing_of_range_le hr _ _ (hU i j),
      fun i j => mem_chartRing_of_range_le hr _ _ (hZ i j), hlow, hdiag,
      fun i j => mem_chartRing_of_range_le hr _ _ (hgs i j), by rw [hϖ]; exact heq⟩

theorem trivFlagMod_of_eq_zero (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (hN : N = 0) (b : Fin N → K → ℤ) :
    TrivFlagMod o ϖ x N b := by
  subst hN
  refine ⟨fun _ => 0, fun s _ => ⟨fun i => i.elim0, 1, one_mem _, 0, zero_mem _, by simp⟩,
    fun s t _ _ => ⟨0, 0, 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, Subsingleton.elim _ _⟩⟩

theorem isUnit_natCast_of_not_dvd {A O : Type} [CommRing A] [CommRing O] [IsLocalRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  by_contra hu
  have hbO : algebraMap A O (b : A) ∈ IsLocalRing.maximalIdeal O := by
    rw [map_natCast]
    exact hu
  have hbm : (b : A) ∈ m := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m _).1 hbO
  have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
  obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
  have h1 : (1 : A) ∈ m := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
  exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)

theorem trivFlagOnHodge_of_fargues : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → TrivFlagOnHodge := by
  intro hF
  unfold TrivFlagOnHodge
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd Fl x e hRL p hpS hHT A _ _ _
  unfold AtPlacesOver
  intro m _ hpm O _ _ _ _ _ _ _ τ W hW
  haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hflag : TrivFlagMod O ϖ y (D.p + D.q) (fun i => x (τ, i)) := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
    · exact trivFlagMod_of_eq_zero O ϖ y _ h0 _
    · have hint := intCast_injective_of_isArithVar hd
      haveI : CharZero Ω := ⟨fun a b hab => by
        have : Int.castRingHom Ω (a : ℤ) = Int.castRingHom Ω (b : ℤ) := by simpa using hab
        exact_mod_cast hint this⟩
      have h1 := GlobalTheory.T.hodge_tate_free_trivial_flag_mod hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpos (zpLocSubalg Ω p)
        (mem_range_zpLocSubalg Ω p) Fl x e hHT hRL τ
      have hr : ∀ a : zpLocSubalg Ω p, algebraMap (zpLocSubalg Ω p) Ω a ∈ (algebraMap O Ω).range := by
        intro a
        obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zpLocSubalg Ω p _).1 ⟨a, rfl⟩
        have hu := isUnit_natCast_of_not_dvd (O := O) m p hpm b hb
        refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
        rw [hab, map_mul, map_intCast, div_eq_mul_inv]
        congr 1
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
      have h2 : TrivFlagMod O ((p : O) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => x (τ, i)) :=
        trivFlagMod_of_range_le hr _ _ (by simp) _ _ _ h1
      have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
        have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
        rwa [map_natCast] at this
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hpO
      have hR : 𝔐.R p - 2 ≠ 0 := by
        have := 𝔐.R_ge p hpS
        omega
      exact GlobalTheory.T.triv_flag_mod_of_dvd O Ω K J y _ ϖ _ _ (dvd_pow hpO hR) h2
  have hJ := isMultiHomogIdeal_pointIdeal_sup_map_C (ι := J) (O := O) y (IsLocalRing.maximalIdeal O)
  have hWh := GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof.{0} O K J _ W hJ hW.1
  have hCϖ : (C ϖ : GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) ∈ W :=
    hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)))
  exact GlobalTheory.T.trivial_flag_at_prime O Ω K J y ϖ hϖ _ _ hflag W ⟨hW.1.1.1, hWh, hW.2⟩ (le_sup_left.trans hW.1.1.2) hCϖ

end GlobalTheory.CompanionTheory.Ar.Num
