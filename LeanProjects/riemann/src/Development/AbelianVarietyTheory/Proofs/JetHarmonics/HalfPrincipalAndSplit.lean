import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.HalfGen

theorem factors_of_ncard_places (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have h1 : s.card ≤ Module.finrank ℚ E := by
    have := Multiset.pow_card_le_prod hle
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map] at this
    exact (Nat.pow_le_pow_iff_right hg.one_lt).1 this
  have h2 : Module.finrank ℚ E ≤ s.toFinset.card := by
    rw [← h, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun v => v.asIdeal) (fun v hv => ?_)
      (fun v _ w _ e => HeightOneSpectrum.ext e) (Finset.finite_toSet _)
    rw [Finset.mem_coe, Multiset.mem_toFinset, hs, Ideal.mem_normalizedFactors_iff hI0]
    exact ⟨v.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hv⟩
  have h3 := Multiset.toFinset_card_le s
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.1 (by omega)⟩

theorem barE_piG {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D _

theorem half_principal_and_split : ∀ (D : D7) (T : Core D), LawsM T → ∀ EX : ErrX D,
 letI := T.Q.H.starRing
 (∃ α : 𝓞 D.host.E, α * star α = ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {star α}) ∧ (∀ i, star (EX.piG i) = piBarO EX i ∧ piBarO EX i * star (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E)) ∧ ((∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) → T.Q.l.Mb = Ideal.span {piBarO EX 0 * piBarO EX 1}) ∧ ∀ (L : SizeData₂ D), ParameterChoice' D L → ∀ i, (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup := by
  intro D T h EX
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => by rw [bar_core, barE_piG]
  have hbb : ∀ a, T.Q.H.bar (T.Q.H.bar a) = a := fun a => by rw [bar_core, bar_core, barE_barE]
  have hn : ∀ i, piBarO EX i * T.Q.H.bar (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [← hb, hbb, mul_comm, hb]
    exact RPfVal.piG_mul_bar EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hpp : (piOf T EX 0 * piOf T EX 1) * T.Q.H.bar (piOf T EX 0 * piOf T EX 1) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [map_mul, ← hp 0, ← hp 1]; ring
  refine ⟨⟨T.Q.H.bar (piOf T EX 0 * piOf T EX 1), ?_, ?_⟩, fun i => ⟨hb i, hn i⟩, fun ho => ?_, fun _ _ i => ?_⟩
  · show T.Q.H.bar _ * T.Q.H.bar (T.Q.H.bar _) = _
    rw [hbb, mul_comm, hpp, level_M T h, Nat.cast_mul]
  · show _ = Ideal.span {T.Q.H.bar (T.Q.H.bar _)}
    rw [hbb, hM]
  · have hcg : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    rw [← hn 0, ← hn 1] at hcg
    have hc : IsCoprime (piBarO EX 0) (piBarO EX 1) := hcg.of_mul_left_left.of_mul_right_left
    have hd : ∀ i, piBarO EX i ∣ piOf T EX 0 * piOf T EX 1 := fun i =>
      Ideal.mem_span_singleton.1 (ho i (hM ▸ Ideal.mem_span_singleton_self _))
    obtain ⟨c, hcc⟩ := hc.mul_dvd (hd 0) (hd 1)
    have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
    have hu : c * T.Q.H.bar c = 1 := by
      apply mul_left_cancel₀ hg
      rw [_root_.mul_one]
      conv_rhs => rw [← hpp, hcc, map_mul, map_mul]
      rw [← hn 0, ← hn 1]
      ring
    rw [hM, hcc]
    exact Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one _ hu) _
  · exact factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.HalfGen
