import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

theorem reg_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q :=
  fun _ _ _ ξ p a ha => exists_open_mem_regAt ξ p a ha

theorem reg_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  intro X Ω _ ξ
  refine ⟨fun p => ?_, fun p q h => (RegAtMono.regAt_mono X Ω ξ p q h).1, fun hg p a => ?_⟩
  · unfold regAt
    exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)
  · haveI := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
    refine ⟨u, u.2, v, v.2, fun h => ?_, rfl⟩
    exact nonZeroDivisors.ne_zero hv (Subtype.ext h)

theorem regat_loc : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  intro o _ Ω _ _ κ _ x M c p hp
  have h1 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p := fun a ha => (M.tie.ring c hp.1 a).1 ha p hp
  refine ⟨h1, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction M.X Ω M.ξ o κ x M.tie c p hp a).1 ha
    exact ⟨s * a, hsa, s, hs, hu, by field_simp [hu.1]⟩
  · rintro ⟨u, hu, v, -, hv, rfl⟩
    rw [div_eq_mul_inv]
    exact mul_mem (h1 u hu) hv.2.2

theorem prime_pt : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  intro o _ Ω _ _ κ _ x M c hc P hP
  obtain ⟨p, ⟨h1, h2⟩, h3⟩ := chart_point_of_prime M.X Ω M.ξ o κ x M.tie c hc P hP
  refine ⟨p, ⟨h1, fun u => ?_⟩, fun q hq => h3 q ⟨hq.1, fun u => ?_⟩⟩
  · rw [← h2 u, not_not]
  · rw [hq.2 u, not_not]

open ChartPrimes in
theorem basic : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  intro o _ Ω _ _ κ _ x M c p U hp hpU
  have T := M.tie
  have hc := hp.1
  obtain ⟨W, hW, hmem⟩ := T.affine c hc
  have hg : genPt M.ξ ∈ W := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hpW : p.1 ∈ W := (hmem _).2 ⟨p.2, hp⟩
  obtain ⟨f, hf, hpf⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hpU⟩ hpW
  have key : ∀ (q : Cpt M.ξ) (hq : q.1 ∈ W), q.1 ∈ M.X.basicOpen f ↔ unitAt M.ξ q (secVal M.ξ W hg f) := by
    intro q hq
    rw [M.X.mem_basicOpen f _ hq, ← genMap_germ_eq W hg q hq f]
    exact isUnit_iff_unitAt q (T.gen.inj _) _
  refine ⟨secVal M.ξ W hg f, ?_, (key p hpW).1 hpf, fun q hq hu => hf ((key q ((hmem _).2 ⟨q.2, hq⟩)).2 hu)⟩
  exact (T.ring c hc _).2 fun q hq => ⟨_, genMap_germ_eq W hg q ((hmem _).2 ⟨q.2, hq⟩) f⟩

theorem reg_le_spec : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  intro o _ Ω _ _ κ _ x M p q
  refine ⟨fun h => ?_, (reg_local M.X Ω M.ξ).2.1 p q⟩
  rw [specializes_iff_forall_open]
  intro s hs hp
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨f, -, hu, hf⟩ := basic o Ω κ x M c p ⟨s, hs⟩ hc hp
  exact hf q ⟨hc.1, fun j => h (hc.2 j)⟩ ⟨hu.1, h hu.2.1, h hu.2.2⟩

end PositivityTheory.HtPt.Ma
