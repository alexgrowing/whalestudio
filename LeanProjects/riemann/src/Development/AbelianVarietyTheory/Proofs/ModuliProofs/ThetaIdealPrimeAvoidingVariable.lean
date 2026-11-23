import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsVeryGeneralPointOfHolomorphicFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPrime

theorem eval₂_smul_of_isHomogeneous {o K I : Type} [CommRing o] [CommRing K] (β : o →+* K)
    (v : I → K) (c : K) {F : MvPolynomial I o} {n : ℕ} (hF : F.IsHomogeneous n) :
    MvPolynomial.eval₂ β (c • v) F = c ^ n * MvPolynomial.eval₂ β v F := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ i ∈ m.support, m i = n := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem exists_homogenisation {o I D : Type} [CommRing o] (a₀ : I) (a : D → I)
    (G : MvPolynomial D o) : ∃ (n : ℕ) (H : MvPolynomial I o),
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K), v a₀ ≠ 0 →
        MvPolynomial.eval₂ β v H = v a₀ ^ n * MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, fun K _ β v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, H, hH⟩ := hp
    obtain ⟨m, H', hH'⟩ := hq
    refine ⟨n + m, MvPolynomial.X a₀ ^ m * H + MvPolynomial.X a₀ ^ n * H', fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, hH K β v hv, hH' K β v hv]
    ring
  | mul_X p i hp =>
    obtain ⟨n, H, hH⟩ := hp
    refine ⟨n + 1, H * MvPolynomial.X (a i), fun K _ β v hv => ?_⟩
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hH K β v hv]
    field_simp
    ring

noncomputable def coneIdeal {o I Z : Type} [CommRing o] (em : o →+* ℂ) (B : Set Z) (θ : Z → I → ℂ) :
    Ideal (MvPolynomial I o) :=
  ⨅ (z : Z) (_ : z ∈ B) (c : ℂ) (_ : c ≠ 0), RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z))

theorem mem_coneIdeal {o I Z : Type} [CommRing o] {em : o →+* ℂ} {B : Set Z} {θ : Z → I → ℂ}
    {F : MvPolynomial I o} : F ∈ coneIdeal em B θ ↔
      ∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ em (c • θ z) F = 0 := by
  simp [coneIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem coneIdeal_isPrime {o I : Type} [CommRing o] [Countable o] [Countable I] (em : o →+* ℂ)
    {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ) (ho : IsOpen B)
    (hc : IsPreconnected B) (hn : B.Nonempty) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B) :
    (coneIdeal em B θ).IsPrime := by
  obtain ⟨z, hz, c, hc0, h⟩ :=
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em I d B θ ho hc hn hd
  have : coneIdeal em B θ = RingHom.ker (MvPolynomial.eval₂Hom em (c • θ z)) := by
    ext F
    rw [mem_coneIdeal, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom]
    exact ⟨fun hF => hF z hz c hc0, h F⟩
  rw [this]
  exact RingHom.ker_isPrime _

theorem exists_ratios {o I : Type} [CommRing o] [Finite I] (em : o →+* ℂ)
    (hem : Function.Injective em) {d : ℕ} {B : Set (Fin d → ℂ)} (θ : (Fin d → ℂ) → I → ℂ)
    (ho : IsOpen B) (hd : ∀ a, DifferentiableOn ℂ (fun z => θ z a) B)
    (hf : ∀ z ∈ B, {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) (a₁ : I)
    (h₁ : MvPolynomial.X a₁ ∉ coneIdeal em B θ) :
    ∃ (a₀ : I) (a : Fin d → I), MvPolynomial.X a₀ ∉ coneIdeal em B θ ∧
      ∀ (K : Type) [Field K] (β : o →+* K) (v : I → K),
        RingHom.ker (MvPolynomial.eval₂Hom β v) = coneIdeal em B θ →
        ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 →
          G = 0 := by
  rw [mem_coneIdeal] at h₁
  push Not at h₁
  obtain ⟨z₁, hz₁, c₁, -, h₁⟩ := h₁
  have h₁' : θ z₁ a₁ ≠ 0 := by
    intro h
    apply h₁
    simp [h]
  have hcont : ContinuousAt (fun z => θ z a₁) z₁ :=
    (hd a₁).continuousOn.continuousAt (ho.mem_nhds hz₁)
  have hU : {z | z ∈ B ∧ θ z a₁ ≠ 0} ∈ nhds z₁ :=
    Filter.inter_mem (ho.mem_nhds hz₁) (hcont.eventually_ne h₁')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsub : Metric.ball z₁ ε ⊆ B := fun z hz => (hball hz).1
  obtain ⟨a₀, a, ⟨z₀, hz₀, h₀⟩, hind⟩ := GlobalTheory.CountableFibres.exists_independent_ratios d I
    (Metric.ball z₁ ε) θ Metric.isOpen_ball (convex_ball z₁ ε).isPreconnected
    ⟨z₁, Metric.mem_ball_self hε⟩ (fun a => (hd a).mono hsub)
    (fun z hz => ⟨fun h => (hball hz).2 (by rw [h]; rfl),
      Set.Countable.mono (fun z' hz' => And.intro (hsub hz'.1) hz'.2) (hf z (hsub hz))⟩)
  have hX : MvPolynomial.X a₀ ∉ coneIdeal em B θ := by
    intro h
    have := mem_coneIdeal.1 h z₀ (hsub hz₀) 1 one_ne_zero
    simp [h₀] at this
  refine ⟨a₀, a, hX, fun K _ β v hv G hG => ?_⟩
  have hv₀ : v a₀ ≠ 0 := by
    intro h
    apply hX
    rw [← hv, RingHom.mem_ker]
    simp [h]
  obtain ⟨n, H, hH⟩ := exists_homogenisation a₀ a G
  have hHP : H ∈ coneIdeal em B θ := by
    rw [← hv, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hH K β v hv₀, hG, mul_zero]
  have hmap : MvPolynomial.map em G = 0 := by
    refine hind _ fun z hz hz0 => ?_
    have := mem_coneIdeal.1 hHP z (hsub hz) 1 one_ne_zero
    rw [one_smul, hH ℂ em _ hz0] at this
    rw [MvPolynomial.eval_map]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hz0)
  exact MvPolynomial.map_injective em hem (by rw [hmap, map_zero])

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) :
    Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (by simp)
  exact hf.countable

theorem span_range_eq_top {K I : Type} [Field K] {v : I → K} (hv : v ≠ 0) :
    Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) (IsUnit.mk0 _ ha)

theorem exists_prime_independent_ratios : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  intro hL hL2 g N' J Mat κ w w' o _ b em C d hAr hG p a₁ hN hp hle hX
  obtain ⟨-, hft, hem⟩ := hAr
  have : Countable o := countable_of_finiteType o hft
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨r, B, θ, hfam, hcov⟩ := hG.fam
  have hmem : ∀ F, F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v →
      MvPolynomial.eval₂ em v F = 0 := by
    intro F
    simp [thIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  have hinf : (Finset.univ : Finset (Fin r)).inf (fun i => coneIdeal em (B i) (θ i)) ≤ p := by
    refine le_trans (fun F hF => ?_) hle
    rw [hmem]
    intro t v ht hv
    obtain ⟨i, z, hz, hθ⟩ := hcov t ht
    have hFi : F ∈ coneIdeal em (B i) (θ i) :=
      (Finset.inf_le (f := fun i => coneIdeal em (B i) (θ i)) (Finset.mem_univ i)) hF
    have key : ∃ c : ℂ, c ≠ 0 ∧ v = c • θ i z := by
      by_cases h0 : θ i z = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        by_contra hne
        rw [h0, smul_zero] at hne
        obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ v (θ i z) hv hθ
          (span_range_eq_top hne)
        apply hne
        funext a
        have := hu a
        rw [h0] at this
        simpa using this
      · obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ _ (θ i z) v hθ hv
          (span_range_eq_top h0)
        exact ⟨u, u.ne_zero, funext hu⟩
    obtain ⟨c, hc, rfl⟩ := key
    exact mem_coneIdeal.1 hFi z hz c hc
  obtain ⟨i, -, hi⟩ := hp.inf_le'.1 hinf
  obtain ⟨ho, hc, hd, hz⟩ := hfam i
  have hX' : MvPolynomial.X a₁ ∉ coneIdeal em (B i) (θ i) := fun h => hX (hi h)
  have hn : (B i).Nonempty := by
    by_contra hne
    apply hX'
    rw [mem_coneIdeal]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  obtain ⟨a₀, a, h₀, hind⟩ := exists_ratios em hem (θ i) ho hd (fun z hz' => (hz z hz').2) a₁ hX'
  refine ⟨_, a₀, a, coneIdeal_isPrime em (θ i) ho hc hn hd, fun F hF => ?_, hi, h₀, hind⟩
  rw [mem_coneIdeal]
  intro z hz' c _
  obtain ⟨t, ht, hθ⟩ := (hz z hz').1
  have hcomp := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [eval₂_smul_of_isHomogeneous em _ c (MvPolynomial.homogeneousComponent_isHomogeneous e F),
    (hmem _).1 (hcomp e) t _ ht hθ, mul_zero]

end GlobalTheory.ThetaPrime
