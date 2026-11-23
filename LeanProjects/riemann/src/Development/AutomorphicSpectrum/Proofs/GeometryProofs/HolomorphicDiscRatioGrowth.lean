import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointAnalyticDiscStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeigStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem val_mul_eq {R K : Type} [CommRing R] [Field K] {φ₀ : R →+* K} (hξ : IsCptGen (pt φ₀)) (φ : R →+* ℂ)
    {g h : R} (h0 : φ₀ h ≠ 0) {r : ℂ} (hv : ValAt (pt φ₀) (pt φ) (φ₀ g / φ₀ h) r) : r * φ h = φ g := by
  obtain ⟨hsp, s, hs, rfl⟩ := hv
  let c : Cpt (pt φ₀) := ⟨centre (pt φ), hsp⟩
  have e : s * tS c.1 h = tS c.1 g := by
    apply hξ.inj c
    rw [map_mul, genMap_toStalk, genMap_toStalk]
    refine (congrArg (· * φ₀ h) hs).trans ?_
    exact div_mul_cancel₀ _ h0
  have k : ∀ a : R, (Scheme.stalkClosedPointTo (pt φ)).hom (tS c.1 a) = φ a := fun a => by
    have := genMap_toStalk φ (self (pt φ)) a
    rw [genMap_self] at this
    exact this
  rw [← k h, ← k g, ← e]
  exact (map_mul _ _ _).symm

theorem ne_zero_of_top_le {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (f : R)
    (hW : ⊤ ≤ (pt φ) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens)) : φ f ≠ 0 := by
  have h1 : genPt (pt φ) ∈ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) :=
    hW (show IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  have h2 : f ∉ (genPt (pt φ)).asIdeal := h1
  rw [genPt_asIdeal] at h2
  exact h2

theorem isDVR_regAt {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    {φ : R →+* K} (hξ : IsCptGen (pt φ)) (x : Cpt (pt φ)) (h1 : x.1.asIdeal.height = 1) :
    IsDiscreteValuationRing (regAt (pt φ) x) := by
  haveI : (x.1 : PrimeSpectrum R).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hd := GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' R x.1.asIdeal h1
  have key : ∀ (q : PrimeSpectrum R), Nonempty (Localization.AtPrime q.asIdeal ≃+* (Spec.structureSheaf R).presheaf.stalk q) :=
    fun q => ⟨(IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv⟩
  obtain ⟨e⟩ := key x.1
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (e.trans (CPoint.regAtEquivStalk hξ x))

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

namespace GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc

open GlobalTheory.CompanionTheory.Ar.CptModel

theorem exists_pole_prime {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] (t : K) (ht : ∀ a : R, algebraMap R K a ≠ t) :
    ∃ p : Ideal R, p.IsPrime ∧ p.height = 1 ∧ ∀ a c : R, c ∉ p → t * algebraMap R K c ≠ algebraMap R K a := by
  by_contra hcon
  push Not at hcon
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes R (e.symm t) fun q hq h1 => by
    obtain ⟨a, c, hc, hac⟩ := hcon q hq h1
    refine ⟨a, c, hc, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, e.commutes, e.commutes]
    exact hac
  have h2 : e (algebraMap R (FractionRing R) a) = t := by rw [ha, e.apply_symm_apply]
  rw [e.commutes] at h2
  exact ht a h2

theorem exists_cpt {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (hφ : Function.Injective φ) (p : Ideal R)
    (hp : p.IsPrime) : ∃ x : Cpt (pt φ), x.1.asIdeal = p := by
  have hsp : genPt (pt φ) ⤳ ((⟨p, hp⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) := by
    refine (PrimeSpectrum.le_iff_specializes (genPt (pt φ) : PrimeSpectrum R) ⟨p, hp⟩).1 ?_
    show (genPt (pt φ)).asIdeal ≤ p
    rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact ⟨⟨_, hsp⟩, rfl⟩

theorem exists_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) : ∃ c : R →+* S, spMap c = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem exists_disc {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (f : R) (hf : algebraMap R K f ≠ 0)
    (t : K) (x : Cpt (pt (algebraMap R K))) (hxf : f ∈ x.1.asIdeal) (hx1 : x.1.asIdeal.height = 1)
    (hxt : t ∉ regAt (pt (algebraMap R K)) x) :
    ∃ (φ : (Fin 1 → ℂ) → (R →+* ℂ)) (r : (Fin 1 → ℂ) → ℂ) (C : ℝ), IsHolPts (Metric.ball 0 1) φ ∧
      ∀ z ∈ punct 1 1 1, ⊤ ≤ (pt (φ z)) ⁻¹ᵁ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) ∧
        ValAt (pt (algebraMap R K)) (pt (φ z)) t (r z) ∧ r z ≠ 0 ∧ ‖(r z)⁻¹‖ ≤ C * ‖z 0‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  have hgW : genPt (pt (algebraMap R K)) ∈
      (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := by
    show f ∉ (genPt (pt (algebraMap R K))).asIdeal
    rw [genPt_asIdeal]
    exact hf
  have hxW : x.1 ∉ (PrimeSpectrum.basicOpen f : (Spec (CommRingCat.of R)).Opens) := fun hm => (show f ∉ x.1.asIdeal from hm) hxf
  have hlft : LocallyOfFiniteType (spMap (algebraMap ℚ R)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨V, hV, ψ, r, C, -, hhol, -, hz⟩ := GlobalTheory.T.dvr_point_analytic_disc ℚ (algebraMap ℚ ℂ) (Spec (CommRingCat.of R))
    (spMap (algebraMap ℚ R)) K (pt (algebraMap R K)) (PrimeSpectrum.basicOpen f) x ⊤ t hlft hξ hgW hxW trivial
    (isDVR_regAt hξ x hx1) hxt
  obtain ⟨c, hc⟩ := exists_ringHom (S := Γ(Spec (CommRingCat.of R), V)) hV.fromSpec
  have hy : ∀ w, spMap (ψ w) ≫ hV.fromSpec = pt ((ψ w).comp c) := fun w => by
    rw [← hc]
    exact (Spec.map_comp _ _).symm
  refine ⟨fun z => (ψ z).comp c, r, C, ⟨hhol.1, fun a => hhol.2 (c a)⟩, fun z hzp => ?_⟩
  have := hz z hzp
  rwa [hy] at this

theorem disc_of_pole {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R] [Algebra R K] [IsFractionRing R K] (g h b : R)
    (hh : algebraMap R K h ≠ 0) (hb : algebraMap R K b ≠ 0)
    (ht : ∀ a : R, algebraMap R K a ≠ algebraMap R K g / algebraMap R K h) :
    ∃ (ψ : ℂ → (R →+* ℂ)) (C : ℝ), (∀ a : R, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  have hξ : IsCptGen (pt (algebraMap R K)) := isCptGen_fractionRing
  obtain ⟨p, hp, hp1, hpole⟩ := exists_pole_prime _ ht
  have hhp : h ∈ p := by
    by_contra hn
    exact hpole g h hn (div_mul_cancel₀ _ hh)
  obtain ⟨x, rfl⟩ := exists_cpt (algebraMap R K) (IsFractionRing.injective R K) p hp
  have hnt : algebraMap R K g / algebraMap R K h ∉ regAt (pt (algebraMap R K)) x := by
    intro hm
    obtain ⟨a, c, hc, -, e⟩ := (mem_regAt_iff _ x _).1 hm
    exact hpole a c hc e
  obtain ⟨φ, r, C, hhol, hz⟩ := exists_disc (K := K) (b * h) (by rw [map_mul]; exact mul_ne_zero hb hh) _ x
    (Ideal.mul_mem_left _ b hhp) hp1 hnt
  have hd : ∀ z : ℂ, ‖(fun _ => z : Fin 1 → ℂ)‖ = ‖z‖ := fun z => pi_norm_const z
  refine ⟨fun z => φ fun _ => z, C, fun a => ?_, fun z hz1 hz0 => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun (z : ℂ) (_ : Fin 1) => z) (Metric.ball 0 1) :=
      (differentiable_pi.2 fun _ => differentiable_id).differentiableOn
    refine (hhol.2 a).comp h1 fun z hz1 => ?_
    rw [mem_ball_zero_iff] at hz1 ⊢
    rwa [hd]
  · have hmem : (fun _ => z : Fin 1 → ℂ) ∈ punct 1 1 1 := by
      refine ⟨?_, fun _ _ => hz0⟩
      rw [mem_ball_zero_iff] at hz1 ⊢
      rwa [hd]
    obtain ⟨hW, hval, hr0, hbd⟩ := hz _ hmem
    have hbh := ne_zero_of_top_le _ _ hW
    rw [map_mul] at hbh
    have e := val_mul_eq hξ _ hh hval
    have hz0' := right_ne_zero_of_mul hbh
    refine ⟨left_ne_zero_of_mul hbh, hz0', ?_⟩
    have e2 : φ (fun _ => z) h = (r fun _ => z)⁻¹ * φ (fun _ => z) g := by
      rw [← e]
      field_simp
    show ‖φ (fun _ => z) h‖ ≤ C * ‖z‖ * ‖φ (fun _ => z) g‖
    rw [e2, norm_mul]
    exact mul_le_mul_of_nonneg_right hbd (norm_nonneg _)

theorem pole_disc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  intro Ω _ _ A hFG hSm hfrac g h b hh hb ht
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 hFG
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨a, ha, c, hc, hc0, e⟩ := hfrac z
    have hc0' : algebraMap A Ω ⟨c, hc⟩ ≠ 0 := hc0
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, eq_div_of_mul_eq hc0' e⟩
  refine disc_of_pole (K := Ω) g h b hh hb fun a e => ht ?_
  have e' : (a : Ω) = (g : Ω) / h := e
  rw [← e']
  exact a.2

end GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc
