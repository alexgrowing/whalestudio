import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecMonomialOfConeCombinatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SgZero

theorem exists_nat_evalZ (φ : InvFun ℤ) (g : ℕ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ)
    (δ ga : Fin m → LinearMap.BilinForm ℤ X) (M d : ℕ) (hpf : IsPolFan id g φ) (hrk : Module.finrank ℤ X ≤ g)
    (hc : IsCone id φ ga) (hδ : ∀ k, δ k = (M : ℤ) • ga k) : ∃ b : Fin m → ℕ, ∀ k, (b k : ℝ) = d * φ.evalZ (δ k) := by
  have hP := hpf X hrk
  have key : ∀ k, ∃ n : ℕ, φ.evalZ (ga k) = n := by
    intro k
    obtain ⟨z, hz⟩ := hP.integral (ga k) (hc.mem k) (hc.nonneg k)
    by_cases h0 : ga k = 0
    · refine ⟨0, ?_⟩
      have := hc.evalZ_smul 0 k
      simp only [Nat.cast_zero, zero_smul, zero_mul] at this
      rw [h0]; simpa [h0] using this
    · have hp := hP.pos (ga k) (hc.mem k) (hc.nonneg k) h0
      refine ⟨z.toNat, ?_⟩
      rw [hz] at hp ⊢
      have : (0 : ℤ) ≤ z := by exact_mod_cast hp.le
      rw [show ((z.toNat : ℕ) : ℝ) = ((z.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg this]
  choose n hn using key
  refine ⟨fun k => d * (M * n k), fun k => ?_⟩
  rw [hδ, hc.evalZ_smul, hn]
  push_cast; ring

theorem dvd_of_map_dvd_of_finite (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    (ρ : A →+* B) (hρ : Function.Injective ρ) (hf : ρ.Finite) (a c : A) (ha : a ≠ 0) (h : ρ a ∣ ρ c) : a ∣ c := by

  letI : Algebra A B := ρ.toAlgebra
  haveI : Module.Finite A B := hf
  obtain ⟨x, hx⟩ := h
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) x
  let K := FractionRing A
  let L := FractionRing B
  let gL : A →+* L := (algebraMap B L).comp ρ
  have hgL : Function.Injective gL := (IsFractionRing.injective B L).comp hρ
  let iK : K →+* L := IsFractionRing.lift hgL
  have hιK : ∀ r : A, iK (algebraMap A K r) = gL r := IsFractionRing.lift_algebraMap hgL
  have hA : algebraMap A K a ≠ 0 := fun e => ha (IsFractionRing.injective A K (e.trans (map_zero _).symm))
  have hρa : algebraMap B L (ρ a) ≠ 0 := fun e => hA (by
    have := hgL (show gL a = gL 0 by simpa [gL] using e)
    rw [this, map_zero])
  set y : K := algebraMap A K c / algebraMap A K a with hy
  have hιKy : iK y = algebraMap B L x := by
    rw [hy, map_div₀, hιK, hιK]
    simp only [gL, RingHom.comp_apply, hx, map_mul]
    exact mul_div_cancel_left₀ _ hρa
  have hint : IsIntegral A y := by
    refine ⟨p, hpm, ?_⟩
    apply iK.injective
    rw [map_zero, Polynomial.hom_eval₂, hιKy]
    have e1 : iK.comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) := by
      ext r; exact hιK r
    rw [e1, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hint
  refine ⟨z, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hz, hy, mul_div_cancel₀ _ hA]

theorem idlAlong_eq_span_monomial : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∃ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) ∧ idlAlong (J.comap π) ξ = Ideal.span {∏ k, t k ^ b k} := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W φ d J S π j hJ hval hbl hji hpf V _ _ _ Q m t δ hrk ht hsym hnn hdef
    hmono ga M hcone hδ ξ hU
  obtain ⟨b, hb⟩ := exists_nat_evalZ φ g Q.X m δ ga M d hpf hrk hcone hδ
  refine ⟨b, hb, ?_⟩
  have hCN : IsCN V := hU.1
  obtain ⟨R', _, _, _, ρ, r, D, e, hCN', hρi, hρf, hρl, hr, hrefn, hmon⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data V Q m t δ hCN hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hdef
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal π J hbl V ξ
  rw [hg₀]
  have key : ∀ (Wr : Type) [CommRing Wr] [IsDomain Wr] [IsDiscreteValuationRing Wr], IsAdicComplete (maximalIdeal Wr) Wr →
      ∀ κ : R' →+* Wr, Function.Injective κ → IsLocalHom κ →
        Ideal.span {κ (ρ g₀)} = Ideal.span {κ (ρ (∏ k, t k ^ b k))} := by
    intro Wr _ _ _ hc κ hκi hκl
    obtain ⟨T, σ, c, e', hσ, hy, hc', hβ⟩ := GlobalTheory.T.exists_trait_period_form_valuation_sum_refined_chart F S j V Q ξ hU m t δ R' ρ r D e hCN' hρi hρf hρl hr
      (fun k => (ht k).2) hsym hrefn hmon Wr hc κ hκi hκl
    have hy' : jK T.V ≫ spMap σ ≫ (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = T.y ≫ i := by
      rw [← hji]
      simpa only [Category.assoc] using congrArg (· ≫ π) hy
    have h1 := GlobalTheory.T.idealSheafAlongLocalSpec_monomial_of_cone_combination F Z i φ J d hval Q.X m ga δ M hcone hδ b hb T Wr σ c e' (spMap κ ≫ spMap ρ ≫ ξ ≫ π)
      (fun k => κ (ρ (t k))) hσ hy' hc' hβ
    have h2 : idlAlong J (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = Ideal.span {κ (ρ g₀)} := by
      rw [GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, ← GlobalTheory.PullAlong.idlAlong_comap_eq, hg₀,
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rw [← h2, h1, map_prod, map_prod]
    simp only [map_pow]
  obtain ⟨hN', hI', -, hZ'⟩ := hCN'
  obtain ⟨-, hIV, -, -⟩ := hCN
  set f := ∏ k, t k ^ b k with hfdef
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k).2
  have hρf0 : ρ f ≠ 0 := fun h => hf0 (hρi (h.trans (map_zero ρ).symm))
  have hκ0 : ∀ (Wr : Type) [CommRing Wr] (κ : R' →+* Wr), Function.Injective κ → κ (ρ f) ≠ 0 :=
    fun Wr _ κ hκ h => hρf0 (hκ (h.trans (map_zero κ).symm))
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨Wr, _, _, _, κ, ⟨hdvr, hc, -⟩, hκi, hcm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
    have hκl : IsLocalHom κ := ⟨fun a ha => by
      by_contra hna
      have : a ∈ (maximalIdeal Wr).comap κ := by rw [hcm]; exact hna
      exact (mem_maximalIdeal _).1 this ha⟩
    have := key Wr hc κ hκi hκl
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hκ0 Wr κ hκi this
  have hρg0 : ρ g₀ ≠ 0 := fun h => hg0 (hρi (h.trans (map_zero ρ).symm))
  have d1 : ρ f ∣ ρ g₀ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ g₀) (ρ f) hρf0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).symm.dvd
  have d2 : ρ g₀ ∣ ρ f := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ f) (ρ g₀) hρg0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).dvd
  exact Ideal.span_singleton_eq_span_singleton.2
    (associated_of_dvd_dvd (dvd_of_map_dvd_of_finite V R' ρ hρi hρf g₀ f hg0 d2) (dvd_of_map_dvd_of_finite V R' ρ hρi hρf f g₀ hf0 d1))

end GlobalTheory.SgZero
