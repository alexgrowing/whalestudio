import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemAssociatedOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatPrincipalHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConeFormRegularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConeFormOrderStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.DivDescent

theorem exists_associated_of_divisor {A R : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (φ : A →+* R)
    (hφ : φ.Flat) (hloc : IsLocalHom φ) (h : R) (hh : h ≠ 0)
    (h1 : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ = ⊥ → h ∉ Q)
    (h2 : ∀ q : Ideal A, q ≠ ⊥ → ∃ n : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ = q →
      (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) =
        (q ^ n).map ((algebraMap R (Localization.AtPrime Q)).comp φ)) :
    ∃ a : A, Associated (φ a) h := by
  have loc := GlobalTheory.T.flat_principal_height_one φ hφ hloc h hh h1 h2
  by_cases hu : IsUnit h
  · exact ⟨1, by rw [map_one]; exact (associated_one_iff_isUnit.mpr hu).symm⟩
  have hhm : Ideal.span {h} ≤ maximalIdeal R := by
    rw [Ideal.span_singleton_le_iff_mem, mem_maximalIdeal, mem_nonunits_iff]; exact hu
  obtain ⟨Q, hQmin, -⟩ := Ideal.exists_minimalPrimes_le hhm
  haveI hQp : Q.IsPrime := hQmin.1.1
  have hhQ : h ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mp hQmin.1.2
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin) ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hh ((Ideal.mem_bot).mp hhQ)
  obtain ⟨d, hdJ, s0, hs0, hds⟩ := loc Q hQ1
  have hd0 : φ d ≠ 0 := by
    intro hd
    rw [hd, zero_dvd_iff] at hds
    exact (mul_ne_zero (fun hs : s0 = 0 => hs0 (by rw [hs]; exact Q.zero_mem)) hh) hds
  obtain ⟨c, hc⟩ := hdJ
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hd0 hc
  set J : Ideal A := (Ideal.span {h}).comap φ with hJ
  set K : Ideal A := (Ideal.span {d}).colon J with hK
  set J' : Ideal A := (Ideal.span {d}).colon K with hJ'
  have hKm : K.map φ = Ideal.span {c} := by
    rw [hK, GlobalTheory.T.flat_map_colon_ideal φ hφ, Ideal.map_span, Set.image_singleton]
    ext y
    rw [Submodule.mem_colon, Ideal.mem_span_singleton]
    constructor
    · intro hy
      apply GlobalTheory.dvd_of_forall_height_eq_one hc0
      intro P _ hP1 _
      obtain ⟨a, ⟨v, hv⟩, s, hsP, t, ht⟩ := loc P hP1
      have haJ : a ∈ J := by rw [hJ, Ideal.mem_comap, Ideal.mem_span_singleton]; exact ⟨v, hv⟩
      have hy' := hy (φ a) (Ideal.mem_map_of_mem φ haJ)
      rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
      obtain ⟨u, hu'⟩ := hy'
      refine ⟨s, hsP, u * t, ?_⟩
      apply mul_left_cancel₀ hh
      calc h * (s * y) = y * (s * h) := by ring
        _ = y * φ a * t := by rw [ht]; ring
        _ = φ d * u * t := by rw [hu']
        _ = h * (c * (u * t)) := by rw [hc]; ring
    · rintro ⟨w, rfl⟩ z hz
      have hz' : z ∈ Ideal.span {h} := Ideal.map_comap_le hz
      obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hz'
      rw [smul_eq_mul, Ideal.mem_span_singleton, hc]
      exact ⟨w * v, by ring⟩
  have hJ'm : J'.map φ = Ideal.span {h} := by
    rw [hJ', GlobalTheory.T.flat_map_colon_ideal φ hφ, Ideal.map_span, Set.image_singleton, hKm]
    ext y
    rw [Submodule.mem_colon, Ideal.mem_span_singleton]
    constructor
    · intro hy
      have hyc := hy c (Ideal.mem_span_singleton_self c)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hc] at hyc
      obtain ⟨k, hk⟩ := hyc
      exact ⟨k, mul_right_cancel₀ hc0 (by rw [hk]; ring)⟩
    · rintro ⟨k, rfl⟩ z hz
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hz
      rw [smul_eq_mul, Ideal.mem_span_singleton, hc]
      exact ⟨k * w, by ring⟩
  obtain ⟨a, -, ha⟩ := exists_mem_associated_of_map_eq φ J' hh hJ'm
  exact ⟨a, ha⟩

end GlobalTheory.DivDescent

namespace GlobalTheory.DivDescent

theorem exists_stalk_associated_chartFn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → Cn P.D.toPre.X m γ → InCone P.D.toPre γ → (∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φ.evalZ be) → ∀ h : R, h ≠ 0 → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (g : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → ∃ n : ℕ, (n : ℤ) = ℓ be ∧ Associated (g h) (ϖ ^ n)) → ∃ a : Z.X.presheaf.stalk (ξ (closedPoint R)), Associated ((Scheme.stalkClosedPointTo ξ).hom a) h := by
  intro E _ _ _ H D l Xo c Z Cn φf hC hL R _ _ _ ξ t hm P m γ ℓ hCN hEt hFU hTor hCn hIn hℓ h hh hord
  haveI : IsNoetherianRing R := hCN.1
  haveI : IsIntegrallyClosed R := hCN.2.1
  haveI : IsNoetherianRing (Z.X.presheaf.stalk (ξ (closedPoint R))) := isNoetherianRing_stalk Z _
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ).hom :=
    GlobalTheory.CdvrExt.isLocalHom_of_map_maximalIdeal _ hEt.2.1
  have hinj := GlobalTheory.CdvrExt.injective_of_flat_local (Scheme.stalkClosedPointTo ξ).hom hEt.1
  haveI : IsDomain (Z.X.presheaf.stalk (ξ (closedPoint R))) := Function.Injective.isDomain _ hinj
  exact exists_associated_of_divisor _ hEt.1 hloc h hh
    (GlobalTheory.T.local_cone_form_regular Z Cn φf hC hL ξ t hm P γ ℓ hCN hEt hFU hTor hCn hIn hℓ h hh hord)
    (GlobalTheory.T.local_cone_form_order Z Cn φf hC hL ξ t hm P γ ℓ hCN hEt hFU hTor hCn hIn hℓ h hh hord)

end GlobalTheory.DivDescent
