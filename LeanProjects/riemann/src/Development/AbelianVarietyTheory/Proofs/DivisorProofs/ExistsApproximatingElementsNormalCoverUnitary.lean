import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSystemOfOrderGeAlongTraitsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

theorem range_jK_spMap_subset : ∀ (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R), Function.Injective ρ → ∀ (X : Scheme.{0}) (χ : Sp V ⟶ X), Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro V R _ _ _ _ ρ hρ X χ x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem exists_elements_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  intro E _ _ _ H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V _ _ _ Cm hB ξ hξ N₁ M _ g z₁ ζ Φ y ρ e h U hUne hcov htr hmem K _ _ ev k₀ hk₀ hpt hdef ga hga
  obtain ⟨hρi, hρf, hζ, hst, -⟩ := hmem
  obtain ⟨hρl, hext⟩ := GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend V (Φ.V y) K ρ hρi hρf
  obtain ⟨ev₁, hev₁⟩ := hext ev
  have hcov' := hcov
  obtain ⟨-, -, hζg, -⟩ := hcov'
  obtain ⟨S₁, hS₁, p₁, sM, U₁, hft, hqc, hfl, hnorm, hprop, hdom, hcart, hU₁, hlift, hxi⟩ :=
    GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover E H Dw hpq l Xo c C J hJ S π hπ M g z₁ ζ hcov
  haveI := hS₁
  haveI : IsIntegrallyClosed (Φ.V y) := (Φ.cn y).2.1
  have hζ' : (spMap ρ ≫ ξ) ≫ π = spMap (Φ.ev y) ≫ ζ := by rw [hζ, Category.assoc]
  have hgen : Set.range (jK (Φ.V y) ≫ (spMap ρ ≫ ξ) ≫ π) ⊆ Set.range C.iF := by
    intro x hx
    obtain ⟨p, hp⟩ := range_jK_spMap_subset V (Φ.V y) ρ hρi _ (ξ ≫ π) (by simpa only [Category.assoc] using hx)
    simp only [Category.assoc] at hp
    rw [← hξ, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  obtain ⟨ξ₁, hξ₁p, hξ₁⟩ := hxi (Φ.V y) (spMap ρ ≫ ξ) (Φ.ev y) hζ' hgen
  have hcomp : spMap ev₁ ≫ spMap ρ = spMap ev := by
    rw [← hev₁, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have hpt' : ∀ p, (spMap ev₁ ≫ (spMap ρ ≫ ξ)) p = (spMap ρ ≫ ξ) (closedPoint (Φ.V y)) := by
    intro p
    rw [← Category.assoc, hcomp, hpt]
    change _ = ξ ((spMap ρ) (closedPoint (Φ.V y)))
    rw [spMap, Spec_closedPoint]
  have hdef' : GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ (spMap ρ ≫ ξ)) := by rwa [← Category.assoc, hcomp]
  obtain ⟨hpt₁, hdef₁⟩ := hξ₁ K ev₁ k₀ hk₀ hpt' hdef'
  obtain ⟨b', hb', hid⟩ := GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial E H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V Cm hB ξ hξ
  have hU₂ : ((U₁ ⊓ p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
    have h1 : ((p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
      obtain ⟨s, hs⟩ := (p₁.denseRange).exists_mem_open U.isOpen hUne
      exact ⟨s, hs⟩
    exact nonempty_preirreducible_inter U₁.isOpen (p₁ ⁻¹ᵁ U).isOpen hU₁ h1
  obtain ⟨g₀, hg₀, happ⟩ := GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation C.Z M S₁ sM p₁ g J hft hqc hfl hnorm hprop hdom hcart (U₁ ⊓ p₁ ⁻¹ᵁ U) hU₂ z₁ (Φ.V y) (Φ.ev y)
    (Φ.ev_loc y) ξ₁ hξ₁p
  have hpath : ξ₁ ≫ p₁ ≫ g = spMap ρ ≫ (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
    rw [← Category.assoc, hξ₁p, Category.assoc, ← hζg, ← Category.assoc, hζ]
    simp only [Category.assoc]
  have hkey : Ideal.span {g₀} = Ideal.span {∏ k, Φ.t y k ^ (2 * b' (h k))} := by
    rw [← hg₀, GlobalTheory.TorRef.idlAlong_comap, hpath, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, map_prod]
    congr 2
    exact (Equiv.prod_comp h _).symm.trans (Finset.prod_congr rfl fun j _ => by
      rw [map_pow, ← (hst j).1, ← pow_mul])
  have hδ : ∀ k, Φ.δ y k = GlobalTheory.PolFan.pull e.toLinearMap ((l.M' : ℤ) • Cm.δ (h k)) :=
    fun k => LinearMap.ext₂ fun a b => by rw [(hst k).2 a b]; rfl
  have hev : ∀ k, φ.evalZ (Φ.δ y k) = φ.evalZ ((l.M' : ℤ) • Cm.δ (h k)) := fun k => by
    rw [hδ k, evalZ_pull φ (r := e.toLinearMap) e.surjective]
  have hbdd : BddAct (H.bar : 𝓞 E → 𝓞 E) := (GlobalTheory.Poinc.bddAct_int_and_cm).2 E H
  have hM : 1 ≤ l.M' := GlobalTheory.LevelExist.M'_pos l
  have hδga : ∀ i, Φ.δ y i = ((l.M' : ℕ) : ℤ) • ga i := fun i => LinearMap.ext₂ fun a b => by
    rw [(hst i).2 a b]; simp [hga]
  refine ⟨ev₁, hev₁, (Scheme.stalkClosedPointTo ξ₁).hom.range, g₀, fun k => 2 * b' (h k),
    fun x hx => GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield S₁ (Φ.V y) ξ₁ K ev₁ k₀ hpt₁ hdef₁ x hx, fun k => ?_,
    Ideal.span_singleton_eq_span_singleton.1 hkey, ?_⟩
  · push_cast
    rw [hev k, hb' (h k)]
    ring
  intro D l' a hdom c' e'
  obtain ⟨e₁, he₁⟩ := happ D e'
  obtain ⟨f, hord, hlead⟩ := GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) hbdd (min Dw.p Dw.q) φ hφ 1 !![(1 : ℤ)] Φ.posW N₁ _ Φ y ga
    l.M' hM hδga (D * (2 * d)) l' a hdom c' (max e' e₁)
  have hord' : Φ.OrdGe φ (D * (2 * d)) e₁ f := fun y' hP hm i =>
    (sup_le_sup_left (α := Ideal (Φ.V y')) (Ideal.pow_le_pow_right (le_max_right e' e₁)) _) (hord y' hP hm i)
  obtain ⟨x, hx, hxe⟩ := he₁ f (by
    intro V' _ _ _ _ hc ξ' ev' hl hcomm hU
    have hj : jK V' ≫ spMap ev' = spMap ((algebraMap V' (FractionRing V')).comp ev') := by
      simp only [jK, spMap, ← Spec.map_comp]; rfl
    obtain ⟨y', hy'⟩ := hlift (FractionRing V') (jK V' ≫ ξ') ((algebraMap V' (FractionRing V')).comp ev')
      (by rw [Category.assoc, ← hcomm, ← Category.assoc, hj]) (fun x hx => (hU hx).1)
    have hUM : Set.range (jK V' ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
      rw [hcomm]
      rintro _ ⟨q, rfl⟩
      have := (hU ⟨q, rfl⟩).2
      rw [Scheme.Hom.comp_apply]
      exact this
    have htr' := GlobalTheory.T.mem_system_of_order_ge_along_traits GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c C φ d J hV M z₁ U ζ N₁ Φ htr V' hc ev' hl hUM y' hy' D e₁ f hord'
    have hpath' : ξ' ≫ p₁ ≫ g = spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b) := by
      rw [hζg, ← Category.assoc (spMap ev'), hcomm, Category.assoc]
    rwa [GlobalTheory.TorRef.idlAlong_comap, hpath'])
  refine ⟨x, hx, ?_⟩
  have h1 : Φ.ev y f - Φ.coefT y a c' * Φ.monoT y a ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    (sup_le_sup_left (α := Ideal (Φ.V y)) (Ideal.pow_le_pow_right (le_max_left e' e₁)) _) hlead
  have h2 : Φ.ev y f - x * g₀ ^ D ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    Ideal.mem_sup_right hxe
  have h3 := Ideal.sub_mem _ h1 h2
  convert h3 using 1
  ring

end GlobalTheory.USep
