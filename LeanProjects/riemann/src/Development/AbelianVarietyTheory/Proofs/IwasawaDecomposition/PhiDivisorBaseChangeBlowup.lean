import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySabMapOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ArcGenOrder

theorem exists_moduli_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (K : Type) [Field K] (x : Sp K ⟶ X.X), Set.range x ⊆ Set.range X.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ X.j = x := by
  intro E _ _ _ H D l Xo c X K _ x hx
  have := c.fin
  have : NumberField c.F := {}
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
  let f : 𝓞 c.F →+* K := (Spec.preimage (x ≫ X.s)).hom
  have hxs : x ≫ X.s = spMap f := by simp only [spMap, f, CommRingCat.ofHom_hom, Spec.map_preimage]

  let p0 : Sp K := IsLocalRing.closedPoint K
  obtain ⟨q, hq⟩ := hx ⟨p0, rfl⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have e1 : (x ≫ X.s) p0 = (X.jQ ≫ pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)) q := by
      rw [← pullback.condition]
      simp only [Scheme.Hom.comp_apply]
      rw [← hq]; rfl
    have h1 : r ∈ ((x ≫ X.s) p0).asIdeal := by
      rw [hxs]
      show f r ∈ (IsLocalRing.closedPoint K).asIdeal
      rw [hr]; exact Ideal.zero_mem _
    rw [e1] at h1
    have h2 : algebraMap (𝓞 c.F) c.F r ∈ ((X.jQ ≫ pullback.snd _ _) q).asIdeal := h1
    rw [@Ideal.eq_bot_of_prime _ _ _ ((X.jQ ≫ pullback.snd _ _) q).isPrime, Ideal.mem_bot] at h2
    exact (map_eq_zero_iff _ hβ).1 h2
  let g : c.F →+* K := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f)
    fun y => IsUnit.mk0 _ ((map_ne_zero_iff f hf).2 (nonZeroDivisors.ne_zero y.2))
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = f := IsLocalization.lift_comp _
  have hsq : x ≫ X.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [hxs, ← hg]; simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let z : Sp K ⟶ pullback X.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift x (spMap g) hsq
  have hz : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _

  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hinj : Function.Injective (pullback.fst X.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (Scheme.Hom.isEmbedding _).injective
  have hrange : Set.range z ⊆ Set.range X.jQ := by
    intro w ⟨p, hp⟩
    obtain ⟨q', hq'⟩ := hx ⟨p, rfl⟩
    refine ⟨q', hinj ?_⟩
    rw [← hp]
    show X.j q' = (z ≫ pullback.fst _ _) p
    rw [hz]; exact hq'
  haveI := X.jQ_open
  refine ⟨IsOpenImmersion.lift X.jQ z hrange, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz]

theorem exists_lift_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ X.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ X.j = jK W ≫ χ → ∃ χZ : Sp W ⟶ Z.X, χZ ≫ π = χ ∧ jK W ≫ χZ = y ≫ Z.j := by
  intro E _ _ _ H D l Xo c X Z π hj hs W _ _ _ hW χ y hy
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : IsProper Z.s := GlobalTheory.ProperFamily.isProper_of_isProjOver Z.proj
  haveI : IsProper X.s := GlobalTheory.ProperFamily.isProper_of_isProjOver X.proj
  haveI : IsProper (π ≫ X.s) := by rw [hs]; infer_instance
  haveI : IsProper π := IsProper.of_comp π X.s
  have hv : ValuativeCriterion.Existence π := by
    have h : UniversallyClosed π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hp : (y ≫ Z.j) ≫ π = jK W ≫ χ := by rw [Category.assoc, hj, hy]
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨W, FractionRing W, y ≫ Z.j, χ, ⟨hp⟩⟩).exists_lift
  exact ⟨q, q2, q1⟩

theorem idlAlong_generic_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' b) [Module.Finite (𝓞 E) a.D₀.X], Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O' → ∀ χA : Sp (PowerSeries O') ⟶ X.X, χA ≫ X.s = spMap (PowerSeries.C (R := O')) ≫ spMap b → (∀ x : Sp (PowerSeries O'), χA x ∈ abLocus X.t.G ↔ PowerSeries.X ∉ x.asIdeal) → (∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χA x ∈ Set.range X.j) → X.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χA → ∀ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ a.be → idlAlong J (spMap (PowerSeries.map (algebraMap O' (FractionRing O'))) ≫ χA) ≤ Ideal.span {PowerSeries.X ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB O' _ _ _ _ b ϖ a _ hϖ hcpl χA h1 h2 h3 h4 m hm
  have hinjK : Function.Injective (algebraMap O' (FractionRing O')) := IsFractionRing.injective O' _
  haveI : CharZero (FractionRing O') := charZero_of_injective_algebraMap hinjK
  let g : PowerSeries O' →+* PowerSeries (FractionRing O') := PowerSeries.map (algebraMap O' (FractionRing O'))
  have hg : Function.Injective g := PowerSeries.map_injective _ hinjK
  have hW : CDvr (PowerSeries (FractionRing O')) := GlobalTheory.ArcData.cdvr_powerSeries _
  haveI : IsDiscreteValuationRing (PowerSeries (FractionRing O')) := hW.1

  have hgen : Set.range (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) ⊆ Set.range X.j := by
    rintro _ ⟨p, rfl⟩
    refine h3 _ fun hmem => ?_
    let ψ : PowerSeries O' →+* FractionRing (PowerSeries (FractionRing O')) :=
      (algebraMap (PowerSeries (FractionRing O')) _).comp g
    have hψ : Function.Injective ψ :=
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O')))).comp hg
    have e1 : jK (PowerSeries (FractionRing O')) ≫ spMap g = spMap ψ := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
    have e2 : (jK (PowerSeries (FractionRing O')) ≫ spMap g) p = spMap ψ p := by rw [e1]
    have hx : PowerSeries.C ϖ * PowerSeries.X ∈ (spMap ψ p).asIdeal := by
      rw [← e2]; exact hmem
    have hmem' : ψ (PowerSeries.C ϖ * PowerSeries.X) ∈ p.asIdeal := hx
    rw [hp, Ideal.mem_bot, map_eq_zero_iff _ hψ] at hmem'
    exact mul_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hϖ.ne_zero) PowerSeries.X_ne_zero hmem'

  obtain ⟨Wt⟩ := (X.hasArcData_iff _ _ _ _ _).1 h4
  obtain ⟨hL, hL₂, -, -, h5, -⟩ := GlobalTheory.allSixLaws
  have hmax : maximalIdeal O' = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hcpl' : IsAdicComplete (maximalIdeal O') O' := hmax ▸ hcpl
  have hR := (GlobalTheory.ArcData.powerSeries_dvr_admissible_X_ideal O' hcpl').1.1
  have hR' := (GlobalTheory.ArcData.admissible_maximal_ideal_of_complete_dvr_char_zero hW).1.1
  have hI : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map g ≤ maximalIdeal (PowerSeries (FractionRing O')) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, PowerSeries.map_X,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hu : g PowerSeries.X ≠ 0 := by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
  have hS : ∀ (F : Type) [Field F] (i : PowerSeries (FractionRing O') →+* F), Function.Injective i →
      ∃ σ : PowerSeries O' →+* PowerSeries F, Function.Injective σ ∧
        (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i (g (PowerSeries.C x)))) ∧
        ∀ r, PowerSeries.constantCoeff (σ r) = i (g r) := fun F _ i hi =>
    ⟨(PowerSeries.C (R := F)).comp (i.comp g), PowerSeries.C_injective.comp (hi.comp hg), fun _ => rfl,
      fun r => PowerSeries.constantCoeff_C _⟩
  obtain ⟨A⟩ := GlobalTheory.ArcSpecialise.specialise hL hL₂ GlobalTheory.twistBaseChange GlobalTheory.UnifPullGuards.unifBaseChange_holds h5 hR hR'
    PowerSeries.C_injective Wt h1 g hI hu hgen hS
  have hXirr : Irreducible (PowerSeries.X : PowerSeries (FractionRing O')) := PowerSeries.X_irreducible
  haveI : CharZero (PowerSeries (FractionRing O')) := charZero_of_injective_ringHom PowerSeries.C_injective
  have hfi : Function.Injective (g.comp (PowerSeries.C (R := O'))) := hg.comp PowerSeries.C_injective
  obtain ⟨be, hbe, hmon, hbeq⟩ := GlobalTheory.ArcOrder.exists_form hfi A hXirr 1 1
    (by show PowerSeries.map _ PowerSeries.X = _; rw [PowerSeries.map_X]; simp)

  obtain ⟨y, hy⟩ := exists_moduli_point E H D l Xo c X _ (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) hgen
  obtain ⟨χZ, hχZ, hjZ⟩ := exists_lift_of_generic E H D l Xo c X Z π hB.2.1 hB.2.2.1 _ hW (spMap g ≫ χA) y hy
  obtain ⟨mZ⟩ := GlobalTheory.T.nonempty_sabMap_of_compatible E H D l Xo c X Z π hB.2.1 hB.2.2.1
  obtain ⟨mA⟩ := GlobalTheory.TraitOrder.cancel hχZ mZ A.m
  have hr : Set.range (jK (PowerSeries (FractionRing O')) ≫ χZ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y p, by rw [hjZ]; rfl⟩
  have hprim : ∀ p : ℕ, p.Prime → IsUnit (p : PowerSeries (FractionRing O')) := fun p hp => by
    rw [← map_natCast (PowerSeries.C (R := FractionRing O'))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)).map _
  obtain ⟨m', hm', hid⟩ := GlobalTheory.TorRef.blowOrd_eqChar E H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB _ hW hprim
    PowerSeries.X hXirr χZ A.t mA A.P hr be hbe hmon

  have hev : (comb 0 φ (n * d') φ).evalZ be = (comb 0 φ (n * d') φ).evalZ a.be := by
    unfold InvFun.evalZ
    rw [← InvFun.eval_equiv _ A.e]
    congr 1
    funext u v
    rw [hbeq u v]
    simp
  have hmm : m' = m := by exact_mod_cast hm'.trans (hev.trans hm.symm)
  subst hmm
  rw [← hχZ, ← GlobalTheory.TorRef.idlAlong_comap, ← hB.2.2.2.2.1, hid]

end GlobalTheory.ArcGenOrder
