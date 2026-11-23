import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.ChartAt

theorem mem_genericPoints_of_forall_specializes {X : Scheme.{0}} (ε : X) (h : ∀ z, z ⤳ ε → z = ε) :
    ε ∈ genericPoints X := by
  have hc : irreducibleComponent ε ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents ε
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := ε)) isClosed_irreducibleComponent
  have e : ξ = ε := h ξ (hξ.specializes mem_irreducibleComponent)
  subst e
  change closure {ξ} ∈ irreducibleComponents X
  rw [hξ.def]
  exact hc

theorem forall_specializes_of_flat {X Y : Scheme.{0}} (g : Y ⟶ X) [Flat g] (ε : Y) (h : ∀ z, z ⤳ ε → z = ε) :
    ∀ z, z ⤳ g ε → z = g ε := by
  intro z hz
  obtain ⟨z', hz', e⟩ := Flat.generalizingMap g hz
  rw [← e, h z' hz']

theorem forall_specializes_fromSpec {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(Y, U))
    (hP : P.asIdeal ∈ minimalPrimes Γ(Y, U)) : ∀ z, z ⤳ hU.fromSpec P → z = hU.fromSpec P := by
  intro z hz
  have hr : z ∈ Set.range hU.fromSpec := hz.mem_open hU.fromSpec.isOpenEmbedding.isOpen_range ⟨P, rfl⟩
  obtain ⟨Q, rfl⟩ := hr
  have h1 : Q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 hz
  have h2 : (show PrimeSpectrum Γ(Y, U) from Q).asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h1
  have h3 := hP.2 ⟨PrimeSpectrum.isPrime Q, bot_le⟩ h2
  rw [show Q = P from PrimeSpectrum.ext (le_antisymm h2 h3)]

theorem exists_chart_at : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := by
  intro n N X Y Z sX sY q i hi hn hN hsX hsY hq he hs K _ y'
  let pt : Sp K := closedPoint (CommRingCat.of K)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y' pt))) isOpen_univ
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hU : IsAffineOpen (q ⁻¹ᵁ V₀) := hV₀.preimage q
  set U := q ⁻¹ᵁ V₀ with hUdef
  have hrange : Set.range y' ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨w, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim w pt]
    exact hxV
  let χ : Γ(Y, U) →+* K := (Spec.preimage (IsOpenImmersion.lift hU.fromSpec y' hrange)).hom
  have hχ : spMap χ ≫ hU.fromSpec = y' := by
    have : spMap χ = IsOpenImmersion.lift hU.fromSpec y' hrange := Spec.map_preimage _
    rw [this, IsOpenImmersion.lift_fac]
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨P₀, hP₀, hPχ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Γ(Y, U))) (J := RingHom.ker χ) bot_le
  obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(Y, U), P.asIdeal = P₀ := ⟨⟨P₀, hP₀.1.1⟩, rfl⟩
  have hmax := forall_specializes_fromSpec hU P hP₀
  have hgen : (sY (hU.fromSpec P)).asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY (hU.fromSpec P) := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    rw [← forall_specializes_of_flat sY _ hmax b hb]
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hsm : ψ.Smooth := by
    have : Smooth (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  haveI : Algebra.Smooth (cycAway N) Γ(Y, U) := hsm
  haveI : IsDedekindDomain (cycAway N) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N
  have hic : IsIntegrallyClosed (Γ(Y, U) ⧸ P.asIdeal) := isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (fun m _ => isDomain_and_isIntegrallyClosed_atPrime_of_smooth (cycAway N) m _) hP₀
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω :=
    ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  have hsurj : Function.Surjective f.rangeRestrict.toRingHom := f.rangeRestrict_surjective
  have hkerR : RingHom.ker f.rangeRestrict.toRingHom = P.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hφker, Subtype.ext_iff]
    rfl
  let χR : f.range →+* K := RingHom.liftOfSurjective f.rangeRestrict.toRingHom hsurj ⟨χ, hkerR.le.trans hPχ⟩
  have hχR : χR.comp f.rangeRestrict.toRingHom = χ := RingHom.liftOfSurjective_comp _ _ _
  have hfin : IsFinite (spMap f.rangeRestrict.toRingHom) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective _ hsurj)
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    spMap χR, i ''ᵁ V₀, spMap f.rangeRestrict.toRingHom ≫ hU.isoSpec.inv ≫ (q ∣_ V₀) ≫ (i.isoImage V₀).hom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV₀.image_of_isOpenImmersion i, inferInstance, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · exact IsIntegrallyClosed.of_equiv
      ((Ideal.quotEquivOfEq hkerR.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc, ← hχ, ← hχR, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) ∈ genericPoints X
    rw [hw]
    exact mem_genericPoints_of_forall_specializes _ (forall_specializes_of_flat q _ hmax)
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    have h1 := GlobalTheory.Poinc.Chart.stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec
      (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) (fun z => by
        obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact ⟨a, c, rfl⟩) _ rfl
    have e2 : spMap f.range.val.toRingHom ≫ (spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec) ≫ q ≫ i =
        (spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) ≫ hU.fromSpec ≫ q) ≫ i := by
      rw [← e]; simp only [Category.assoc]
    rw [e2, Scheme.Hom.stalkMap_comp]
    exact h1.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  · simp only [Category.assoc]
    rw [Scheme.Hom.isoImage_hom_ι, ← Category.assoc (q ∣_ V₀), morphismRestrict_ι, Category.assoc,
      ← Category.assoc hU.isoSpec.inv, hU.isoSpec_inv_ι]

end GlobalTheory.Poinc.ChartAt
