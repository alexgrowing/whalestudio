import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import ReciprocityTheory.GaloisValuations.GlobalB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : AlgebraicClosure F) :
    e.O.valuation x < 1 ↔ e.w x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h : 0 < e.w x := e.w.pos hx
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, or_iff_right hx,
    e.mem_O, map_inv₀, not_le, one_lt_inv₀ h]

theorem exists_emb (K : Type) [Field K] [Algebra F K] [Module.Finite F K] (O : ValuationSubring K)
    (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (h : ∀ x : 𝓞 F, O.valuation (algebraMap F K (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ ψ : K →ₐ[F] AlgebraicClosure F, (∀ x ∈ O, e.w (ψ x) ≤ 1) ∧
      ∀ x, O.valuation x < 1 → e.w (ψ x) < 1 := by
  let ι : K →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing ((ι : K →+* AlgebraicClosure F).comp O.subtype)
  have hOF : ∀ x : 𝓞 F, algebraMap F K (x : F) ∈ O := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int O (x.isIntegral_coe.map (algebraMap F K).toIntAlgHom)
  have key : ∀ x : O, A.valuation (ι x) < 1 ↔ O.valuation x < 1 := fun x => by
    rw [← O.valuation_lt_one_iff]
    refine (A.valuation_lt_one_iff ⟨_, hA x⟩).symm.trans ?_
    exact not_congr (isUnit_map_iff (((ι : K →+* AlgebraicClosure F).comp O.subtype).codRestrict A.toSubring hA) x)
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (F := F) (A := A) (A' := e.O) (v := v)
    (fun x => by rw [← h, ← key ⟨_, hOF x⟩, ι.commutes])
    (fun x => by
      rw [valuation_lt_one_iff, e.w_alg]
      exact v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) x)
  have hm : ∀ x, g x ∈ e.O ↔ x ∈ A := fun x => by
    rw [← hg]; exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨(g : AlgebraicClosure F →ₐ[F] AlgebraicClosure F).comp ι, fun x hx => (e.mem_O _).1 ((hm _).2 (hA ⟨x, hx⟩)), fun x hx => ?_⟩
  have hxO : x ∈ O := (O.valuation_le_one_iff x).1 hx.le
  have := (key ⟨x, hxO⟩).2 hx
  rw [← valuation_lt_one_iff]
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at this ⊢
  refine this.imp (fun h0 => ?_) fun h1 h2 => h1 ((hm _).1 ?_)
  · change g (ι x) = 0
    rw [h0, map_zero]
  · rw [map_inv₀]; exact h2

theorem exists_point (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S]
    [Algebra.FiniteType (𝓞 F) S] (hinj : Function.Injective (algebraMap (𝓞 F) S)) (m : Ideal S)
    [hm : m.IsMaximal] (hmO : m.comap (algebraMap (𝓞 F) S) ≠ ⊥) {t : S} (ht : t ≠ 0) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : S →+* AlgebraicClosure F),
      (∀ a : 𝓞 F, φ (algebraMap _ _ a) = algebraMap F _ (a : F)) ∧ (∀ s, e.w (φ s) ≤ 1) ∧
      (∀ s ∈ m, e.w (φ s) < 1) ∧ φ t ≠ 0 := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (𝓞 F) S
  let v : HeightOneSpectrum (𝓞 F) := ⟨m.comap (algebraMap (𝓞 F) S), inferInstance, hmO⟩
  obtain ⟨e⟩ := (GlobalTheory.TrueGeo.ExtConj.main F).1 v
  obtain ⟨π, hπm, hπ⟩ := (Submodule.ne_bot_iff _).1 hmO
  have hπ' : algebraMap (𝓞 F) S π ≠ 0 := fun h => hπ (hinj (h.trans (map_zero _).symm))
  obtain ⟨q, hqU, hqm, hht⟩ := exists_mem_height_map_le_one m
    (PrimeSpectrum.basicOpen (algebraMap (𝓞 F) S π * t)).isOpen ⟨⊥, mul_ne_zero hπ' ht, bot_le⟩
  have hqπ : algebraMap (𝓞 F) S π ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_right _ _ h)
  have hqt : t ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_left _ _ h)
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  have hinj' : Function.Injective (algebraMap (𝓞 F) (S ⧸ q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have h1 : a ∈ q.asIdeal.comap (algebraMap (𝓞 F) S) :=
      (Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal) (a := algebraMap (𝓞 F) S a)).mp ha
    have h2 : (q.asIdeal.comap (algebraMap (𝓞 F) S)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance fun h => ha0 (by simpa [h] using h1)
    have h3 := h2.eq_of_le v.isPrime.ne_top (Ideal.comap_mono hqm)
    exact hqπ (h3.ge hπm)
  obtain ⟨K, _, _, _, O, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one (K := F)
    hinj' (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ (Ideal.mem_map_of_mem _ hπm)
  have key : ∀ s : S, O.valuation (φ (Ideal.Quotient.mk _ s)) < 1 ↔ s ∈ m := fun s => by
    rw [← O.valuation_lt_one_iff, ← Ideal.mem_comap, hφm, ← Ideal.mem_comap, hcomap]
  obtain ⟨ψ, h₁, h₂⟩ := exists_emb K O v e fun x => by
    refine Iff.trans ?_ (key (algebraMap _ _ x))
    rw [show algebraMap F K (x : F) = _ from (hφ x).symm]
    rfl
  refine ⟨v, e, (ψ : K →+* AlgebraicClosure F).comp (O.subtype.comp (φ.comp (Ideal.Quotient.mk _))), fun a => ?_,
    fun s => h₁ _ (φ _).2, fun s hs => h₂ _ ((key s).2 hs), fun h => hqt ?_⟩
  · exact (congrArg ψ (hφ a)).trans (ψ.commutes _)
  · have : φ (Ideal.Quotient.mk _ t) = 0 := Subtype.ext ((map_eq_zero ψ).1 h)
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff φ hφi).1 this)

theorem exists_overring (R K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (h : K) (hint : ¬ IsIntegral R h) :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra R S) (_ : Algebra.FiniteType R S)
      (t : S), Function.Injective (algebraMap R S) ∧ t ≠ 0 ∧ Ideal.span {t} ≠ ⊤ ∧
      ∀ a b, algebraMap R K a * h = algebraMap R K b → algebraMap R S a = algebraMap R S b * t := by
  have h0 : h ≠ 0 := fun e => hint (e ▸ isIntegral_zero)
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  let := invertibleOfNonzero h0
  refine ⟨Algebra.adjoin R {h⁻¹}, inferInstance, inferInstance, inferInstance,
    Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton _),
    ⟨h⁻¹, Algebra.subset_adjoin rfl⟩,
    fun a b e => IsFractionRing.injective R K (congrArg Subtype.val e),
    fun e => inv_ne_zero h0 (congrArg Subtype.val e), fun eq => hint ?_, fun a b e => Subtype.ext ?_⟩
  · have ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top h⁻¹
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_sup_right)
    exact ⟨p, by simpa [Polynomial.Monic, sub_eq_zero] using hp, hpx⟩
  · change algebraMap R K a = algebraMap R K b * h⁻¹
    rw [← e, mul_inv_cancel_right₀ h0]

theorem isIntegral_of_points (R K : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Algebra.FiniteType (𝓞 F) R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hinj : Function.Injective (algebraMap (𝓞 F) R)) (h : K)
    (hgen : ∀ P : Ideal R, P.IsPrime → P.comap (algebraMap (𝓞 F) R) = ⊥ →
      ∃ a ∉ P, ∃ b, algebraMap R K a * h = algebraMap R K b)
    (hpt : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* AlgebraicClosure F),
      (∀ a : 𝓞 F, φ (algebraMap _ _ a) = algebraMap F _ (a : F)) → (∀ s, e.w (φ s) ≤ 1) →
      ∀ a b, algebraMap R K a * h = algebraMap R K b → φ a ≠ 0 → e.w (φ b) ≤ e.w (φ a)) :
    IsIntegral R h := by
  by_contra hint
  obtain ⟨S, _, _, _, _, t, hRS, ht, hne, hab⟩ := exists_overring R K h hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have htm : t ∈ m := hle (Ideal.subset_span rfl)
  let : Algebra (𝓞 F) S := ((algebraMap R S).comp (algebraMap (𝓞 F) R)).toAlgebra
  have : IsScalarTower (𝓞 F) R S := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (𝓞 F) S := .trans (S := R) inferInstance inferInstance
  obtain ⟨v, e, φ, h₁, h₂, h₃, h₄⟩ := exists_point (F := F) S (hRS.comp hinj) m (fun hb => by
    obtain ⟨a, ha, b, e⟩ := hgen (m.comap (algebraMap R S)) inferInstance
      ((Ideal.comap_comap _ _).trans hb)
    exact ha (by rw [Ideal.mem_comap, hab a b e]; exact m.mul_mem_left _ htm)) ht
  obtain ⟨a, ha, b, hb⟩ := hgen (RingHom.ker (φ.comp (algebraMap R S))) (RingHom.ker_isPrime _)
    (eq_bot_iff.2 fun x hx => by
      have : algebraMap F (AlgebraicClosure F) (x : F) = 0 := (h₁ x).symm.trans hx
      simpa using this)
  have h₅ := hpt v e (φ.comp (algebraMap R S)) h₁ (fun s => h₂ _) a b hb ha
  have h₆ : e.w (φ (algebraMap R S a)) = e.w (φ (algebraMap R S b)) * e.w (φ t) := by
    rw [hab a b hb, map_mul, map_mul]
  have h₇ : 0 < e.w (φ (algebraMap R S a)) := e.w.pos ha
  have h₈ := h₃ t htm
  have h₉ := e.w.nonneg (φ t)
  change e.w (φ (algebraMap R S b)) ≤ e.w (φ (algebraMap R S a)) at h₅
  nlinarith

theorem regAt_of_points {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 F)) [LocallyOfFiniteType p]
    (hN : Geo.Tor.IsNormalScheme X) (hp : (p (genericPoint X)).asIdeal = ⊥) (U : X.Opens)
    (h : X.functionField) (hgen : ∀ x ∈ U, (p x).asIdeal = ⊥ → RegAt x h)
    (hpt : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (spMap e.O.subtype ≫ yt) h) ≤ 1) :
    ∀ x ∈ U, RegAt x h := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
  replace hW : IsAffineOpen W := hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let ρ := Spec.preimage (hW.fromSpec ≫ p)
  have hρ : Spec.map ρ = hW.fromSpec ≫ p := Spec.map_preimage _
  let : Algebra (𝓞 F) Γ(X, W) := ρ.hom.toAlgebra
  have hft : Algebra.FiniteType (𝓞 F) Γ(X, W) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ρ)).mp (hρ ▸ inferInstance)
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  have hP (P : PrimeSpectrum Γ(X, W)) :
      (p (hW.fromSpec P)).asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) Γ(X, W)) := by
    exact congrArg (fun q : Spec Γ(X, W) ⟶ Sp (𝓞 F) => (q P).asIdeal) hρ.symm
  have hPW (P : PrimeSpectrum Γ(X, W)) : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
  have hfn (a : Γ(X, W)) : algebraMap _ X.functionField a = fnOf W (gen_mem hxW) a := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) Γ(X, W)) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot, eq_bot_iff, ← hp]
    obtain ⟨P, hP'⟩ := hW.range_fromSpec.ge (gen_mem hxW)
    rw [← hP']
    exact (Ideal.comap_mono bot_le).trans (hP P).ge
  have hint : IsIntegral Γ(X, W) h := by
    refine isIntegral_of_points (F := F) _ _ hinj h (fun P hPp hP0 => ?_)
      fun v e φ h₁ h₂ a b hab ha => ?_
    · obtain ⟨c, rfl⟩ := hgen _ (hWU (hPW ⟨P, hPp⟩)) ((hP ⟨P, hPp⟩).trans hP0)
      let := X.presheaf.algebra_section_stalk (⟨_, hPW ⟨P, hPp⟩⟩ : W)
      have := hW.isLocalization_stalk' ⟨P, hPp⟩ (hPW ⟨P, hPp⟩)
      obtain ⟨⟨b, a⟩, e⟩ := @IsLocalization.surj _ _ P.primeCompl _ _ _ this c
      refine ⟨a, a.2, b, ?_⟩
      rw [hfn, hfn, ← algebraMap_germ (hPW ⟨P, hPp⟩), ← algebraMap_germ (hPW ⟨P, hPp⟩), ← map_mul,
        mul_comm]
      exact congrArg _ e
    · let φ' : Γ(X, W) →+* e.O := φ.codRestrict e.O fun s => (e.mem_O _).2 (h₂ s)
      have e₁ : spMap e.O.subtype ≫ Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec =
          Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) ≫ p =
          spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
        rw [Category.assoc, ← hρ, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        exact h₁ a
      have h₃ := hpt v e (Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec) (e₁ ▸ e₂)
        ((Points.le_preimage_specMap_fromSpec hW _).trans (Scheme.Hom.preimage_mono _ hWU))
      rw [e₁] at h₃
      have h₄ := Points.le_preimage_specMap_fromSpec hW (CommRingCat.ofHom φ)
      have h₅ := (Points.le_preimage_iff _ _).1 h₄
      have h₆ (c : Γ(X, W)) : valAt (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec)
          (algebraMap _ X.functionField c) = φ c := by
        rw [hfn, valAt_fnOf h₅, Points.valR_eq _ _ h₄, Points.valMap_specMap_fromSpec]
        rfl
      have h₇ : RegAt (below (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec)) h := by
        refine hgen _ (hWU h₅) ?_
        refine (congrArg (fun q : Sp (AlgebraicClosure F) ⟶ Sp (𝓞 F) =>
          (q (IsLocalRing.closedPoint (AlgebraicClosure F))).asIdeal) e₂).trans ?_
        change Ideal.comap (algebraMap (𝓞 F) F) (Ideal.comap (algebraMap F (AlgebraicClosure F))
          (IsLocalRing.maximalIdeal _)) = ⊥
        rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _
          (algebraMap F (AlgebraicClosure F)).injective,
          Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)]
      rw [← h₆ b, ← hab, valAt_mul (f := algebraMap _ X.functionField a) (regAt_fnOf h₅ _ _) h₇, h₆,
        map_mul]
      exact mul_le_of_le_one_right (e.w.nonneg _) h₃
  let := X.presheaf.algebra_section_stalk (⟨x, hxW⟩ : W)
  have : IsScalarTower Γ(X, W) (X.presheaf.stalk x) X.functionField :=
    .of_algebraMap_eq fun a => (algebraMap_germ hxW a).symm
  have := (hN x).2
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (hint.tower_top (A := X.presheaf.stalk x))

theorem real_norm {β P c T : ℝ} {τ k n : ℕ} (hn : 0 < n) (hT : 0 ≤ T)
    (e : T = β ^ 2 * (Real.exp (-(2 * k * n * c)) * P ^ k) ^ τ) :
    Real.exp (-(((τ * k * n : ℕ) : ℝ) * c)) * ((β ^ n) ^ 2 * P ^ (τ * k * n)) ^ (1 / (2 * (n : ℝ))) =
      Real.sqrt T := by
  have h₁ : (β ^ n) ^ 2 * P ^ (τ * k * n) =
      (Real.sqrt T * Real.exp (((τ * k * n : ℕ) : ℝ) * c)) ^ (2 * n) := by
    have h₂ : Real.exp (-(2 * k * n * c)) ^ (τ * n) * Real.exp (((τ * k * n : ℕ) : ℝ) * c) ^ (2 * n) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_one_iff]
      push_cast
      ring
    rw [mul_pow, pow_mul (Real.sqrt T), Real.sq_sqrt hT, e]
    calc _ = (β ^ n) ^ 2 * P ^ (τ * k * n) * 1 := (mul_one _).symm
      _ = _ := by rw [← h₂]; ring
  have h₃ : 1 / (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ)⁻¹ := by push_cast; rw [one_div]
  rw [h₁, h₃, Real.pow_rpow_inv_natCast (by positivity) (by omega), mul_left_comm, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, mul_one]

section Local

variable {Z : Scheme.{0}} [IsIntegral Z] {D : CartierDiv Z} {x : Z} {u g : Z.functionFieldˣ}
  {f : Z.functionField} {k τ : ℕ}

theorem unitAt_quot (hu : D.IsEqn x u) (hg : (k • D).IsEqn x g) :
    UnitAt x ((u : Z.functionField)⁻¹ ^ k * g) := by
  have := (hu.nsmul k).iff_unitAt.1 hg
  rwa [div_eq_inv_mul, Units.val_pow_eq_pow_val, ← inv_pow] at this

theorem mul_pow_eq (f : Z.functionField) (u g : Z.functionFieldˣ) (k τ : ℕ) :
    f * g ^ τ = f * u ^ (τ * k) * ((u : Z.functionField)⁻¹ ^ k * g) ^ τ := by
  have := u.ne_zero
  rw [mul_comm τ, pow_mul, mul_assoc, ← mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ this, one_pow,
    one_mul]

theorem regAt_iff (hu : D.IsEqn x u) (hg : (k • D).IsEqn x g) :
    RegAt x (f * u ^ (τ * k)) ↔ RegAt x (f * g ^ τ) := by
  have h₁ := hg.nsmul τ
  rw [← mul_nsmul'] at h₁
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← h₁.regularAt_iff,
    ← (hu.nsmul _).regularAt_iff]

end Local

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem mem_secs_iff : f ∈ A.secs (τ * k * A.n) ↔
    ∀ x, RegAt x (f * (eqn A.D x : Y.Fn) ^ (τ * k)) := by
  refine Var.mem_riemannRochSpace_iff_regularAt_everywhere.trans (forall_congr' fun x => ?_)
  have hu : A.D.IsEqn x (eqn A.D x) := (A.D.exists_isEqn x).choose_spec
  rw [(hu.nsmul _).regularAt_iff, Units.val_pow_eq_pow_val, pow_mul, ← mul_pow]
  exact ⟨regAt_of_pow (have := Y.isNormalScheme; inferInstance) A.n.pos, fun h => regAt_pow h _⟩

theorem nrmInf_eq (σ : F →+* ℂ) (y : Pts Y σ) {g : Y.Fnˣ} (hg : (k • A.D).IsEqn (under y) g) {φ : ℝ}
    (hφ : ∀ f : Y.Fn, (k • A.D).RegularAt (under y) f →
      Real.exp (-(2 * k * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
        ‖ratVal (f * (g : Y.Fn)) y‖ ^ 2 * Real.exp (-φ))
    (hf : RegAt (under y) (f * g ^ τ)) :
    A.nrmInf σ (τ * k * A.n) f y =
      Real.sqrt (‖valAt y.1 (f * g ^ τ)‖ ^ 2 * Real.exp (-(τ * φ))) := by
  obtain ⟨u, hu⟩ := A.D.exists_isEqn (under y)
  have hw := unitAt_quot hu hg
  have hb := (regAt_iff hu hg).2 hf
  have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hu
  have hreg (N : ℕ) : (N • A.D).RegularAt (under y) ((u : Y.Fn)⁻¹ ^ N) := by
    have := (CartierDiv.isEqn_iff_generatesAt_inv.1 (hu.nsmul N)).regularAt
    rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
  have h₁ := hφ _ (hreg k)
  rw [C.pn_mPow Y σ A.D k _ _ y hgen, ratVal_eq_valAt y hw.regAt] at h₁
  have h₂ := C.pn_mul Y σ _ (C.mPow Y σ A.D (τ * k * A.n) (A.m σ)) _ _ y (regAt_pow hb A.n)
    (hreg (τ * k * A.n))
  have e : (f * (u : Y.Fn) ^ (τ * k)) ^ (A.n : ℕ) * (u : Y.Fn)⁻¹ ^ (τ * k * A.n) = f ^ (A.n : ℕ) := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← mul_pow, mul_inv_cancel₀ u.ne_zero, one_pow, mul_one]
  rw [e, C.pn_mPow Y σ A.D _ _ _ y hgen, ratVal_eq_valAt y (regAt_pow hb _), valAt_pow hb,
    norm_pow] at h₂
  rw [Adl.nrmInf, h₂]
  refine real_norm A.n.pos (by positivity) ?_
  rw [h₁, mul_pow_eq f u g k τ, valAt_mul hb (regAt_pow hw.regAt _), valAt_pow hw.regAt, norm_mul,
    norm_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, mul_neg]
  ring

theorem nrmFin_eq {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) {g : Y.Fnˣ}
    (hg : (k • A.D).IsEqn (below y.1) g)
    (hl : k * A.lg v e y =
      Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ k * g : Y.Fnˣ) : Y.Fn))))
    (hf : RegAt (below y.1) (f * g ^ τ)) :
    A.nrmFin v (τ * k * A.n) f e y = e.w (valAt y.1 (f * g ^ τ)) := by
  have hu : A.D.IsEqn _ (eqn A.D (below y.1)) := (A.D.exists_isEqn (below y.1)).choose_spec
  have hw := unitAt_quot hu hg
  have hb := (regAt_iff hu hg).2 hf
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] at hl
  have h₁ : ((τ * k * A.n : ℕ) : ℝ) * A.lg v e y / ((A.n : ℕ) : ℝ) = τ * (k * A.lg v e y) := by
    push_cast
    field_simp
  rw [Adl.nrmFin, pow_mul, ← mul_pow, valAt_pow hb, map_pow, one_div,
    Real.pow_rpow_inv_natCast (e.w.nonneg _) A.n.ne_zero, h₁, hl, Real.exp_nat_mul,
    Real.exp_log (e.w.pos (valAt_ne_zero hw)), mul_pow_eq f (eqn A.D (below y.1)) g k τ,
    valAt_mul hb (regAt_pow hw.regAt _), valAt_pow hw.regAt, map_mul, map_pow]

theorem exists_lift (M : Model Y) {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) :
    ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j := by
  have : IsProper M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  let ρ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict
    e.O fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int e.O
      (x.isIntegral_coe.map (algebraMap F (AlgebraicClosure F)).toIntAlgHom)
  have hex : ValuativeCriterion.Existence M.p := by
    have h : UniversallyClosed M.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have w : (y.1 ≫ M.j) ≫ M.p = spMap (algebraMap e.O (AlgebraicClosure F)) ≫ spMap ρ := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hex
    { R := e.O, K := AlgebraicClosure F, i₁ := y.1 ≫ M.j, i₂ := spMap ρ, commSq := ⟨w⟩ }
  exact ⟨l.l, l.fac_left⟩

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem exists_isRatSec_of_pull {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (j : Z ⟶ X)
    [IsPreimmersion j] (hη : j (genericPoint Z) ⤳ genericPoint X) {L : LB X}
    {r : (L.pull j).ι → Z.functionFieldˣ} (hr : IsRatSec (L.pull j) r) :
    ∃ r' : L.ι → X.functionFieldˣ, IsRatSec L r' ∧
      ∀ c : (L.pull j).ι, fnMap j hη (r' (c PUnit.unit)) = r c := by
  choose t ht using fun i : L.ι => fnMap_surjective j hη (r fun _ => i)
  have h0 (i : L.ι) : t i ≠ 0 := fun e => (r fun _ => i).ne_zero (by rw [← ht, e, map_zero])
  refine ⟨fun i => Units.mk0 _ (h0 i), fun i i' h => (fnMap j hη).injective ?_, fun c => ht _⟩
  have h₁ : genericPoint Z ∈ j ⁻¹ᵁ (L.U i ⊓ L.U i') := hη.mem_open (L.U i ⊓ L.U i').isOpen h
  have h₂ : genericPoint Z ∈ (L.pull j).U (fun _ => i) ⊓ (L.pull j).U (fun _ => i') :=
    ⟨Set.mem_iInter.2 fun _ => h₁.1, Set.mem_iInter.2 fun _ => h₁.2⟩
  have l : (L.pull j).U (fun _ => i) ⊓ (L.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (L.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (L.g i i')) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [map_mul, Units.val_mk0, Units.val_mk0, ht, ht, fnMap_fnOf j hη h h₁, hr _ _ h₂, e]
  exact congrArg (· * _) (fnOf_resG l h₂ _)

set_option maxHeartbeats 1600000 in

theorem small_equiv_smallSec : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F)
    (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+), A.Induced M L k 0 →
    Geo.Tor.IsNormalScheme M.X → ∀ τ : ℕ, Nonempty (A.small (τ * k * A.n) ≃ (L.pow τ).smallSec) := by
  intro F _ _ C Y A M L k ⟨_, r, hr, hinf, hfin⟩ hN τ
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have : LocallyOfFiniteType M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  have hη := j_gen_specializes M
  obtain ⟨r', hr', e'⟩ := exists_isRatSec_of_pull M.j hη hr.isRatSec
  have hP := presents_divOfRatSec (L.pow τ).isLB (isRatSec_pow hr' τ)
  have hmem {x : Y.X} {c : PUnit → L.B.ι} (h : M.j x ∈ L.B.U (c PUnit.unit)) :
      x ∈ (L.B.pull M.j).U c := Set.mem_iInter.2 fun _ => h
  have hpow {x : M.X} {c : PUnit → L.B.ι} :
      x ∈ (lbPow L.B τ).U c ↔ x ∈ L.B.U (c PUnit.unit) :=
    ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have hmap (t : M.X.functionField) (c : PUnit → L.B.ι) : fnMap M.j hη t * (r c : Y.Fn) ^ τ =
      fnMap M.j hη (t * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ)) := by
    rw [map_mul, Units.val_pow_eq_pow_val, map_pow, e' c]
  have hreg (t : M.X.functionField) (x : Y.X) (c : PUnit → L.B.ι)
      (h : M.j x ∈ L.B.U (c PUnit.unit)) :
      RegAt x (fnMap M.j hη t * (eqn A.D x : Y.Fn) ^ (τ * k)) ↔
        RegAt (M.j x) (t * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ)) := by
    rw [regAt_iff (u := eqn A.D x) (A.D.exists_isEqn x).choose_spec (hr.isEqn c x (hmem h)), hmap, regAt_fnMap_iff]
  have hF (t : M.X.functionField) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y)
      (yt : Sp e.O ⟶ M.X) (c : PUnit → L.B.ι) (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j)
      (hc : ⊤ ≤ yt ⁻¹ᵁ L.B.U (c PUnit.unit))
      (ht : RegAt (M.j (below y.1)) (t * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ))) :
      A.nrmFin v (τ * k * A.n) (fnMap M.j hη t) e y = e.w (valAt (spMap e.O.subtype ≫ yt)
        (t * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ))) := by
    have h₁ : M.j (below y.1) ∈ L.B.U (c PUnit.unit) := by
      change below (y.1 ≫ M.j) ∈ _
      rw [← h]
      exact hc (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
    rw [nrmFin_eq A e y (hr.isEqn c _ (hmem h₁)) (by simpa using hfin v e y yt c h hc)
      (by rwa [hmap, regAt_fnMap_iff]), hmap, valAt_fnMap _ _ _ ht, h]
  have hI (s : (L.pow τ).B.Sec) (σ : F →+* ℂ) (y : Pts Y σ)
      (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))) (h : y'.1 = y.1 ≫ M.j) :
      A.nrmInf σ (τ * k * A.n) (fnMap M.j hη (hP.rat s)) y ≤ 1 ↔
        ((L.pow τ).φ _).nsq (CxPts.secVal M.p _ s) y' ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_chart L.isLB (M.j (under y))
    let c : PUnit → L.B.ι := fun _ => i
    have h₁ : below (y.1 ≫ M.j) ∈ (lbPow L.B τ).U c := hpow.2 hi
    have h₂ := hP.rat_mul s c (gen_mem h₁)
    have h₃ : RegAt (M.j (below y.1)) (hP.rat s * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ)) :=
      h₂ ▸ regAt_fnOf h₁ _ _
    have h₄ : y' ∈ CxPts.ptsIn M.p _ ((lbPow L.B τ).U c) := CxPts.mem_ptsIn.2 (h ▸ h₁)
    rw [nrmInf_eq A σ y (hr.isEqn c _ (hmem hi)) (fun f => hinf σ y y' c f h (hmem hi))
      (by rwa [hmap, regAt_fnMap_iff]), hmap, valAt_fnMap _ _ _ h₃, Real.sqrt_le_left zero_le_one, one_pow,
      Weight.nsq_eq _ (CxPts.secVal_mem s) h₄]
    refine iff_of_eq (congrArg (· ≤ (1 : ℝ)) (congrArg₂ (fun a b => ‖a‖ ^ 2 * Real.exp (-b)) ?_ ?_))
    · refine (congrArg _ h₂).trans ((valAt_fnOf h₁ _ _).trans ?_)
      rw [← h]
      rfl
    · exact ((L.φ _).zpow_φ τ c y').symm
  have hto (s : (L.pow τ).smallSec) : fnMap M.j hη (hP.rat s.1) ∈ A.small (τ * k * A.n) := by
    have h₀ (x : M.X) (c : PUnit → L.B.ι) (h : x ∈ L.B.U (c PUnit.unit)) :
        RegAt x (hP.rat s.1 * (r' (c PUnit.unit) ^ τ : M.X.functionFieldˣ)) :=
      hP.rat_mul s.1 c (gen_mem (hpow.2 h)) ▸ regAt_fnOf (hpow.2 h) _ _
    refine ⟨(mem_secs_iff A).2 fun x => ?_, fun σ y => ?_, fun v e y => ?_⟩
    · obtain ⟨i, hi⟩ := exists_chart L.isLB (M.j x)
      exact (hreg _ x (fun _ => i) hi).2 (h₀ _ (fun _ => i) hi)
    · exact (hI s.1 σ y ⟨y.1 ≫ M.j, by
        rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp]; rfl⟩ rfl).2 (s.2 _ _)
    · obtain ⟨yt, h⟩ := exists_lift M e y
      obtain ⟨i, hi⟩ := exists_chart L.isLB (yt (IsLocalRing.closedPoint e.O))
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ (lbPow L.B τ).U fun _ => i := (Points.le_preimage_iff _ _).2 (hpow.2 hi)
      have h₂ : below (spMap e.O.subtype ≫ yt) ∈ (lbPow L.B τ).U fun _ => i :=
        h₁ (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
      have h₃ : below (y.1 ≫ M.j) ∈ (lbPow L.B τ).U fun _ => i := h ▸ h₂
      rw [hF _ v e y yt (fun _ => i) h ((Points.le_preimage_iff _ _).2 hi) (h₀ _ _ (hpow.1 h₃))]
      refine (e.mem_O _).1 ?_
      have h₄ := (congrArg (valAt (spMap e.O.subtype ≫ yt))
        (hP.rat_mul s.1 (fun _ => i) (gen_mem h₂))).trans ((valAt_fnOf h₂ _ _).trans
          (Points.valR_spMap_comp _ _ _ h₁ _))
      exact h₄ ▸ Subtype.coe_prop _
  refine ⟨(Equiv.ofBijective (fun s => (⟨_, hto s⟩ : A.small (τ * k * A.n))) ⟨fun s s' h => Subtype.ext (hP.rat_injective
    ((fnMap M.j hη).injective (congrArg Subtype.val h))), ?_⟩).symm⟩
  rintro ⟨f, hf, h₁, h₂⟩
  obtain ⟨t, rfl⟩ := fnMap_surjective M.j hη f
  have h₀ (x : Y.X) (c : PUnit → L.B.ι) (h : M.j x ∈ L.B.U (c PUnit.unit)) :=
    (hreg t x c h).1 ((mem_secs_iff A).1 hf x)
  obtain ⟨s, rfl⟩ := hP.exists_rat_eq (f := t) (CartierDiv.mem_sections.2 fun x => by
    obtain ⟨c, hc⟩ := exists_chart (L.pow τ).isLB x
    refine ⟨_, hP.isEqn c x hc, regAt_of_points M.p hN (asIdeal_p_gen M) (L.B.U (c PUnit.unit)) _
      (fun z hz h => ?_) (fun v e yt h hyt => ?_) x (hpow.1 hc)⟩
    · obtain ⟨z, rfl⟩ := mem_range_j M h
      exact h₀ z c hz
    · let y : AlgPt Y := ⟨M.pb.lift _ _ h, M.pb.lift_snd _ _ _⟩
      have e₁ : spMap e.O.subtype ≫ yt = y.1 ≫ M.j := (M.pb.lift_fst _ _ h).symm
      have e₂ : below (y.1 ≫ M.j) ∈ L.B.U (c PUnit.unit) :=
        e₁ ▸ hyt (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
      exact (hF t v e y yt c e₁ hyt (h₀ _ c e₂)).ge.trans (h₂ v e y))
  refine ⟨⟨s, fun σ' y' => ?_⟩, rfl⟩
  have hσ : Function.Injective σ' := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  obtain ⟨σ, rfl⟩ : ∃ σ : F →+* ℂ, σ' = σ.comp (algebraMap (𝓞 F) F) :=
    ⟨IsFractionRing.lift hσ, RingHom.ext fun a => (IsFractionRing.lift_algebraMap hσ a).symm⟩
  have w : y'.1 ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [y'.2, ← Spec.map_comp]; rfl
  exact (hI s σ ⟨M.pb.lift _ _ w, M.pb.lift_snd _ _ _⟩ y' (M.pb.lift_fst _ _ w).symm).1 (h₁ _ _)

end GlobalTheory.TrueGeo.SmallSec
