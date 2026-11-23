import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FrameCmp

def ev {Y : Scheme.{0}} {R : Type} [CommRing R] (τ : Y ⟶ Sp R) (y : Y) : R →+* Y.presheaf.stalk y :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ τ.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom

theorem ev_eq_gs {Y : Scheme.{0}} {R : Type} [CommRing R] (τ : Y ⟶ Sp R) (y : Y) (a : R) :
    ev τ y a = gs τ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := (gs_eq τ y ⊤ trivial _).symm

theorem ev_comp {Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (τ : Y ⟶ Sp R') (y : Y) (φ : R →+* R') (a : R) :
    ev (τ ≫ spMap φ) y a = ev τ y (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [ev, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

structure Probes (Z : Scheme.{0}) where

  I : Type 1

  Y : I → Scheme.{0}

  y : ∀ p, Y p

  β : ∀ p, Y p ⟶ Z

variable {Z : Scheme.{0}} (P : Probes Z)

abbrev Probes.F : Type 1 := ∀ p : P.I, (P.Y p).presheaf.stalk (P.y p)

variable {P} {R R' : Type} [CommRing R] [CommRing R'] {l m n : ℕ}

def Rel (x : Sp R ⟶ Z) (b' : Fin m → P.F) (M : Matrix (Fin m) (Fin n) R) (b : Fin n → P.F) : Prop :=
  ∀ (p : P.I) (τ : P.Y p ⟶ Sp R), τ ≫ x = P.β p → ∀ a, b' a p = ∑ c, ev τ (P.y p) (M a c) * b c p

def Ind (x : Sp R ⟶ Z) (b : Fin n → P.F) : Prop :=
  ∀ c : Fin n → R, (∀ (p : P.I) (τ : P.Y p ⟶ Sp R), τ ≫ x = P.β p → ∑ i, ev τ (P.y p) (c i) * b i p = 0) → c = 0

def Cmp (x : Sp R ⟶ Z) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  Ind x b ∧ Ind x b' ∧ (∃ M, Rel x b' M b) ∧ ∃ M', Rel x b M' b'

variable {x : Sp R ⟶ Z} {b : Fin n → P.F} {b' : Fin m → P.F} {b'' : Fin l → P.F}

theorem Cmp.symm (h : Cmp x b b') : Cmp x b' b := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem Rel.map {M} (h : Rel x b' M b) (φ : R →+* R') : Rel (spMap φ ≫ x) b' (M.map φ) b := fun p τ e a => by
  rw [h p (τ ≫ spMap φ) (by rw [Category.assoc, e]) a]
  simp only [ev_comp, Matrix.map_apply]

theorem Rel.mul {M M'} (h' : Rel x b'' M' b') (h : Rel x b' M b) : Rel x b'' (M' * M) b := fun p τ e a => by
  rw [h' p τ e a]
  simp only [h p τ e, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem Rel.one : Rel x b 1 b := fun p τ _ a => by
  simp [Matrix.one_apply, apply_ite]

theorem Ind.unique (hb : Ind x b) {M M'} (h : Rel x b' M b) (h' : Rel x b' M' b) : M = M' := by
  ext a c
  have := hb (fun c => M a c - M' a c) fun p τ e => by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← h p τ e a, ← h' p τ e a, sub_self]
  exact sub_eq_zero.1 (congrFun this c)

theorem Ind.of_injective (φ : R →+* R') (hφ : Function.Injective φ) (h : Ind (spMap φ ≫ x) b) : Ind x b := by
  intro c hc
  have := h (fun i => φ (c i)) fun p τ e => by
    rw [← hc p (τ ≫ spMap φ) (by rw [Category.assoc, e])]
    simp only [ev_comp]
  exact funext fun i => hφ ((congrFun this i).trans (map_zero φ).symm)

theorem spMap_comp {R'' : Type} [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem Cmp.card_eq [Nontrivial R] (h : Cmp x b b') : n = m := by
  obtain ⟨h₁, h₂, ⟨M, hM⟩, M', hM'⟩ := h
  have e := Matrix.indexEquivOfInv (h₂.unique (hM.mul hM') Rel.one) (h₁.unique (hM'.mul hM) Rel.one)
  simpa using (Fintype.card_congr e).symm

theorem cDvr_powerSeries (K : Type) [Field K] [CharZero K] : GlobalTheory.LN.CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

theorem Cmp.of_powerSeries {K : Type} [Field K] {x : Sp K ⟶ Z} (h : Cmp (spMap (PowerSeries.C (R := K)) ≫ x) b b') :
    Cmp x b b' := by
  have e : spMap (PowerSeries.constantCoeff (R := K)) ≫ spMap (PowerSeries.C (R := K)) ≫ x = x := by
    rw [← Category.assoc, spMap_comp, PowerSeries.constantCoeff_comp_C]
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨h₁, h₂, ⟨M, hM⟩, M', hM'⟩ := h
  exact ⟨h₁.of_injective _ PowerSeries.C_injective, h₂.of_injective _ PowerSeries.C_injective,
    ⟨_, e ▸ hM.map _⟩, ⟨_, e ▸ hM'.map _⟩⟩

def TraitCmp (x : Sp R ⟶ Z) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ →
    Cmp (spMap φ ≫ x) b b'

theorem TraitCmp.symm (h : TraitCmp x b b') : TraitCmp x b' b := fun W _ _ _ hW φ hφ => (h W hW φ hφ).symm

theorem TraitCmp.field [CharZero R] (h : TraitCmp x b b') {K : Type} [Field K] (ψ : R →+* K) (hψ : Function.Injective ψ) :
    Cmp (spMap ψ ≫ x) b b' := by
  have : CharZero K := charZero_of_injective_ringHom hψ
  refine Cmp.of_powerSeries ?_
  rw [← Category.assoc, spMap_comp]
  exact h _ (cDvr_powerSeries K) _ (PowerSeries.C_injective.comp hψ)

theorem mem_of_completion {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {W : Type} [CommRing W] [IsDomain W] (ι : V →+* W) (hι : ∀ v, IsUnit (ι v) → IsUnit v)
    (γ : K →+* FractionRing W) (hγ : ∀ v, γ (algebraMap V K v) = algebraMap W _ (ι v)) (d : K) (w : W)
    (h : γ d = algebraMap W _ w) : ∃ v, algebraMap V K v = d := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger V d with h₁ | ⟨v, hv⟩
  · exact h₁
  have e : ι v * w = 1 := by
    apply IsFractionRing.injective W (FractionRing W)
    rw [map_mul, ← hγ, ← h, ← map_mul, hv, inv_mul_cancel₀ hd, map_one, map_one]
  obtain ⟨u, rfl⟩ := hι v (IsUnit.of_mul_eq_one _ e)
  refine ⟨u⁻¹.val, ?_⟩
  rw [← inv_inv d, ← hv]
  simp

theorem TraitCmp.det_mem [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] {b' : Fin n → P.F}
    (h : TraitCmp x b b') {M} (hM : Rel (spMap (algebraMap R (FractionRing R)) ≫ x) b' M b) :
    ∃ a, algebraMap R (FractionRing R) a = M.det := by
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := R) (K := FractionRing R) M.det).2 fun p _ hp => ?_
  set V := primeLocalSubalgebra (FractionRing R) p
  have : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  let W := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hVW : Function.Injective (algebraMap V W) := algebraMap_adicCompletion_injective_of_dvr V
  have hRV : Function.Injective (algebraMap R V) := fun a c e =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val e)
  let φ : R →+* W := (algebraMap V W).comp (algebraMap R V)
  have hφ : Function.Injective φ := hVW.comp hRV
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W (FractionRing W)).comp hVW
  let γ : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := V) hi
  have hγ : ∀ v : V, γ (algebraMap V _ v) = algebraMap W _ (algebraMap V W v) := fun v =>
    IsFractionRing.lift_algebraMap hi v
  have e : γ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext fun r => hγ (algebraMap R V r)
  obtain ⟨-, -, ⟨N, hN⟩, -⟩ := h W hW φ hφ
  have h₁ := hM.map γ
  have h₂ := hN.map (algebraMap W (FractionRing W))
  rw [← Category.assoc, spMap_comp] at h₁ h₂
  rw [e] at h₁
  have hMN := (h.field _ ((IsFractionRing.injective W (FractionRing W)).comp hφ)).1.unique h₁ h₂
  obtain ⟨v, hv⟩ := mem_of_completion (K := FractionRing R) (algebraMap V W) (fun v hv => by
      by_contra hn
      have : algebraMap V W v ∈ IsLocalRing.maximalIdeal W := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hn
      exact this hv) γ hγ M.det N.det (by
    rw [RingHom.map_det, RingHom.map_det]; exact congrArg Matrix.det hMN)
  rw [← hv]; exact v.2

theorem TraitCmp.exists_unit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] {b' : Fin n → P.F}
    (h : TraitCmp x b b') : ∃ u : Rˣ, ∀ (K : Type) [Field K] (ψ : R →+* K), Function.Injective ψ →
      ∃ M, Rel (spMap ψ ≫ x) b' M b ∧ M.det = ψ u := by
  have hi := IsFractionRing.injective R (FractionRing R)
  obtain ⟨h₁, -, ⟨M, hM⟩, M', hM'⟩ := h.field _ hi
  obtain ⟨a, ha⟩ := h.det_mem hM
  obtain ⟨a', ha'⟩ := h.symm.det_mem hM'
  have e : a' * a = 1 := hi (by
    rw [map_mul, ha, ha', ← Matrix.det_mul, h₁.unique (hM'.mul hM) Rel.one, Matrix.det_one, map_one])
  refine ⟨⟨a, a', (mul_comm _ _).trans e, e⟩, fun K _ ψ hψ => ⟨M.map (IsFractionRing.lift hψ), ?_, ?_⟩⟩
  · have := hM.map (IsFractionRing.lift hψ)
    rwa [← Category.assoc, spMap_comp, show (IsFractionRing.lift hψ).comp (algebraMap R (FractionRing R)) = ψ from
      RingHom.ext (IsFractionRing.lift_algebraMap hψ)] at this
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← ha]
    exact IsFractionRing.lift_algebraMap hψ a

section Base

variable {Z : Scheme.{0}} {P : Probes Z} {n m : ℕ}

def GenPt (η : Z) : Prop := ∀ q : Z, q ⤳ η → q = η

theorem GenPt.mem_genericPoints {η : Z} (h : GenPt η) : η ∈ genericPoints Z := by
  have hC := irreducibleComponent_mem_irreducibleComponents η
  have hg := (isIrreducible_irreducibleComponent (x := η)).isGenericPoint_genericPoint isClosed_irreducibleComponent
  have e := h _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  show closure {η} ∈ irreducibleComponents Z
  rw [hg.def]; exact hC

theorem genPt_iff {R K : Type} [CommRing R] [IsDomain R] [Field K] (x₀ : Sp R ⟶ Z) [IsOpenImmersion x₀] (ψ : R →+* K)
    (pt : Sp K) : GenPt ((spMap ψ ≫ x₀) pt) ↔ Function.Injective ψ := by
  have hk : (spMap ψ pt : PrimeSpectrum R).asIdeal = RingHom.ker ψ := by
    have : (pt : PrimeSpectrum K).asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (α := PrimeSpectrum K) pt ⟨⊥, Ideal.isPrime_bot⟩)
    exact congrArg (Ideal.comap ψ) this
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  rw [RingHom.injective_iff_ker_eq_bot, ← hk, Scheme.Hom.comp_apply]
  constructor
  · intro h
    have s : o ⤳ spMap ψ pt := (PrimeSpectrum.le_iff_specializes (R := R) o (spMap ψ pt)).1 (show (⊥ : Ideal R) ≤ _ from bot_le)
    have := x₀.isOpenEmbedding.injective (h _ (s.map x₀.continuous))
    exact (congrArg PrimeSpectrum.asIdeal this).symm
  · intro h q hq
    obtain ⟨q', rfl⟩ : q ∈ Set.range x₀ := hq.mem_open x₀.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    have s := (PrimeSpectrum.le_iff_specializes (R := R) q' (spMap ψ pt)).2 (x₀.isOpenEmbedding.isInducing.specializes_iff.1 hq)
    refine congrArg _ (PrimeSpectrum.ext (R := R) ?_)
    have s' : (q' : PrimeSpectrum R).asIdeal ≤ (spMap ψ pt : PrimeSpectrum R).asIdeal := s
    rw [h] at s' ⊢
    exact le_bot_iff.1 s'

theorem fromSpec_mem {W : Z.Opens} (hW : IsAffineOpen W) (q) : hW.fromSpec q ∈ W :=
  show hW.fromSpec q ∈ (W : Set Z) from hW.range_fromSpec ▸ ⟨q, rfl⟩

theorem gs_fromSpec {W : Z.Opens} (hW : IsAffineOpen W) {Y : Scheme.{0}} (τ : Y ⟶ Sp Γ(Z, W)) (y : Y) (a : Γ(Z, W)) :
    gs (τ ≫ hW.fromSpec) y W a = ev τ y a := by
  rw [← gs_pull τ hW.fromSpec y W (fromSpec_mem hW _), hW.fromSpec_app_self, ev_eq_gs]
  exact gs_res τ y (U := ⊤) (V := hW.fromSpec ⁻¹ᵁ W) le_top (fromSpec_mem hW _) _

theorem exists_spMap {W : Z.Opens} (hW : IsAffineOpen W) {K : Type} [Field K] (x : Sp K ⟶ Z) (pt : Sp K) (h : x pt ∈ W) :
    ∃ ψ : Γ(Z, W) →+* K, spMap ψ ≫ hW.fromSpec = x := by
  have hr : Set.range x ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q pt]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec x hr)
  exact ⟨φ.hom, (congrArg (· ≫ hW.fromSpec) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem ev_field_injective {K : Type} [Field K] (pt : Sp K) : Function.Injective (ev (𝟙 (Sp K)) pt) := RingHom.injective _

theorem ev_spMap {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) (pt : Sp K) (a : R) :
    ev (spMap ψ) pt a = ev (𝟙 _) pt (ψ a) := by rw [← ev_comp (𝟙 _) pt ψ a, Category.id_comp]

variable [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (z : Z ⟶ Sp ℤ) [Flat z]
include hZ

theorem exists_domain_chart {V : Z.Opens} {p : Z} (hp : p ∈ V) : ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ W ≤ V ∧
    IsDomain Γ(Z, W) ∧ IsIntegrallyClosed Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ ⟨_, hC⟩) (x := p) ⟨hp, mem_irreducibleComponent⟩
  refine ⟨W, hW, hpW, fun q hq => (hle hq).1, GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => (hle hq).2⟩⟩

theorem ext_genPt {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) → gs x pt V a = gs x pt V b) : a = b := by
  refine fn_ext fun p hp => ?_
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hp
  have hi := IsFractionRing.injective Γ(Z, W) (FractionRing Γ(Z, W))
  let pt : Sp (FractionRing Γ(Z, W)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have hm : (spMap (algebraMap Γ(Z, W) (FractionRing Γ(Z, W))) ≫ hW.fromSpec) pt ∈ W := fromSpec_mem hW _
  have v : ∀ c : Γ(Z, V), gs (spMap (algebraMap Γ(Z, W) (FractionRing Γ(Z, W))) ≫ hW.fromSpec) pt V c =
      ev (𝟙 _) pt (algebraMap Γ(Z, W) (FractionRing Γ(Z, W)) ((Z.presheaf.map (homOfLE hle).op).hom c)) := fun c => by
    rw [← gs_res _ pt hle hm, gs_fromSpec, ev_spMap]
  have e := h _ _ pt (hle hm) ((genPt_iff (R := Γ(Z, W)) hW.fromSpec _ pt).2 hi)
  rw [v, v] at e
  rw [← gs_res _ p hle hpW, ← gs_res _ p hle hpW, hi (ev_field_injective pt e)]

theorem unit_ext_genPt {V : Z.Opens} {a b : Γ(Z, V)ˣ}
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) → gm x pt V a = gm x pt V b) : a = b :=
  Units.ext (ext_genPt hZ fun K _ x pt hx hg => by rw [gs_unit _ _ _ hx, gs_unit _ _ _ hx, h K x pt hx hg])

omit hZ [IsLocallyNoetherian Z] in
include z in
theorem charZero_chart {W : Z.Opens} (hW : IsAffineOpen W) [Nontrivial Γ(Z, W)] : CharZero Γ(Z, W) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ z)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  have h₂ : φ.hom = algebraMap ℤ Γ(Z, W) := RingHom.ext_int _ _
  have : Module.Flat ℤ Γ(Z, W) := RingHom.flat_algebraMap_iff.1 (h₂ ▸ h₁)
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Z, W)) (r := (k : ℤ))
    (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h0))).right_eq_zero_of_smul (x := 1) (by simpa using hk)
  exact one_ne_zero this

def GeoCmp (V : Z.Opens) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ χ : Sp W ⟶ Z, (∀ q, χ q ∈ V) →
    (∀ q, GenPt ((Out.jK W ≫ χ) q)) → Cmp χ b b'

omit hZ [IsLocallyNoetherian Z] in
theorem GeoCmp.traitCmp {V W : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') (hW : IsAffineOpen W)
    (hle : W ≤ V) [IsDomain Γ(Z, W)] : TraitCmp (R := Γ(Z, W)) hW.fromSpec b b' := fun T _ _ _ hT φ hφ =>
  h T hT _ (fun _ => hle (fromSpec_mem hW _)) fun q => by
    have := (genPt_iff (R := Γ(Z, W)) hW.fromSpec ((algebraMap T (FractionRing T)).comp φ) q).2
      ((IsFractionRing.injective T _).comp hφ)
    rwa [← spMap_comp, Category.assoc] at this

include z

theorem GeoCmp.field {V : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') {K : Type} [Field K]
    (x : Sp K ⟶ Z) (pt : Sp K) (hx : x pt ∈ V) (hg : GenPt (x pt)) : Cmp x b b' := by
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hx
  have := charZero_chart z hW
  obtain ⟨ψ, rfl⟩ := exists_spMap hW x pt hpW
  exact (h.traitCmp hW hle).field ψ ((genPt_iff (R := Γ(Z, W)) hW.fromSpec ψ pt).1 hg)

theorem GeoCmp.card_eq {V : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') {p : Z} (hp : p ∈ V) :
    n = m := by
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hp
  have := charZero_chart z hW
  exact ((h.traitCmp hW hle).field _ (IsFractionRing.injective Γ(Z, W) (FractionRing Γ(Z, W)))).card_eq

theorem GeoCmp.exists_unit {V : Z.Opens} {b b' : Fin n → P.F} (h : GeoCmp V b b') : ∃ u : Γ(Z, V)ˣ,
    ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) →
      ∃ M, Rel x b' M b ∧ ev (𝟙 _) pt M.det = (gm x pt V u).val := by
  have loc : ∀ p : V, ∃ (W : Z.Opens) (u : Γ(Z, W)ˣ), p.1 ∈ W ∧ W ≤ V ∧
      ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ W → GenPt (x pt) →
        ∃ M, Rel x b' M b ∧ ev (𝟙 _) pt M.det = (gm x pt W u).val := by
    intro p
    obtain ⟨W, hW, hpW, hle, _, _⟩ := exists_domain_chart hZ p.2
    have := charZero_chart z hW
    have : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    obtain ⟨u, hu⟩ := (h.traitCmp hW hle).exists_unit
    refine ⟨W, u, hpW, hle, fun K _ x pt hx hg => ?_⟩
    obtain ⟨ψ, rfl⟩ := exists_spMap hW x pt hx
    obtain ⟨M, hM, hd⟩ := hu K ψ ((genPt_iff (R := Γ(Z, W)) hW.fromSpec ψ pt).1 hg)
    refine ⟨M, hM, ?_⟩
    rw [hd, ← gs_unit _ _ _ hx, gs_fromSpec, ev_spMap]
  choose W u hp hle hu using loc
  obtain ⟨s, hs⟩ := glue_unit V W hle (fun p hp' => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp'⟩, hp _⟩) u
    (fun i j y hy => by
      have e : res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j) :=
        unit_ext_genPt hZ fun K _ x pt hx hg => by
          obtain ⟨M, hM, hd⟩ := hu i K x pt hx.1 hg
          obtain ⟨M', hM', hd'⟩ := hu j K x pt hx.2 hg
          rw [gm_res _ _ _ hx, gm_res _ _ _ hx]
          refine Units.ext ?_
          rw [← hd, ← hd', (h.field hZ z x pt (hle i hx.1) hg).1.unique hM hM']
      exact (gm_res _ y inf_le_left hy _).symm.trans ((congrArg (gm _ y _) e).trans (gm_res _ y inf_le_right hy _)))
  refine ⟨s, fun K _ x pt hx hg => ?_⟩
  obtain ⟨M, hM, hd⟩ := hu ⟨_, hx⟩ K x pt (hp _) hg
  exact ⟨M, hM, by rw [hd, ← hs, gm_res _ _ _ (hp ⟨_, hx⟩)]⟩

omit [IsLocallyNoetherian Z] hZ z [Flat z] in
theorem det_square {K : Type} [Field K] {x : Sp K ⟶ Z} (pt : Sp K) {b₁ b₁' b₂ b₂' : Fin n → P.F} {N N' M₁ M₂}
    (hN : Rel x b₂ N b₁) (hN' : Rel x b₂' N' b₁') (h₁ : Rel x b₁ M₁ b₁') (h₂ : Rel x b₂ M₂ b₂') (hi : Ind x b₁')
    {u u' m₁ m₂ : ((Sp K).presheaf.stalk pt)ˣ} (e : ev (𝟙 _) pt N.det = u.val) (e' : ev (𝟙 _) pt N'.det = u'.val)
    (e₁ : ev (𝟙 _) pt M₁.det = m₁.val) (e₂ : ev (𝟙 _) pt M₂.det = m₂.val) : u = m₂ * m₁⁻¹ * u' := by
  have h := congrArg (fun M => ev (𝟙 _) pt (Matrix.det M)) (hi.unique (hN.mul h₁) (h₂.mul hN'))
  simp only [Matrix.det_mul, map_mul, e, e', e₁, e₂, ← Units.val_mul, Units.val_inj] at h
  rw [mul_right_comm, ← h, mul_inv_cancel_right]

def Tr {Z₁ : Scheme.{0}} (A : LB Z₁) (f : Z ⟶ Z₁) (r s : ℤ) (θ : A.ι → Fin 1 → P.F) (v : A.ι → Fin n → P.F) : Prop :=
  ∀ (i j : A.ι) (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), f (x pt) ∈ A.U i → f (x pt) ∈ A.U j →
    ∃ (C : Matrix (Fin 1) (Fin 1) K) (M : Matrix (Fin n) (Fin n) K) (c d : ((Sp K).presheaf.stalk pt)ˣ),
      Rel x (θ i) C (θ j) ∧ Rel x (v i) M (v j) ∧
      ev (𝟙 _) pt C.det = c.val ∧ ev (𝟙 _) pt M.det = d.val ∧ gm (x ≫ f) pt _ (A.g i j) = c ^ r * d ^ s

theorem lbIso_of_cmp {Z₁ Z₂ : Scheme.{0}} {A₁ : LB Z₁} {A₂ : LB Z₂} (h₁ : A₁.IsLB) (h₂ : A₂.IsLB) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂)
    (r s : ℤ) (θ₁ : A₁.ι → Fin 1 → P.F) (v₁ : A₁.ι → Fin n → P.F) (θ₂ : A₂.ι → Fin 1 → P.F) (v₂ : A₂.ι → Fin m → P.F)
    (hc : ∀ i j (V : Z.Opens), (∀ q ∈ V, f₁ q ∈ A₁.U i) → (∀ q ∈ V, f₂ q ∈ A₂.U j) →
      GeoCmp V (θ₁ i) (θ₂ j) ∧ GeoCmp V (v₁ i) (v₂ j))
    (t₁ : Tr A₁ f₁ r s θ₁ v₁) (t₂ : Tr A₂ f₂ r s θ₂ v₂) : LBIso (A₁.pull f₁) (A₂.pull f₂) := by
  rcases isEmpty_or_nonempty Z with hE | ⟨⟨p₀⟩⟩
  · exact ⟨⟨fun _ => 1⟩, fun i j => unit_ext fun x _ => isEmptyElim x⟩
  obtain rfl : n = m := by
    obtain ⟨i, hi⟩ := exists_chart h₁ (f₁ p₀)
    obtain ⟨j, hj⟩ := exists_chart h₂ (f₂ p₀)
    exact (hc i j (f₁ ⁻¹ᵁ A₁.U i ⊓ f₂ ⁻¹ᵁ A₂.U j) (fun _ h => h.1) (fun _ h => h.2)).2.card_eq hZ z (p := p₀) ⟨hi, hj⟩
  have hc' := fun p : (PUnit → A₂.ι) × (PUnit → A₁.ι) => hc (p.2 PUnit.unit) (p.1 PUnit.unit)
    ((A₂.pull f₂).U p.1 ⊓ (A₁.pull f₁).U p.2) (fun _ h => mem_pull.1 h.2) (fun _ h => mem_pull.1 h.1)
  choose u hu using fun p => (hc' p).1.exists_unit hZ z
  choose d hd using fun p => (hc' p).2.exists_unit hZ z
  refine ⟨⟨fun p => u p ^ r * d p ^ s⟩, fun p q => unit_ext_genPt hZ fun K _ x pt hx hg => ?_⟩
  obtain ⟨C, hC, eC⟩ := hu p K x pt hx.1 hg
  obtain ⟨C', hC', eC'⟩ := hu q K x pt hx.2 hg
  obtain ⟨M, hM, eM⟩ := hd p K x pt hx.1 hg
  obtain ⟨M', hM', eM'⟩ := hd q K x pt hx.2 hg
  obtain ⟨C₁, M₁, c₁, d₁, a₁, a₂, a₃, a₄, a₅⟩ := t₁ _ _ K x pt (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)
  obtain ⟨C₂, M₂, c₂, d₂, b₁, b₂, b₃, b₄, b₅⟩ := t₂ _ _ K x pt (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1)
  have e₁ := det_square pt hC hC' a₁ b₁ ((hc' q).1.field hZ z x pt hx.2 hg).1 eC eC' a₃ b₃
  have e₂ := det_square pt hM hM' a₂ b₂ ((hc' q).2.field hZ z x pt hx.2 hg).1 eM eM' a₄ b₄
  refine (gm_res x pt _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div (A₁.pull f₁) (A₂.pull f₂) x pt p q hx).trans (congrArg₂ (fun a b => a * b⁻¹)
      ((gm_pull_g A₂ f₂ x pt _ _ hx.1.1 hx.2.1).trans b₅) ((gm_pull_g A₁ f₁ x pt _ _ hx.1.2 hx.2.2).trans a₅)))
    (gm_res x pt _ hx _))).symm)
  have v : ∀ p : (PUnit → A₂.ι) × (PUnit → A₁.ι), gm x pt ((A₂.pull f₂).U p.1 ⊓ (A₁.pull f₁).U p.2) (u p ^ r * d p ^ s) =
      gm x pt _ (u p) ^ r * gm x pt _ (d p) ^ s := fun p => by rw [map_mul, map_zpow, map_zpow]
  refine (v p).trans (Eq.trans ?_ (congrArg _ (v q)).symm)
  rw [e₁, e₂]
  simp only [mul_zpow, mul_inv, inv_zpow]
  ac_rfl

end Base

section Values

open MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LN TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_up_sec {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {φ : K → (Y ⟶ X)}
    (e : ∀ k, φ' k ≫ F = φ k) {ε : K → ℤ} (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L φ p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L φ p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain rfl : (fun k => φ' k ≫ F) = φ := funext e
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ s = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ LB.wchart L' φ' q)).op).hom (a.f q),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz))) (gs_res r z _ hz _))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => φ' k ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ ε (𝟙 Y) y hy.1.1, sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, one_mul, ← mul_assoc, ← Units.val_mul,
          mul_right_comm, inv_mul_cancel, one_mul])
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W q)) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, mul_one, Units.val_mul, mul_assoc]
  rfl

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) q (r z) U h, Category.id_comp]

def cv {T : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ T) : Γ(T, ⊤) →+* R :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_cv {T Y : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ T) (τ : Y ⟶ Sp R) (y : Y) (a : Γ(T, ⊤)) :
    ev τ y (cv x a) = gs (τ ≫ x) y ⊤ a := by
  rw [ev_eq_gs, ← gs_pull τ x y ⊤ trivial]
  exact congrArg (gs τ y ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _)

variable {Z Z₁ : Scheme.{0}}

structure Pt (G : Over Z) (L : LB G.left) where

  Y : Scheme.{0}

  g : Y ⟶ G.left

  y : Y

  k : L.ι

  hk : g y ∈ L.U k

abbrev probes (G : Over Z) (L : LB G.left) : Probes Z := ⟨Pt G L, Pt.Y, Pt.y, fun p => p.g ≫ G.hom⟩

def sg {G : Over Z} {L : LB G.left} {N : ℕ} {T : Over Z} (s : LB.Sec (LPow G L (N : ℤ) T)) {Y : Scheme.{0}}
    (r : Y ⟶ (T ⊗ G).left) (y : Y) (j : L.ι) : Y.presheaf.stalk y :=
  gs r y (LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => j)) (s.f (fun _ => j))

theorem exists_lift (G T : Over Z) {Y : Scheme.{0}} (a : Y ⟶ T.left) (c : Y ⟶ G.left) (h : a ≫ T.hom = c ≫ G.hom) :
    ∃ r : Y ⟶ (T ⊗ G).left, r ≫ (fst T G).left = a ∧ r ≫ (snd T G).left = c :=
  ⟨pullback.lift a c h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem whisker_snd' (G : Over Z) {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem lin_univ {G : Over Z} {L : LB G.left} (hL : L.IsLB) {N n : ℕ} {T T' : Over Z} {h : T' ⟶ T}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c s} (H : Lin G L N h b c s) {Y : Scheme.{0}} (r : Y ⟶ (T' ⊗ G).left) (y : Y)
    (j : L.ι) (hj : (snd T' G).left (r y) ∈ L.U j) :
    sg s r y j = ∑ i, gs (r ≫ (fst T' G).left) y ⊤ (c i) * sg (b i) (r ≫ (h ▷ G).left) y j := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL (r y) (fun _ : PUnit => (snd T' G).left) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have e₁ := H (r y) J hJ
  have m : (h ▷ G).left (r y) ∈ LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q (r y) ∈ L.U j) (whisker_snd' G h)).mpr hj
  have m' : r y ∈ LB.wchart L (fun _ : Fin 1 => (snd T' G).left) (fun _ => j) := Set.mem_iInter.2 fun _ => hj
  have e₂ := (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s (𝟙 _) (r y) J (fun _ => j)
    (fun _ => by rw [Category.id_comp]; exact e PUnit.unit)).symm.trans (e₁.trans (Finset.sum_congr rfl fun i _ =>
      congrArg _ (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left (r y) J
        (fun _ => j) (fun _ => by rw [whisker_snd']; exact e PUnit.unit))))
  refine (gs_stalkMap r y _ m' _).trans ((congrArg (r.stalkMap y).hom e₂).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gs_comp r _ y ⊤ trivial _).symm
      (gs_comp r _ y _ m _).symm))))

def Comes {G : Over Z} {L : LB G.left} (N : ℕ) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) (v : (probes G L).F) : Prop :=
  ∀ (Y' : Scheme.{0}) (ψ : Y' ⟶ G.left) (σ : Y' ⟶ Sp W), σ ≫ χ = ψ ≫ G.hom →
    ∃ a : LB.Sec (LB.LinComb L (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ))), ∀ (p : Pt G L) (r : p.Y ⟶ Y'), r ≫ ψ = p.g →
      gs r p.y (LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => p.k)) (a.f (fun _ => p.k)) = v p

def Bas {G : Over Z} {L : LB G.left} (N : ℕ) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) {n : ℕ} (v : Fin n → (probes G L).F) :
    Prop :=
  Ind χ v ∧ (∀ i, Comes N χ (v i)) ∧ ∀ v', Comes N χ v' → ∃ c : Fin n → W, ∀ (p : Pt G L) (τ : p.Y ⟶ Sp W),
    τ ≫ χ = p.g ≫ G.hom → v' p = ∑ i, ev τ p.y (c i) * v i p

theorem Bas.cmp {G : Over Z} {L : LB G.left} {N : ℕ} {W : Type} [CommRing W] {χ : Sp W ⟶ Z} {n m : ℕ}
    {v : Fin n → (probes G L).F} {v' : Fin m → (probes G L).F} (h : Bas N χ v) (h' : Bas N χ v') : Cmp χ v v' := by
  choose M hM using fun i => h.2.2 _ (h'.2.1 i)
  choose M' hM' using fun i => h'.2.2 _ (h.2.1 i)
  exact ⟨h.1, h'.1, ⟨Matrix.of M, fun p τ e a => hM a p τ e⟩, ⟨Matrix.of M', fun p τ e a => hM' a p τ e⟩⟩

variable {G : Over Z} {G₁ : Over Z₁} {L : LB G.left} {L₁ : LB G₁.left} {f : Z ⟶ Z₁} {φ : G.left ⟶ G₁.left}
  (w : LB.Iso L (L₁.pull φ)) {N n : ℕ}

def IsVal {T : Over Z₁} (s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)) (v : (probes G L).F) : Prop :=
  ∀ (p : Pt G L) (r : p.Y ⟶ (T ⊗ G₁).left) (j : L₁.ι), r ≫ (snd T G₁).left = p.g ≫ φ → φ (p.g p.y) ∈ L₁.U j →
    sg s r p.y j = (gw w p.g p.y j p.k ^ (N : ℤ)).val * v p

variable {w} (hφ : IsPullback φ G.hom G₁.hom f) (hw : PGen w) (hL : L.IsLB) (hL₁ : L₁.IsLB)

include hw hL hL₁ in
theorem exists_isVal {T : Over Z₁} [Mono T.hom] (s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)) : ∃ v, IsVal w s v := by
  classical
  have : Mono (snd T G₁).left := inferInstanceAs (Mono (pullback.snd T.hom G₁.hom))
  choose j₀ hj₀ using fun p : Pt G L => exists_chart hL₁ (φ (p.g p.y))
  have ex : ∀ p : Pt G L, ∃ a : p.Y.presheaf.stalk p.y, ∀ r : p.Y ⟶ (T ⊗ G₁).left, r ≫ (snd T G₁).left = p.g ≫ φ →
      a = (gw w p.g p.y (j₀ p) p.k ^ (N : ℤ))⁻¹.val * sg s r p.y (j₀ p) := fun p => by
    by_cases h : ∃ r : p.Y ⟶ (T ⊗ G₁).left, r ≫ (snd T G₁).left = p.g ≫ φ
    · obtain ⟨r₀, h₀⟩ := h
      exact ⟨(gw w p.g p.y (j₀ p) p.k ^ (N : ℤ))⁻¹.val * sg s r₀ p.y (j₀ p), fun r hr => by
        rw [(cancel_mono _).1 (hr.trans h₀.symm)]⟩
    · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ h⟩
  choose v hv using ex
  refine ⟨v, fun p r j hr hj => ?_⟩
  have m : ∀ i, φ (p.g p.y) ∈ L₁.U i → r p.y ∈ LB.wchart L₁ (fun _ : Fin 1 => (snd T G₁).left) (fun _ => i) := fun i hi =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L₁.U i) hr).mpr hi
  have t := sec_trans (L := L₁) (φ := fun _ : Fin 1 => (snd T G₁).left) (ε := fun _ => (N : ℤ)) s r p.y (m j hj) (m _ (hj₀ p))
  have g := hw _ p.g p.y j (j₀ p) p.k p.k hj (hj₀ p) p.hk p.hk
  rw [gm_self hL p.g p.y p.hk, inv_one, mul_one] at g
  refine t.trans ?_
  rw [hv p r hr, g, Geo.Tor.trF, Fin.prod_univ_one, hr, mul_zpow, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
  rfl

include hφ hL₁ in
theorem rel_of_lin {T₁ T₂ T' : Over Z₁} {h₁ : T' ⟶ T₁} {h₂ : T' ⟶ T₂} {m : ℕ}
    {b₁ : Fin m → LB.Sec (LPow G₁ L₁ (N : ℤ) T₁)} {b₂ : Fin n → LB.Sec (LPow G₁ L₁ (N : ℤ) T₂)}
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤))
    (H : ∀ k, ∃ t, Lin G₁ L₁ N h₁ (fun _ : Fin 1 => b₁ k) (fun _ => 1) t ∧ Lin G₁ L₁ N h₂ b₂ (fun k' => M k k') t)
    {v₁ : Fin m → (probes G L).F} {v₂ : Fin n → (probes G L).F} (hv₁ : ∀ k, IsVal w (b₁ k) (v₁ k))
    (hv₂ : ∀ k, IsVal w (b₂ k) (v₂ k)) {R : Type} [CommRing R] (x : Sp R ⟶ Z) (x' : Sp R ⟶ T'.left)
    (hx : x' ≫ T'.hom = x ≫ f) : Rel x v₁ (M.map (cv x')) v₂ := by
  intro (p : Pt G L) (τ : p.Y ⟶ Sp R) (e : τ ≫ x = p.g ≫ G.hom) k
  obtain ⟨r, r₁, r₂⟩ := exists_lift G₁ T' (τ ≫ x') (p.g ≫ φ) (by
    rw [Category.assoc, hx, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
  obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
  have hj' : (snd T' G₁).left (r p.y) ∈ L₁.U j := (congrArg (fun q => q p.y ∈ L₁.U j) r₂).mpr hj
  obtain ⟨t, t₁, t₂⟩ := H k
  have E := (lin_univ hL₁ t₁ r p.y j hj').symm.trans (lin_univ hL₁ t₂ r p.y j hj')
  rw [Fin.sum_univ_one, gs_eq _ _ ⊤ trivial, map_one, map_one, one_mul,
    hv₁ k p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj] at E
  refine (Units.mul_right_inj (gw w p.g p.y j p.k ^ (N : ℤ))).1 (E.trans ((Finset.sum_congr rfl fun i _ => ?_).trans
    (Finset.mul_sum _ _ _).symm))
  rw [hv₂ i p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj, r₁, ← ev_cv, mul_left_comm]
  rfl

include hφ hw hL hL₁ in
theorem comes_of_isVal {T : Over Z₁} {s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)} {v : (probes G L).F} (hv : IsVal w s v)
    {W : Type} [CommRing W] (χ : Sp W ⟶ Z) (χ₁ : Sp W ⟶ T.left) (hχ : χ₁ ≫ T.hom = χ ≫ f) : Comes N χ v := by
  intro Y' ψ σ e
  obtain ⟨h, -, h₂⟩ := exists_lift G₁ T (σ ≫ χ₁) (ψ ≫ φ) (by
    rw [Category.assoc, hχ, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
  obtain ⟨a, ha⟩ := GlobalTheory.SecPull.exists_down_sec hw hL₁ hL (fun _ : Fin 1 => ψ) (fun _ => (snd T G₁).left)
    (fun _ => (N : ℤ)) h (fun _ => h₂.symm) s
  refine ⟨a, fun p r hr => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
  have e₁ := hv p (r ≫ h) j (by rw [Category.assoc, h₂, ← Category.assoc, hr]) hj
  rw [ha _ r p.y (fun _ => j) (fun _ => p.k)
    (Set.mem_iInter.2 fun _ => (congrArg (fun q => φ (q p.y) ∈ L₁.U j) hr).mpr hj)
    (Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L.U p.k) hr).mpr p.hk), pw, Fin.prod_univ_one, hr]
  exact (congrArg _ e₁).trans (Units.inv_mul_cancel_left _ _)

include hφ hw hL hL₁ in
theorem bas_of_basisAlong {T : Over Z₁} {b : Fin n → LB.Sec (LPow G₁ L₁ (N : ℤ) T)} {v : Fin n → (probes G L).F}
    (hv : ∀ i, IsVal w (b i) (v i)) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) {χ' : Sp W ⟶ Z₁} (hχ : χ' = χ ≫ f)
    (h : Over.mk χ' ⟶ T) (hb : BasisAlong G₁ L₁ N h b) : Bas N χ v := by
  have hs : (snd (Over.mk χ') G₁).left ≫ G₁.hom = ((fst (Over.mk χ') G₁).left ≫ χ) ≫ f := by
    rw [Category.assoc, ← hχ]; exact Frames.snd_hom G₁ (Over.mk χ')
  obtain ⟨ψ, ψ₁, ψ₂⟩ : ∃ ψ : (Over.mk χ' ⊗ G₁).left ⟶ G.left, ψ ≫ φ = (snd (Over.mk χ') G₁).left ∧
      ψ ≫ G.hom = (fst (Over.mk χ') G₁).left ≫ χ := ⟨hφ.lift _ _ hs, hφ.lift_fst _ _ _, hφ.lift_snd _ _ _⟩
  refine ⟨fun c hc => ?_, fun i => comes_of_isVal hφ hw hL hL₁ (hv i) χ h.left ((Over.w h).trans hχ), fun v' hv' => ?_⟩
  · let o : LB.Sec (LPow G₁ L₁ (N : ℤ) (Over.mk χ')) := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩
    have ho : ∀ z J, Good L₁ z J → sval (L := L₁) (φ := fun _ : Fin 1 => (snd (Over.mk χ') G₁).left)
        (ε := fun _ => (N : ℤ)) o (𝟙 _) z J = 0 := fun z J hJ =>
      (gs_eq _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk χ') G₁).left) (𝟙 _)) _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))
    have H₀ : Lin G₁ L₁ N h b 0 o := fun z J hJ => (ho z J hJ).trans (Finset.sum_eq_zero fun i _ => by
      rw [Pi.zero_apply, gs_eq _ _ ⊤ trivial, map_zero, map_zero, zero_mul]).symm
    have H₁ : Lin G₁ L₁ N h b (fun i => (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom (c i)) o := fun z J hJ => by
      obtain ⟨k, hk⟩ := exists_chart hL (ψ z)
      have e : (h ▷ G₁).left ≫ (snd T G₁).left = ψ ≫ φ := (whisker_snd' G₁ h).trans ψ₁.symm
      have hj : φ (ψ z) ∈ L₁.U (J ((h ▷ G₁).left ≫ (snd T G₁).left)) :=
        (congrArg (fun q => q z ∈ L₁.U (J ((h ▷ G₁).left ≫ (snd T G₁).left))) e).mp (hJ _)
      have E := congrArg ((gw w ψ z (J ((h ▷ G₁).left ≫ (snd T G₁).left)) k ^ (N : ℤ)).val * ·)
        (hc (⟨_, ψ, z, k, hk⟩ : Pt G L) (fst (Over.mk χ') G₁).left ψ₂.symm)
      refine (ho z J hJ).trans ((mul_zero _).symm.trans (E.symm.trans ((Finset.mul_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) (ev_eq_gs _ _ _)
          (hv i (⟨_, ψ, z, k, hk⟩ : Pt G L) (h ▷ G₁).left _ e hj).symm)))))
    have E := (hb o).unique H₁ H₀
    exact funext fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
      ((congrFun E i).trans (map_zero _).symm)
  · obtain ⟨a, ha⟩ := hv' _ ψ (fst (Over.mk χ') G₁).left ψ₂.symm
    obtain ⟨t, ht⟩ := exists_up_sec hw hL₁ hL (φ := fun _ : Fin 1 => (snd (Over.mk χ') G₁).left) (fun _ => ψ₁) a
    obtain ⟨c, hc, -⟩ := hb t
    refine ⟨fun i => cv (R := W) (𝟙 (Sp W)) (c i), fun p τ e => ?_⟩
    obtain ⟨r, r₁, r₂⟩ := exists_lift G₁ (Over.mk χ') τ (p.g ≫ φ) (by
      show τ ≫ χ' = _
      rw [hχ, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
    have hr : r ≫ ψ = p.g := hφ.hom_ext (by rw [Category.assoc, ψ₁, r₂])
      (by rw [Category.assoc, ψ₂, ← Category.assoc, r₁, e])
    obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
    have hj' : (snd (Over.mk χ') G₁).left (r p.y) ∈ L₁.U j := (congrArg (fun q => q p.y ∈ L₁.U j) r₂).mpr hj
    have E := ht _ r p.y (fun _ => j) (fun _ => p.k) (Set.mem_iInter.2 fun _ => hj')
      (Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L.U p.k) hr).mpr p.hk)
    rw [ha p r hr, pw, Fin.prod_univ_one, hr] at E
    refine (Units.mul_right_inj (gw w p.g p.y j p.k ^ (N : ℤ))).1 (E.symm.trans ((lin_univ hL₁ hc r p.y j hj').trans
      ((Finset.sum_congr rfl fun i _ => ?_).trans (Finset.mul_sum _ _ _).symm)))
    rw [hv i p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj, r₁, ev_cv, Category.comp_id, mul_left_comm]

theorem exists_lift_open {Y X : Scheme.{0}} (x : Y ⟶ X) (U : X.Opens) (h : ∀ q, x q ∈ U) : ∃ x' : Y ⟶ U.toScheme, x' ≫ U.ι = x :=
  ⟨IsOpenImmersion.lift U.ι x (by rintro _ ⟨q, rfl⟩; exact ⟨⟨_, h q⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

theorem gs_topIso {Y X : Scheme.{0}} (U : X.Opens) (x : Y ⟶ U.toScheme) (y : Y) (a : Γ(X, U)) :
    gs x y ⊤ (U.topIso.inv.hom a) = gs (x ≫ U.ι) y U a := by
  have hm : ∀ t : U.toScheme, U.ι t ∈ U := fun t => t.2
  rw [← gs_pull x U.ι y U (hm _)]
  refine Eq.trans ?_ (gs_res x y (show ⊤ ≤ U.ι ⁻¹ᵁ U from fun t _ => hm t) trivial _)
  refine congrArg (gs _ y ⊤) ?_
  have e : U.topIso.inv = U.ι.appLE U ⊤ (fun t _ => hm t) := (Scheme.Opens.ι_appLE U U ⊤ (fun t _ => hm t)).symm
  rw [e]; rfl

include hφ hw hL hL₁ in
theorem exists_values (A : AmpFrames G₁ L₁ N) (hab : ∀ η : Z, GenPt η → f η ∈ abLocus G₁) :
    ∃ (θ : A.A.ι → Fin 1 → (probes G L).F) (v : A.A.ι → Fin A.n → (probes G L).F),
      (∀ (i : A.A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ Z,
        (∀ q, f (χ q) ∈ A.A.U i) → (∀ q, GenPt ((jK W ≫ χ) q)) → Bas 1 χ (θ i) ∧ Bas N χ (v i)) ∧
      Tr A.A f A.r A.s θ v := by
  have mo : ∀ i, Mono (Over.mk (A.A.U i).ι).hom := fun i => inferInstanceAs (Mono (A.A.U i).ι)
  choose θ hθ using fun i => exists_isVal hw hL hL₁ (A.th i)
  choose v hv using fun i k => exists_isVal hw hL hL₁ (A.b i k)
  refine ⟨fun i _ => θ i, v, fun i W _ _ _ hW χ hχ hg => ?_, fun i j K _ x pt hi hj => ?_⟩
  · obtain ⟨χ₁, e⟩ := exists_lift_open (χ ≫ f) (A.A.U i) hχ
    obtain ⟨t₁, t₂⟩ := A.trait i W hW χ₁ (by
      rw [e]
      rintro _ ⟨q, rfl⟩
      exact hab _ (hg q))
    exact ⟨bas_of_basisAlong hφ hw hL hL₁ (fun _ => hθ i) χ e _ t₁, bas_of_basisAlong hφ hw hL hL₁ (hv i) χ e _ t₂⟩
  · obtain ⟨x', e⟩ := exists_lift_open (x ≫ f) (A.A.U i ⊓ A.A.U j) fun q => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) q pt]; exact ⟨hi, hj⟩
    obtain ⟨c, M, t₁, t₂, t₃⟩ := A.trans i j
    let ρ : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤) →+* (Sp K).presheaf.stalk pt := (ev (𝟙 (Sp K)) pt).comp (cv x')
    have R₁ := rel_of_lin (T' := Over.mk (A.A.U i ⊓ A.A.U j).ι) hφ hL₁ (b₁ := fun _ : Fin 1 => A.th i)
      (b₂ := fun _ : Fin 1 => A.th j) (Matrix.of fun _ _ => c.val) (fun _ => t₁) (fun _ => hθ i) (fun _ => hθ j) x x' e
    have R₂ := rel_of_lin (T' := Over.mk (A.A.U i ⊓ A.A.U j).ι) hφ hL₁ M.val t₂ (hv i) (hv j) x x' e
    refine ⟨_, _, Units.map ρ.toMonoidHom c, Units.map ρ.toMonoidHom (Matrix.GeneralLinearGroup.det M), R₁, R₂,
      congrArg (ev (𝟙 (Sp K)) pt) (Matrix.det_fin_one _), congrArg (ev (𝟙 (Sp K)) pt) ((cv x').map_det M.val).symm,
      Units.ext ?_⟩
    rw [← map_zpow, ← map_zpow, ← map_mul, ← gs_unit (x ≫ f) pt (A.A.U i ⊓ A.A.U j) ⟨hi, hj⟩, ← e, ← gs_topIso, t₃]
    exact ((ev_cv x' (𝟙 _) pt _).trans (by rw [Category.id_comp])).symm

end Values

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField

theorem lbIso_of_ampFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), Geo.Tor.IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  intro E _ _ _ H Z Z₁ Z₂ _ z t t₁ t₂ f₁ f₂ m₁ m₂ N A₁ A₂ hZ hz hab hr hs
  obtain ⟨w₁, hw₁, -⟩ := (isPullCubical_iff m₁.cm t₁.cub t.cub).1 m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := (isPullCubical_iff m₂.cm t₂.cub t.cub).1 m₂.lin
  obtain ⟨θ₁, v₁, b₁, r₁⟩ := exists_values m₁.cart.1 hw₁ t.PP.isLB t₁.PP.isLB A₁ fun q hq =>
    (abLocus_pullback abLocusOne t₁.semi m₁.cart.1 q).2 (hab hq.mem_genericPoints)
  obtain ⟨θ₂, v₂, b₂, r₂⟩ := exists_values m₂.cart.1 hw₂ t.PP.isLB t₂.PP.isLB A₂ fun q hq =>
    (abLocus_pullback abLocusOne t₂.semi m₂.cart.1 q).2 (hab hq.mem_genericPoints)
  rw [← hr, ← hs] at r₂
  refine lbIso_of_cmp hZ z A₁.isLB A₂.isLB f₁ f₂ A₁.r A₁.s θ₁ v₁ θ₂ v₂ (fun i j V h₁ h₂ => ?_) r₁ r₂
  exact ⟨fun W _ _ _ hW χ hχ hg => (b₁ i W hW χ (fun q => h₁ _ (hχ q)) hg).1.cmp (b₂ j W hW χ (fun q => h₂ _ (hχ q)) hg).1,
    fun W _ _ _ hW χ hχ hg => (b₁ i W hW χ (fun q => h₁ _ (hχ q)) hg).2.cmp (b₂ j W hW χ (fun q => h₂ _ (hχ q)) hg).2⟩

end Main

end GlobalTheory.FrameCmp
