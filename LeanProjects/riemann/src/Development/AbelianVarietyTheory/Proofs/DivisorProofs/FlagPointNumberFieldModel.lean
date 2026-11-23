import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem subsingleton_primeSpectrum {R : Type} [CommRing R] (h : ∀ x : R, IsUnit x ∨ IsNilpotent x) :
    Subsingleton (PrimeSpectrum R) := by
  constructor
  intro P Q
  ext x
  rcases h x with hx | ⟨n, hn⟩
  · exact ⟨fun hm => absurd (Ideal.eq_top_of_isUnit_mem _ hm hx) P.2.ne_top,
      fun hm => absurd (Ideal.eq_top_of_isUnit_mem _ hm hx) Q.2.ne_top⟩
  · have hP : x ∈ P.asIdeal := P.2.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
    have hQ : x ∈ Q.asIdeal := Q.2.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
    exact ⟨fun _ => hQ, fun _ => hP⟩

theorem exists_finset_factor {X : Scheme.{0}} (h : X ⟶ Sp ℤ) [LocallyOfFiniteType h]
    {R : Type} [CommRing R] [Nontrivial R] [Subsingleton (PrimeSpectrum R)] (x : Sp R ⟶ X) :
    ∃ s : Finset R, ∀ (T : Type) [CommRing T] (β : T →+* R), Function.Injective β →
      (↑s : Set R) ⊆ Set.range β → ∃ x' : Sp T ⟶ X, spMap β ≫ x' = x := by
  classical
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  let p : Sp R := (show PrimeSpectrum R from ⟨M, hM.isPrime⟩)
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x p) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range U.ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : q = p := Subsingleton.elim (α := PrimeSpectrum R) q p
    rw [this]; exact hpU
  let xU : Sp R ⟶ U.toScheme := IsOpenImmersion.lift U.ι x hr
  have hxU : xU ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, U) ⟶ CommRingCat.of R := Spec.preimage (xU ≫ hU.isoSpec.hom)
  have hφ : Spec.map φ = xU ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hft : (CommRingCat.Hom.hom (h.appLE ⊤ U (by simp))).FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) h inferInstance
      ⟨⊤, isAffineOpen_top (Sp ℤ)⟩ ⟨U, hU⟩ (by simp)
  have hft' : (Int.castRingHom Γ(X, U)).FiniteType := by
    have h2 := hft.comp (RingHom.FiniteType.of_surjective
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)
      (fun a => ⟨(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom) a, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl⟩))
    have e : (CommRingCat.Hom.hom (h.appLE ⊤ U (by simp))).comp
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv) = Int.castRingHom Γ(X, U) :=
      RingHom.ext_int _ _
    rwa [e] at h2
  letI : Algebra ℤ Γ(X, U) := (Int.castRingHom Γ(X, U)).toAlgebra
  obtain ⟨t, ht⟩ := hft'.out
  refine ⟨t.image φ.hom, ?_⟩
  intro T _ β hβ hs
  have hR : ∀ b : Γ(X, U), ∃ c, β c = φ.hom b := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (t : Set Γ(X, U)) := by rw [ht]; trivial
    change φ.hom b ∈ β.range
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact hs (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
    | algebraMap r => exact ⟨r, by rw [map_intCast, eq_intCast (algebraMap ℤ Γ(X, U)), map_intCast]⟩
    | add b b' _ _ hb hb' => rw [map_add]; exact add_mem hb hb'
    | mul b b' _ _ hb hb' => rw [map_mul]; exact mul_mem hb hb'
  choose ψ₀ hψ₀ using hR
  let ψ : Γ(X, U) →+* T :=
    { toFun := ψ₀
      map_one' := hβ (by simp [hψ₀])
      map_mul' := fun a b => hβ (by simp [hψ₀])
      map_zero' := hβ (by simp [hψ₀])
      map_add' := fun a b => hβ (by simp [hψ₀]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β = φ := by
    ext b; exact hψ₀ b
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hxU]

end GlobalTheory.FlagDescent

namespace GlobalTheory.FlagDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal CategoryTheory.Limits

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_cancel {A Q B : Type} [CommRing A] [CommRing Q] [CommRing B] (ι : A →+* Q)
    (hι : Function.Injective ι) (f g : Sp A ⟶ Sp B) (h : spMap ι ≫ f = spMap ι ≫ g) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g] at h ⊢
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext b
  apply hι
  have := congrArg (fun φ => CommRingCat.Hom.hom φ b) h'
  simpa using this

theorem exists_numberField : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (y : GlobalTheory.ShFam.Pad.FlagPt Z Qb), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ι : K →+* Qb) (jF : c.F →+* K) (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z) (uK : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ Z.t.G.left)), ι.comp jF = y.fK ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ yK = y.y ∧ yK ≫ GlobalTheory.Toroidal.genStr Z = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jF ∧ ∀ τ i, y.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK τ i := by
  intro E _ _ _ H Dw l Xo c Z y
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := isProper_toroidalModel_structureMap Z
  haveI : LocallyOfFiniteType (spMap (Int.castRingHom (𝓞 c.F))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change (Int.castRingHom (𝓞 c.F)).FiniteType
    have e : Int.castRingHom (𝓞 c.F) = algebraMap ℤ (𝓞 c.F) := RingHom.ext_int _ _
    rw [e]
    exact (RingHom.finite_algebraMap.2 inferInstance).to_finiteType
  haveI : LocallyOfFiniteType Z.t.G.hom := by haveI := Z.t.semi.smooth; infer_instance
  haveI : Subsingleton (PrimeSpectrum (DualNumber Qb)) := subsingleton_primeSpectrum fun x => by
    by_cases hx : TrivSqZeroExt.fst x = 0
    · right
      refine ⟨2, ?_⟩
      ext <;> simp [pow_two, hx]
    · left
      exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hx)
  haveI : Subsingleton (PrimeSpectrum Qb) := subsingleton_primeSpectrum fun x => by
    by_cases hx : x = 0
    · right; exact ⟨1, by simp [hx]⟩
    · left; exact isUnit_iff_ne_zero.2 hx
  obtain ⟨s₀, hs₀⟩ := exists_finset_factor (Z.s ≫ spMap (Int.castRingHom (𝓞 c.F))) (y.y ≫ genι Z)
  have hu := fun τ i => exists_finset_factor (Z.t.G.hom ≫ Z.s ≫ spMap (Int.castRingHom (𝓞 c.F))) (y.u τ i)
  choose su hsu using hu
  let b := Module.finBasis ℚ c.F
  let S : Set Qb := (s₀ : Set Qb) ∪ Set.range (fun k => y.fK (b k)) ∪
    ⋃ τ, ⋃ i, (TrivSqZeroExt.fst '' (su τ i : Set (DualNumber Qb)) ∪ TrivSqZeroExt.snd '' (su τ i : Set (DualNumber Qb)))
  have hSfin : S.Finite :=
    (s₀.finite_toSet.union (Set.finite_range _)).union (Set.finite_iUnion fun τ => Set.finite_iUnion fun i =>
      ((su τ i).finite_toSet.image _).union ((su τ i).finite_toSet.image _))
  haveI : Finite S := hSfin.to_subtype
  haveI : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  let Kf : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ Kf :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : NumberField Kf := {}
  have hSK : ∀ z ∈ S, z ∈ Kf := fun z hz => IntermediateField.subset_adjoin ℚ S hz
  let ι : Kf →+* Qb := Kf.val.toRingHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hmem : ∀ x, y.fK x ∈ Kf := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hSK _ (Or.inl (Or.inr ⟨k, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
    | smul q x _ hx => rw [map_rat_smul]; exact Kf.smul_mem hx
  let jF : c.F →+* Kf := y.fK.codRestrict Kf hmem
  have hιjF : ι.comp jF = y.fK := RingHom.ext fun _ => rfl
  obtain ⟨x0, hx0⟩ := hs₀ Kf ι hι fun z hz => ⟨⟨z, hSK z (Or.inl (Or.inl hz))⟩, rfl⟩
  have w : x0 ≫ Z.s = spMap jF ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    apply spMap_cancel ι hι
    rw [reassoc_of% hx0, pullback.condition, ← Category.assoc, y.y_over, ← Category.assoc,
      spMap_comp' jF ι, hιjF]
  let yK : Sp Kf ⟶ gen Z := pullback.lift x0 (spMap jF) w
  have hdual : Function.Injective (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) := by
    intro z z' hzz
    have h1 := congrArg TrivSqZeroExt.fst hzz
    have h2 := congrArg TrivSqZeroExt.snd hzz
    simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR] at h1 h2
    exact TrivSqZeroExt.ext (hι h1) (hι h2)
  have hU : ∀ τ i, ∃ v : Sp (DualNumber Kf) ⟶ Z.t.G.left, spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ v = y.u τ i := by
    intro τ i
    refine hsu τ i (DualNumber Kf) _ hdual ?_
    intro z hz
    have h1 : TrivSqZeroExt.fst z ∈ Kf := hSK _ (Or.inr (Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨i, Or.inl ⟨z, hz, rfl⟩⟩⟩))
    have h2 : TrivSqZeroExt.snd z ∈ Kf := hSK _ (Or.inr (Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨i, Or.inr ⟨z, hz, rfl⟩⟩⟩))
    refine ⟨((⟨_, h1⟩ : Kf), (⟨_, h2⟩ : Kf)), ?_⟩
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, ι]
  choose uK huK using hU
  refine ⟨Kf, inferInstance, inferInstance, ι, jF, yK, uK, hιjF, ?_, pullback.lift_snd _ _ _, fun τ i => (huK τ i).symm⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hx0]
  · rw [Category.assoc, pullback.lift_snd, spMap_comp', hιjF, y.y_over]

end GlobalTheory.FlagDescent
