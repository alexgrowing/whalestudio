import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne

open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.TraitGlue

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] {a b : A}
    (ha : a ≠ 0) (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b) : a ∣ b := by
  have ha' : algebraMap A (FractionRing A) a ≠ 0 := fun e =>
    ha (IsFractionRing.injective A (FractionRing A) (e.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := KrullAlg.mem_range_of_forall_height_one (A := A)
    (algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) a) (fun P hP h1 => by
      obtain ⟨c, hc⟩ := h P h1
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have e : algebraMap A (Localization.AtPrime P) (s * b) = algebraMap A (Localization.AtPrime P) (a * r) := by
        rw [map_mul, map_mul, hc, mul_left_comm, IsLocalization.mk'_spec']
      have e' : s * b = a * r := IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors e
      refine ⟨s, s.2, r, ?_⟩
      rw [← mul_div_assoc, ← map_mul, e', map_mul, mul_div_cancel_left₀ _ ha'])
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem dvd_of_generisations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (x : X)
    {a b : X.presheaf.stalk x} (ha : a ≠ 0)
    (h : ∀ (η : X) (hη : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      (X.presheaf.stalkSpecializes hη).hom a ∣ (X.presheaf.stalkSpecializes hη).hom b) : a ∣ b := by
  have := (hX x).2
  refine dvd_of_height_one ha fun q _ hq => ?_
  let y : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x q
  have hs : X.fromSpecStalk x y ⤳ x := by
    have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : ∀ t, e ((X.presheaf.stalkSpecializes hs).hom t) = algebraMap _ (Localization.AtPrime q) t := by
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq t
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
    erw [h3]
    exact he U _ hxU s
  rw [← hcomp, ← hcomp]
  refine map_dvd e (h _ hs ?_)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
  rfl

theorem finite_dim_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X.Opens) {z : X} (hzW : z ∈ W) (hzV : z ∈ V) :
    {η : X | η ∈ W ∧ ringKrullDim (X.presheaf.stalk η) = 1 ∧ η ∉ V}.Finite := by
  obtain ⟨a, haV, hza⟩ := hW.exists_basicOpen_le ⟨z, hzV⟩ hzW
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hza
  have hfin := (KrullAlg.finite_height_one ha).preimage
    (f := fun p : PrimeSpectrum Γ(X, W) => p.asIdeal) (fun _ _ _ _ e => PrimeSpectrum.ext e)
  refine (hfin.image (fun p => hW.fromSpec p)).subset ?_
  rintro η ⟨h1, h2, h3⟩
  letI : Algebra Γ(X, W) (X.presheaf.stalk η) := X.presheaf.algebra_section_stalk ⟨η, h1⟩
  haveI := hW.isLocalization_stalk ⟨η, h1⟩
  refine ⟨hW.primeIdealOf ⟨η, h1⟩, ⟨inferInstance, ?_, ?_⟩, hW.fromSpec_primeIdealOf ⟨η, h1⟩⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hW.primeIdealOf ⟨η, h1⟩).asIdeal] at h2
    exact_mod_cast h2
  · by_contra hn
    refine h3 (haV ((X.mem_basicOpen a η h1).2 ?_))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk η) (hW.primeIdealOf ⟨η, h1⟩).asIdeal a).2 hn

theorem associated_of_map {A V : Type} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing V] [IsDomain V]
    (φ : A →+* V) [IsLocalHom φ] {a b : A} (h : Associated (φ a) (φ b)) (ha : φ a ≠ 0) : Associated a b := by
  have key : ∀ {a c : A}, Associated (φ a) (φ (a * c)) → φ a ≠ 0 → Associated a (a * c) := by
    intro a c h ha
    rw [map_mul] at h
    have : IsUnit (φ c) := isUnit_of_associated_mul h.symm ha
    exact (associated_mul_unit_left _ _ (isUnit_of_map_unit φ c this)).symm
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact key h ha
  · exact (key h.symm (h.ne_zero_iff.1 ha)).symm

theorem valuationRing_stalk {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (η : X)
    (h : ringKrullDim (X.presheaf.stalk η) = 1) : ValuationRing (X.presheaf.stalk η) := by
  have := (hX η).2
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk η) := by
    rw [Ring.krullDimLE_iff, h]
    norm_num
  have : Ring.DimensionLEOne (X.presheaf.stalk η) := by
    refine ⟨fun {p} hp hprime => ?_⟩
    rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
    · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
      exact absurd h hp
    · exact h
  have : IsDedekindDomain (X.presheaf.stalk η) :=
    (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk η))).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩
  have h2 := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk η)).out 2 1
  exact h2.1 this

theorem specializes_germ {X : Scheme.{0}} {W : X.Opens} {x η : X} (h : η ⤳ x) (hx : x ∈ W) (hη : η ∈ W) (s : Γ(X, W)) :
    (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ W x hx).hom s) = (X.presheaf.germ W η hη).hom s :=
  congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

theorem exists_spread {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (x : X) (h0 : f x ≠ 0)
    (hc : ∀ (η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(X, W)), (X.presheaf.germ W x hx).hom s = f x ∧
      ∀ (η : X) (hη : η ∈ W), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.germ W η hη).hom s) (f η) := by
  obtain ⟨W₀, hx₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (f x)
  obtain ⟨⟨W, hW⟩, hx, hle⟩ := EffCartierData.exists_affine_le hx₀
  let s : Γ(X, W) := resG X hle s₀
  have hs : (X.presheaf.germ W x hx).hom s = f x := (Cartier.germ_resG hle _ hx _).trans hs₀
  let B : Set X := {η | ∃ hη : η ∈ W, ringKrullDim (X.presheaf.stalk η) = 1 ∧
    ¬ Associated ((X.presheaf.germ W η hη).hom s) (f η)}
  have hgen : ∀ {V : X.Opens} {y : X}, y ∈ V → genericPoint X ∈ V := fun {V y} hy =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
  have hB : B.Finite := by
    rcases B.eq_empty_or_nonempty with h | ⟨η₀, -, h₀, -⟩
    · rw [h]; exact Set.finite_empty
    have hs0 : s ≠ 0 := fun e => h0 (by rw [← hs, e, map_zero])
    have hb : genericPoint X ∈ X.basicOpen s := by
      rw [X.mem_basicOpen s _ (hgen hx)]
      have : (X.presheaf.germ W _ (hgen hx)).hom s ≠ 0 := fun e =>
        hs0 (germ_injective_of_isIntegral X _ (hgen hx) (e.trans (map_zero _).symm))
      exact (IsUnit.mk0 (G₀ := X.functionField) _ this)
    refine (finite_dim_one hW (U ⊓ X.basicOpen s) (hgen hx) ⟨hne η₀ h₀, hb⟩).subset ?_
    rintro η ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h4 => h3 ?_⟩
    exact (associated_one_iff_isUnit.2 ((X.mem_basicOpen s η h1).1 h4.2)).trans
      (associated_one_iff_isUnit.2 (hU η h4.1 h2)).symm
  have hcl : IsClosed (⋃ η ∈ B, closure ({η} : Set X)) := hB.isClosed_biUnion fun _ _ => isClosed_closure
  let W' : X.Opens := W ⊓ ⟨_, hcl.isOpen_compl⟩
  have hx' : x ∈ W' := by
    refine ⟨hx, fun hm => ?_⟩
    obtain ⟨η, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.1 hm
    have h5 : η ⤳ x := specializes_iff_mem_closure.2 h4
    refine h3 ?_
    rw [← specializes_germ h5 hx h1, hs]
    exact hc η h5 h2
  refine ⟨W', hx', resG X inf_le_left s, (Cartier.germ_resG _ _ hx' _).trans hs, fun η hη h1 => ?_⟩
  rw [Cartier.germ_resG]
  by_contra hn
  exact hη.2 (Set.mem_iUnion₂.2 ⟨η, ⟨hη.1, h1, hn⟩, subset_closure rfl⟩)

theorem exists_of_germs {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (h0 : ∀ x, f x ≠ 0)
    (hc : ∀ (x η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧
      ∀ x, FinalTheorems.stalkId D.idealSheaf x = Ideal.span {f x} := by
  choose W hx s hs hW using fun x => exists_spread U f hU hne x (h0 x) (hc x)
  have hs0 : ∀ x, s x ≠ 0 := fun x e => h0 x (by rw [← hs x, e, map_zero])
  have hreg : ∀ x, Cartier.IsRegularFn (s x) := fun x => Cartier.isRegularFn_of_ne_zero (hs0 x)
  have hdvd : ∀ (i j y : X) (hi : y ∈ W i) (hj : y ∈ W j),
      (X.presheaf.germ _ y hi).hom (s i) ∣ (X.presheaf.germ _ y hj).hom (s j) := by
    intro i j y hi hj
    refine dvd_of_generisations hX y (fun e =>
      hs0 i (germ_injective_of_isIntegral X _ hi (e.trans (map_zero _).symm))) fun η hη h1 => ?_
    have hi' : η ∈ W i := hη.mem_open (W i).isOpen hi
    have hj' : η ∈ W j := hη.mem_open (W j).isOpen hj
    rw [specializes_germ hη hi hi', specializes_germ hη hj hj']
    exact ((hW i η hi' h1).trans (hW j η hj' h1).symm).dvd
  let D : EffCartierData X :=
    { ι := X
      U := W
      f := s
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      regular := hreg
      assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun y hy => by
        rw [Cartier.germ_resG, Cartier.germ_resG]
        exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hdvd j i y hy.2 hy.1))
          (Ideal.span_singleton_le_span_singleton.2 (hdvd i j y hy.1 hy.2)) }
  refine ⟨D, fun x hxD hxU => ?_, fun x => (D.stalkId_idealSheaf x x (hx x)).trans (congrArg (fun t => Ideal.span {t}) (hs x))⟩
  refine (D.mem_support_iff x (hx x)).1 hxD ((X.mem_basicOpen (s x) x (hx x)).2 ?_)
  change IsUnit ((X.presheaf.germ _ x (hx x)).hom (s x))
  rw [hs x]
  refine isUnit_of_dvd_one (dvd_of_generisations hX x (h0 x) fun η hη h1 => ?_)
  exact ((hc x η hη h1).symm.isUnit (hU η (hη.mem_open U.isOpen hxU) h1)).dvd

theorem exists_effCartier_of_orders : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U : X.Opens) (R : ATrait X → ℕ → Prop), (∀ (T : ATrait X) (a : ℕ), Set.range T.ξ ⊆ U → R T a → a = 0) → (∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → ∃ (T : ATrait X) (a e : ℕ), T.CentredAt η e ∧ T.GenIn U ∧ R T a) → (∀ x : X, ∃ f : X.presheaf.stalk x, ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ), T.GenIn U → R T a → T.HasOrd h f a) → ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧ ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a → idlAlong D.idealSheaf T.ξ = Ideal.span {T.ϖ ^ a} := by
  intro X _ _ hX U R hR hT hf
  have hf' : ∀ x : X, ∃ f : X.presheaf.stalk x, f ≠ 0 ∧ ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ),
      T.GenIn U → R T a → T.HasOrd h f a := by
    intro x
    obtain ⟨f, hf⟩ := hf x
    by_cases h0 : f = 0
    · refine ⟨1, one_ne_zero, fun T h a h1 h2 => ?_⟩
      have := hf T h a h1 h2
      rw [h0, ATrait.HasOrd, map_zero, map_zero, Ideal.span_singleton_eq_span_singleton] at this
      exact absurd (this.eq_zero_iff.1 rfl) (pow_ne_zero _ T.irr.ne_zero)
    · exact ⟨f, h0, hf⟩
  choose f h0 hf using hf'
  have hself : ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a →
      Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom (f _)} = Ideal.span {T.ϖ ^ a} := by
    intro T a h1 h2
    have := hf _ T specializes_rfl a h1 h2
    rwa [ATrait.HasOrd, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at this
  obtain ⟨D, hD, hD'⟩ := exists_of_germs hX U f (fun η hη h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have ha : a = 0 := hR T a (by
        rintro _ ⟨p, rfl⟩
        exact ((IsLocalRing.specializes_closedPoint p).map T.ξ.continuous).mem_open U.isOpen hη) h3
      have := hself T a h2 h3
      rw [ha, pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at this
      exact isUnit_of_map_unit _ _ this)
    (fun η h1 => by
      obtain ⟨T, a, e, -, h2, -⟩ := hT η h1
      obtain ⟨p⟩ : Nonempty (Sp (FractionRing T.V)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, h2 ⟨p, rfl⟩⟩) h0
    (fun x η h h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have := valuationRing_stalk hX _ h1
      have e1 := Ideal.span_singleton_eq_span_singleton.1 (hf x T h a h2 h3)
      have e2 := Ideal.span_singleton_eq_span_singleton.1 (hself T a h2 h3)
      exact associated_of_map (Scheme.stalkClosedPointTo T.ξ).hom (e1.trans e2.symm)
        (e1.ne_zero_iff.2 (pow_ne_zero _ T.irr.ne_zero)))
  refine ⟨D, hD, fun T a h1 h2 => ?_⟩
  rw [idlAlong, hD', Ideal.map_span, Set.image_singleton]
  exact hself T a h1 h2

end GlobalTheory.Poinc.TraitGlue
