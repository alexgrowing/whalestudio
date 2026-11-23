import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_pow (hf : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map (Scheme.stalkClosedPointTo y).hom).ne_zero

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dif_pos ht]
  | simp only [valR, dif_pos ht]
  | simp only [valR, ht, dite_true]
  refine H.trans ?_
  first
  | rfl
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; done)
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; rfl)
  | (simp [Scheme.Hom.appLE]; done)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dif_pos hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

theorem regAt_of_pow {x : Z} (hx : IsIntegrallyClosed (Z.presheaf.stalk x)) {n : ℕ} (hn : 0 < n)
    (h : RegAt x (f ^ n)) : RegAt x f := by
  haveI := hx
  obtain ⟨a, ha⟩ := h
  have hint : IsIntegral (Z.presheaf.stalk x) f := by
    refine ⟨Polynomial.X ^ n - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hn.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ha]
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Z.presheaf.stalk x)
    (K := Z.functionField)).1 hint
  exact ⟨b, hb⟩

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

theorem isPreimmersion_j : IsPreimmersion M.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip this

private theorem asIdeal_spMap_algebraMap_eq_bot (s : Sp F) : (spMap (algebraMap (𝓞 F) F) s).asIdeal = ⊥ := by
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have e : (spMap (algebraMap (𝓞 F) F) s).asIdeal = Ideal.comap (algebraMap (𝓞 F) F) s.asIdeal := by
    first
    | rfl
    | simp [spMap]
    | simp [spMap, Spec.map_base]
  rw [e, hs]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j {x : M.X} (hx : (M.p x).asIdeal = ⊥) : x ∈ Set.range M.j := by
  have e : M.p x = spMap (algebraMap (𝓞 F) F) (IsLocalRing.closedPoint F) :=
    PrimeSpectrum.ext (hx.trans (asIdeal_spMap_algebraMap_eq_bot _).symm)
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ e
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz1, ← M.pb.isoPullback_inv_fst]
  first
  | rfl
  | exact (Scheme.comp_apply _ _ _).symm
  | simp

theorem asIdeal_p_j (y : Y.X) : (M.p (M.j y)).asIdeal = ⊥ := by
  have e : M.p (M.j y) = spMap (algebraMap (𝓞 F) F) (Y.str y) := by
    first
    | (show (M.j ≫ M.p) y = (Y.str ≫ spMap _) y
       rw [M.pb.w])
    | rw [← Scheme.comp_apply, M.pb.w, Scheme.comp_apply]
  rw [e, asIdeal_spMap_algebraMap_eq_bot]

theorem asIdeal_p_gen [IsIntegral M.X] : (M.p (genericPoint M.X)).asIdeal = ⊥ := by
  obtain ⟨y⟩ : Nonempty Y.X := inferInstance
  have hs : genericPoint M.X ⤳ M.j y := (genericPoint_spec M.X).specializes trivial
  have h3 : (M.p (genericPoint M.X)).asIdeal ≤ (M.p (M.j y)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (M.p.base.hom.map_specializes hs)
  rw [asIdeal_p_j] at h3
  exact le_bot_iff.1 h3

theorem j_gen_specializes [IsIntegral M.X] : M.j (genericPoint Y.X) ⤳ genericPoint M.X := by
  obtain ⟨y0, hy0⟩ := mem_range_j M (asIdeal_p_gen M)
  rw [← hy0]
  exact M.j.base.hom.map_specializes ((genericPoint_spec Y.X).specializes trivial)

end Model

end GlobalTheory.TrueGeo.SmallSec
