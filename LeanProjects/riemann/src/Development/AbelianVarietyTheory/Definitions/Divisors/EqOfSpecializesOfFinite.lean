import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.ArInt GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

structure ArMod (D : ℕ) where

  k : Type
  [ring : CommRing k]

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp k
  av : IsArithVar p D

attribute [instance] ArMod.ring ArMod.int

def ArMod.proj (N : ℕ) : ArMod N :=
  @ArMod.mk N ℤ _ (PSpace ℤ N) (GlobalTheory.ProjSpace.isArithVar_int N).isIntegral (PSpace.str ℤ N)
    (GlobalTheory.ProjSpace.isArithVar_int N)

theorem ArMod.finrank_pos {N : ℕ} (m : ArMod N) : 0 < Module.finrank ℤ m.k :=
  have := m.av.isDomain
  have := m.av.finite
  have := m.av.charZero_base
  Module.finrank_pos

abbrev GeomPt {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (ι : k →+* AlgebraicClosure ℚ) : Type :=
  GlobalTheory.Points.PtsOver p (spMap ι)

abbrev GeomPt.base {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : k →+* AlgebraicClosure ℚ}
    (z : GeomPt p ι) : X :=
  z.1 (IsLocalRing.closedPoint (AlgebraicClosure ℚ))

abbrev GeomPt.push {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}
    {ι : k →+* AlgebraicClosure ℚ} (π : X' ⟶ X) (hπ : π ≫ p = q) (z : GeomPt q ι) : GeomPt p ι :=
  GlobalTheory.Points.PtsOver.map π hπ _ z

section Points

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k} {ι : k →+* AlgebraicClosure ℚ}

theorem GeomPt.base_push (π : X' ⟶ X) (hπ : π ≫ p = q) (z : GeomPt q ι) : (z.push π hπ).base = π z.base := rfl

def GeomPt.emb (z : GeomPt p ι) : X.residueField z.base →+* AlgebraicClosure ℚ :=
  (Scheme.descResidueField (Scheme.stalkClosedPointTo z.1)).hom

theorem GeomPt.charZero (z : GeomPt p ι) : CharZero (X.residueField z.base) := z.emb.charZero

theorem isProper_int {N : ℕ} (hX : IsArithVar p N) : IsProper (p ≫ spMap (Int.castRingHom k)) := by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  infer_instance

theorem GeomPt.numberField {N : ℕ} (hX : IsArithVar p N) (z : GeomPt p ι) : NumberField (X.residueField z.base) := by
  have := z.charZero
  have := isProper_int hX
  let t := p ≫ spMap (Int.castRingHom k)
  have h₁ : (t.residueFieldMap z.base).hom.EssFiniteType :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap t z.base)
  let P : PrimeSpectrum ℤ := t z.base
  let e := (Scheme.Spec.residueFieldIso (.of ℤ) (t z.base)).commRingCatIsoToRingEquiv.symm
  have h₂ : ((t.residueFieldMap z.base).hom.comp e.toRingHom).EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_surjective _ e.surjective)) h₁
  have h₃ : (algebraMap ℤ P.asIdeal.ResidueField).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₄ := h₃.comp h₂
  rw [RingHom.ext_int (RingHom.comp _ _) (algebraMap ℤ (X.residueField z.base)), RingHom.essFiniteType_algebraMap] at h₄
  have : Algebra.EssFiniteType ℚ (X.residueField z.base) := .of_comp ℤ ℚ _
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra (R := AlgebraicClosure ℚ)) ▸
      AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic ℚ (X.residueField z.base) :=
    Algebra.IsAlgebraic.of_injective z.emb.toRatAlgHom z.emb.injective
  exact { to_finiteDimensional := Algebra.finite_of_essFiniteType_of_isAlgebraic }

theorem GeomPt.card_emb_pos {N : ℕ} (hX : IsArithVar p N) (z : GeomPt p ι) :
    0 < Nat.card (X.residueField z.base →+* ℂ) :=
  have := z.numberField hX
  Nat.card_pos

theorem GeomPt.push_surjective (π : X' ⟶ X) (hπ : π ≫ p = q) [Surjective π] [LocallyOfFiniteType π] :
    Function.Surjective (GeomPt.push (ι := ι) π hπ) := fun z => by
  let s := Limits.pullback.snd π z.1
  have : JacobsonSpace ↥(Limits.pullback π z.1) := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨w, -⟩ := s.surjective (IsLocalRing.closedPoint _)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := ↥(Limits.pullback π z.1)) ⟨w, Set.mem_univ w⟩
    isOpen_univ.isLocallyClosed
  obtain ⟨u, hu⟩ := (pointEquivClosedPoint s).symm ⟨x, hx⟩
  have e : (u ≫ Limits.pullback.fst π z.1) ≫ π = z.1 := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hu, Category.id_comp]
  exact ⟨⟨u ≫ Limits.pullback.fst π z.1, by rw [← hπ, ← Category.assoc, e, z.2]⟩, Subtype.ext e⟩

end Points

section Dim

variable {X Y : Scheme.{0}}

theorem eq_of_specializes_of_finite (f : X ⟶ Y) [LocallyOfFiniteType f] {x w : X} (h : x ⤳ w) (e : f w = f x)
    (hf : (f.residueFieldMap x).hom.Finite) : x = w := by
  let g : Spec (X.residueField x) ⟶ f.fiber (f x) := Limits.pullback.lift (X.fromSpecResidueField x)
    (Spec.map (f.residueFieldMap x)) (f.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have h₁ : g ≫ f.fiberι (f x) = X.fromSpecResidueField x := Limits.pullback.lift_fst _ _ _
  have h₂ : g ≫ f.fiberToSpecResidueField (f x) = Spec.map (f.residueFieldMap x) := Limits.pullback.lift_snd _ _ _
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have : JacobsonSpace (f.fiber (f x)) := LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField (f x))
  have : IsFinite (g ≫ f.fiberToSpecResidueField (f x)) := h₂ ▸ (IsFinite.SpecMap_iff _).2 hf
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (f.fiberToSpecResidueField (f x))
  let o : Spec (X.residueField x) := IsLocalRing.closedPoint _
  have hc : IsClosed {g o} := g.closePoints_subset_preimage_closedPoints (IsLocalRing.isClosed_singleton_closedPoint _)
  have hx : f.fiberι (f x) (g o) = x := by
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.fromSpecResidueField_apply]
  obtain ⟨w', hw⟩ : w ∈ Set.range (f.fiberι (f x)) := by rw [Scheme.Hom.range_fiberι]; exact e
  have hs : g o ⤳ w' := (f.fiberι (f x)).isEmbedding.isInducing.specializes_iff.1 (by rwa [hx, hw])
  rw [← hx, ← hw, (hs.mem_closed hc rfl : w' = g o)]

theorem finite_of_specializes (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] {x a : X} (h : x ⤳ a)
    [CharZero (X.residueField x)] [Algebra.IsAlgebraic ℚ (X.residueField x)] : (t.residueFieldMap a).hom.Finite := by
  let := (t.residueFieldMap a).hom.toAlgebra
  have : Algebra.EssFiniteType ((Sp ℤ).residueField (t a)) (X.residueField a) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap t a)
  have : Algebra.IsAlgebraic ((Sp ℤ).residueField (t a)) (X.residueField a) := ⟨fun b => by
    obtain ⟨s, rfl⟩ := X.residue_surjective a b
    let φ := (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
    obtain ⟨g, hg, hs⟩ : IsAlgebraic ℤ (φ s) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have h₁ : Polynomial.aeval (φ s) g.primPart = 0 := Polynomial.aeval_primPart_eq_zero hg hs
    have h₂ : X.residue a (Polynomial.aeval s g.primPart) = 0 := by
      refine (IsLocalRing.residue_eq_zero_iff _).2 fun hu => (hu.map φ).ne_zero ?_
      rw [← h₁]
      exact (Polynomial.aeval_algHom_apply φ.toIntAlgHom s _).symm
    refine ⟨g.primPart.map (algebraMap ℤ _), fun h0 => ?_, ?_⟩
    · obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal
        (RingHom.ker (algebraMap ℤ ((Sp ℤ).residueField (t a))))).principal
      have hd : Polynomial.C n ∣ g.primPart := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => by
        rw [← Ideal.mem_span_singleton]
        refine hn.le ?_
        rw [RingHom.mem_ker, ← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
      exact ((g.isPrimitive_primPart n hd).map (algebraMap ℤ ((Sp ℤ).residueField (t a)))).ne_zero
        (hn.ge (Ideal.mem_span_singleton_self n))
    · rw [Polynomial.aeval_map_algebraMap, ← h₂]
      exact Polynomial.aeval_algHom_apply (X.residue a).hom.toIntAlgHom s _⟩
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem dim_le_one_iff (T : Type) [TopologicalSpace T] [T0Space T] [QuasiSober T] :
    topologicalKrullDim T ≤ 1 ↔ ∀ a : T, (∀ b, a ⤳ b → b ⤳ a) ∨ ∀ b, b ⤳ a → a ⤳ b := by
  let := specializationOrder T
  have e : topologicalKrullDim T = Order.krullDim T :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))
  rw [e, Order.krullDim_le_one_iff]
  rfl

theorem dim_closure_le_one_iff (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) ≤ 1 ↔ ∀ a b, x ⤳ a → a ⤳ b → x = a ∨ a = b := by
  have : QuasiSober (closure ({x} : Set X)) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  simp only [dim_le_one_iff, ← IsInducing.subtypeVal.specializes_iff]
  refine ⟨fun H a b ha hb => ?_, fun H a => ?_⟩
  · rcases H ⟨a, ha.mem_closure⟩ with h | h
    · exact .inr (hb.antisymm (h ⟨b, (ha.trans hb).mem_closure⟩ hb)).eq
    · exact .inl (ha.antisymm (h ⟨x, subset_closure rfl⟩ ha)).eq
  · by_cases hx : x = a.1
    · exact .inr fun b _ => hx ▸ specializes_iff_mem_closure.2 b.2
    · exact .inl fun b hb => by rw [(H a b (specializes_iff_mem_closure.2 a.2) hb).resolve_left hx]

end Dim

section Alg

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k} {ι : k →+* AlgebraicClosure ℚ}
  {N : ℕ}

theorem asIdeal_eq_bot [IsDomain k] [Module.Finite ℤ k] (p : X ⟶ Sp k) (x : X) [CharZero (X.residueField x)] :
    (p x).asIdeal = ⊥ := by
  let P : PrimeSpectrum k := p x
  let e := (Scheme.Spec.residueFieldIso (.of k) (p x)).commRingCatIsoToRingEquiv.symm
  have : CharZero P.asIdeal.ResidueField := ((p.residueFieldMap x).hom.comp e.toRingHom).charZero
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (I := P.asIdeal) (eq_bot_iff.2 fun n hn => ?_)
  have h := (Ideal.algebraMap_residueField_eq_zero (I := P.asIdeal)).2 hn
  rw [eq_intCast (algebraMap ℤ k), map_intCast] at h
  exact Int.cast_eq_zero.1 h

theorem exists_specializes_ne (hX : IsArithVar p N) (x : X) [CharZero (X.residueField x)] : ∃ b, x ⤳ b ∧ x ≠ b := by
  by_contra! h
  have : Finite (X.residueField x) := hX.finite_residueField
    (isClosed_of_closure_subset fun b hb => (h b (specializes_iff_mem_closure.2 hb)).symm)
  have := Infinite.of_injective _ (Nat.cast_injective (R := X.residueField x))
  exact not_finite (X.residueField x)

theorem GeomPt.isAlgPt (hX : IsArithVar p N) (z : GeomPt p ι) : IsAlgPt z.base := by
  have := z.numberField hX
  have := isProper_int hX
  let t := p ≫ spMap (Int.castRingHom k)
  refine ⟨inferInstance, le_antisymm ((dim_closure_le_one_iff _).2 fun a b ha hb => ?_) ?_⟩
  · by_cases h0 : (t a).asIdeal = ⊥
    · exact .inl (eq_of_specializes_of_finite t ha (PrimeSpectrum.ext (h0.trans (asIdeal_eq_bot t _).symm))
        (finite_of_specializes t specializes_rfl))
    · refine .inr (eq_of_specializes_of_finite t hb (PrimeSpectrum.ext ?_) (finite_of_specializes t ha))
      exact (((t a).isPrime.isMaximal h0).eq_of_le (t b).isPrime.ne_top
        ((PrimeSpectrum.le_iff_specializes _ _).2 (hb.map t.continuous))).symm
  · obtain ⟨b, hb, hne⟩ := exists_specializes_ne hX z.base
    refine Order.one_le_krullDim_iff.2 ⟨⟨closure {⟨b, hb.mem_closure⟩}, isIrreducible_singleton.closure, isClosed_closure⟩,
      ⟨closure {⟨_, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩, lt_of_le_not_ge ?_ fun h => ?_⟩
    · exact closure_minimal (Set.singleton_subset_iff.2 (IsInducing.subtypeVal.specializes_iff.1 hb).mem_closure)
        isClosed_closure
    · exact hne (hb.antisymm (IsInducing.subtypeVal.specializes_iff.2
        (specializes_iff_mem_closure.2 (h (subset_closure rfl))))).eq

theorem exists_geomPt_mem (hX : IsArithVar p N) (ι : k →+* AlgebraicClosure ℚ) (x : X)
    [CharZero (X.residueField x)] {S : Set X} (hS : IsLocallyClosed S) (hx : x ∈ S) :
    ∃ z : GeomPt p ι, z.base ∈ S := by
  have := hX.isDomain
  have := hX.finite
  have := isProper_int hX
  have : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p (spMap (Int.castRingHom k))
  let o : Sp (AlgebraicClosure ℚ) := IsLocalRing.closedPoint _
  have : CharZero ((Sp (AlgebraicClosure ℚ)).residueField o) := (RingHom.charZero_iff (RingHom.injective
    (Scheme.Spec.residueFieldIso (.of (AlgebraicClosure ℚ)) o).inv.hom)).1
      ((RingHom.charZero_iff (algebraMap (AlgebraicClosure ℚ) _).injective).1 inferInstance)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x o
    (PrimeSpectrum.ext ((asIdeal_eq_bot p x).trans (asIdeal_eq_bot (spMap ι) o).symm))
  let s := Limits.pullback.snd p (spMap ι)
  have : JacobsonSpace ↥(Limits.pullback p (spMap ι)) := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (X := ↥(Limits.pullback p (spMap ι)))
    (Z := Limits.pullback.fst p (spMap ι) ⁻¹' S) ⟨w, Set.mem_preimage.2 (hw ▸ hx)⟩
    (hS.preimage (Limits.pullback.fst p (spMap ι)).continuous)
  let u := (pointEquivClosedPoint s).symm ⟨y, hc⟩
  have hu : u.1 o = y := congrArg Subtype.val ((pointEquivClosedPoint s).apply_symm_apply ⟨y, hc⟩)
  refine ⟨⟨u.1 ≫ Limits.pullback.fst p (spMap ι), ?_⟩, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, u.2, Category.id_comp]
  · change Limits.pullback.fst p (spMap ι) (u.1 o) ∈ S
    rwa [hu]

theorem exists_geomPt (hX : IsArithVar p N) (ι : k →+* AlgebraicClosure ℚ) {x : X} (hx : IsAlgPt x) :
    ∃ z : GeomPt p ι, z.base = x := by
  have := hx.1
  obtain ⟨z, hz⟩ := exists_geomPt_mem hX ι x (isClosed_closure (s := {x})).isLocallyClosed (subset_closure rfl)
  rw [← specializes_iff_mem_closure] at hz
  have := z.charZero
  obtain ⟨b, hb, hne⟩ := exists_specializes_ne hX z.base
  exact ⟨z, (((dim_closure_le_one_iff x).1 hx.2.le _ _ hz hb).resolve_right hne).symm⟩

theorem dense_range_base [IsIntegral X] (hX : IsArithVar p N) (ι : k →+* AlgebraicClosure ℚ) :
    Dense (Set.range (GeomPt.base : GeomPt p ι → X)) := by
  have := hX.charZero
  have : CharZero X.functionField := ((X.germToFunctionField ⊤).hom.charZero_iff
    (X.germToFunctionField_injective ⊤)).1 this
  have : CharZero (X.residueField (genericPoint X)) :=
    (RingHom.charZero_iff (R := X.functionField) (X.residue (genericPoint X)).hom.injective).1 this
  refine dense_iff_inter_open.2 fun U hU hne => ?_
  obtain ⟨z, hz⟩ := exists_geomPt_mem hX ι (genericPoint X) hU.isLocallyClosed
    (((genericPoint_spec X).mem_open_set_iff hU).2 (by simpa using hne))
  exact ⟨_, hz, z, rfl⟩

theorem isProper_of_comp (hX : IsArithVar p N) {N' : ℕ} (hX' : IsArithVar q N') (π : X' ⟶ X) (hπ : π ≫ p = q) :
    IsProper π := by
  have := isProper_int hX
  have : IsProper (π ≫ p ≫ spMap (Int.castRingHom k)) := by
    rw [← Category.assoc, hπ]; exact isProper_int hX'
  exact IsProper.of_comp π (p ≫ spMap (Int.castRingHom k))

theorem dense_preimage_push [IsIntegral X] [IsIntegral X'] (hX : IsArithVar p N) {N' : ℕ} (hX' : IsArithVar q N')
    (π : X' ⟶ X) (hπ : π ≫ p = q) [Surjective π] (hd : 0 < π.residueDegree (genericPoint X')) {Z : Set (GeomPt p ι)}
    (hZ : Dense (GeomPt.base '' Z)) : Dense (GeomPt.base '' (GeomPt.push π hπ ⁻¹' Z)) := by
  have := isProper_of_comp hX hX' π hπ
  let W := closure (GeomPt.base '' (GeomPt.push π hπ ⁻¹' Z))
  have h₁ : GeomPt.base '' Z ⊆ π '' W := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', rfl⟩ := GeomPt.push_surjective π hπ z
    exact ⟨z'.base, subset_closure ⟨z', hz, rfl⟩, rfl⟩
  obtain ⟨w, hw, e⟩ : π (genericPoint X') ∈ π '' W :=
    closure_minimal h₁ (π.isClosedMap _ isClosed_closure) (hZ _)
  have hf : (π.residueFieldMap (genericPoint X')).hom.Finite :=
    let _ := (π.residueFieldMap (genericPoint X')).hom.toAlgebra
    Module.finite_of_finrank_pos hd
  obtain rfl := eq_of_specializes_of_finite π (genericPoint_specializes w) e hf
  exact fun x => (genericPoint_specializes x).mem_closed isClosed_closure hw

end Alg

variable {D : D7} {Y : ShimX D.what₂.Tau}

def IsCompModel (A : SlopeTestRemainingChoices Y) (c : Y.Comp) (m : ArMod (dimY Y)) (b : Y.Pt → m.X) : Prop :=
  (∃ ι : m.k →+* AlgebraicClosure ℚ, IrreducibleSpace ↥(Limits.pullback m.p (spMap ι))) ∧
    b '' (Y.compPt ⁻¹' {c}) = {x | IsAlgPt x} ∧
    ∀ Z, A.dense c Z ↔ Z ⊆ Y.compPt ⁻¹' {c} ∧ Dense (b '' Z)

def IsBundleModel (A : SlopeTestRemainingChoices Y) (c : Y.Comp) (m : ArMod (dimY Y)) (b : Y.Pt → m.X) (L : Y.ALB) (sp nf : Prop) : Prop :=
  ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (q : X' ⟶ Sp m.k) (π : X' ⟶ m.X) (_ : π ≫ m.p = q) (H : HermLB q)
    (n d : ℕ), IsArithVar q (dimY Y) ∧ Surjective π ∧ π.residueDegree (genericPoint X') = d ∧ 0 < d ∧ 0 < n ∧
    H.IsSelfInter ((Module.finrank ℤ m.k : ℝ) * d * (n : ℝ) ^ (dimY Y + 1) * Y.arSelfC L c) ∧
    gdeg H (dimY Y) = (Module.finrank ℤ m.k : ℝ) * d * (n : ℝ) ^ dimY Y * Y.geoC L c ∧
    (sp ↔ H.SemiPos (dimY Y)) ∧ (nf ↔ NefFib H) ∧
    ∀ y, Y.compPt y = c → ∀ x : X', IsAlgPt x → π x = b y → IsPtHt H x (n * A.ht L y)

def TieArOn (A : SlopeTestRemainingChoices Y) (S : Set Y.ALB) : Prop :=
  ∃ sp nf : Y.ALB → Y.Comp → Prop, (∀ L ∈ S, (Y.semipos L ↔ ∀ c, sp L c) ∧ (Y.nefFib L ↔ ∀ c, nf L c)) ∧
    ∀ c : Y.Comp, ∃ (m : ArMod (dimY Y)) (b : Y.Pt → m.X),
      IsCompModel A c m b ∧ ∀ L ∈ S, IsBundleModel A c m b L (sp L c) (nf L c)

def approx (A : SlopeTestRemainingChoices Y) (s₀ : ℝ) : Set Y.ALB :=
  {L | ∃ (B : ℝ) (u : Wt Y) (s : ℚ), 2 ≤ B ∧ IsRat Y u ∧ 0 < s ∧ (s : ℝ) ≤ s₀ ∧ Dominant Y (A.sh u s) ∧ L = Y.Mbar B u s}

def TieAr (A : SlopeTestRemainingChoices Y) : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ TieArOn A ({L | Y.semipos L ∧ Y.nefFib L} ∪ approx A s₀)

theorem TieArOn.mono {A : SlopeTestRemainingChoices Y} {S T : Set Y.ALB} (h : TieArOn A T) (hS : S ⊆ T) : TieArOn A S :=
  have ⟨sp, nf, h₀, h⟩ := h
  ⟨sp, nf, fun L hL => h₀ L (hS hL), fun c =>
    have ⟨m, b, h₁, h₂⟩ := h c
    ⟨m, b, h₁, fun L hL => h₂ L (hS hL)⟩⟩

theorem approx_mono (A : SlopeTestRemainingChoices Y) {s t : ℝ} (h : s ≤ t) : approx A s ⊆ approx A t :=
  fun _ ⟨B, u, r, h₁, h₂, h₃, h₄, h₅⟩ => ⟨B, u, r, h₁, h₂, h₃, h₄.trans h, h₅⟩

theorem TieArOn.tieAr {A : SlopeTestRemainingChoices Y} (h : TieArOn A Set.univ) : TieAr A := ⟨1, one_pos, h.mono (Set.subset_univ _)⟩

theorem TieAr.on_pos {A : SlopeTestRemainingChoices Y} (h : TieAr A) : TieArOn A {L | Y.semipos L ∧ Y.nefFib L} :=
  have ⟨_, _, h⟩ := h
  h.mono Set.subset_union_left

theorem TieAr.on_approx {A : SlopeTestRemainingChoices Y} (h : TieAr A) : ∃ s₀ : ℝ, 0 < s₀ ∧ TieArOn A (approx A s₀) :=
  have ⟨s, hs, h⟩ := h
  ⟨s, hs, h.mono Set.subset_union_right⟩

def IsRelModel (A : SlopeTestRemainingChoices Y) (c : Y.Comp) (L : Y.ALB) (m : ArMod (dimY Y)) (H : HermLB m.p) : Prop :=
  ∃ (n : ℕ) (ν : ℝ) (r : m.X → Y.Pt → Prop), 0 < n ∧ 0 < ν ∧
    H.IsSelfInter (ν * (n : ℝ) ^ (dimY Y + 1) * Y.arSelfC L c) ∧
    gdeg H (dimY Y) = ν * (n : ℝ) ^ dimY Y * Y.geoC L c ∧
    (∀ x, IsAlgPt x → ∃ y, r x y) ∧ (∀ y, Y.compPt y = c → ∃ x, r x y) ∧
    (∀ x y, r x y → IsAlgPt x ∧ Y.compPt y = c ∧ IsPtHt H x (n * A.ht L y)) ∧
    ∀ Z, A.dense c Z → Dense {x : m.X | ∃ y ∈ Z, r x y}

theorem IsBundleModel.exists_rel {A : SlopeTestRemainingChoices Y} {c : Y.Comp} {m : ArMod (dimY Y)} {b : Y.Pt → m.X} {L : Y.ALB} {sp nf : Prop}
    (h : IsCompModel A c m b) (hb : IsBundleModel A c m b L sp nf) :
    ∃ (m' : ArMod (dimY Y)) (H : HermLB m'.p), (sp ↔ H.SemiPos (dimY Y)) ∧ (nf ↔ NefFib H) ∧ IsRelModel A c L m' H := by
  obtain ⟨⟨ι, -⟩, hr, hZ⟩ := h
  obtain ⟨X', _, q, π, hπ, H, n, d, hq, _, hd, hd0, hn, h₁, h₂, h₃, h₄, h₅⟩ := hb
  have := isProper_of_comp m.av hq π hπ
  refine ⟨⟨m.k, X', q, hq⟩, H, h₃, h₄, n, (Module.finrank ℤ m.k : ℝ) * d,
    fun x y => IsAlgPt x ∧ Y.compPt y = c ∧ π x = b y, hn,
    mul_pos (Nat.cast_pos.2 m.finrank_pos) (Nat.cast_pos.2 hd0), h₁, h₂, fun x hx => ?_, fun y hy => ?_, ?_,
    fun Z hz => ?_⟩
  · obtain ⟨w, hw⟩ := exists_geomPt hq ι hx
    obtain ⟨y, hy, e⟩ := hr.ge ((w.push π hπ).isAlgPt m.av)
    exact ⟨y, hx, hy, hw ▸ e.symm⟩
  · obtain ⟨w, hw⟩ := exists_geomPt m.av ι (hr.le ⟨y, hy, rfl⟩)
    obtain ⟨w', rfl⟩ := GeomPt.push_surjective π hπ w
    exact ⟨_, w'.isAlgPt hq, hy, hw⟩
  · rintro x y ⟨hx, hy, e⟩
    exact ⟨hx, hy, h₅ y hy x hx e⟩
  · obtain ⟨hs, hd'⟩ := (hZ Z).1 hz
    have h0 : Dense (GeomPt.base '' {w : GeomPt m.p ι | w.base ∈ b '' Z}) := hd'.mono (by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, hw⟩ := exists_geomPt m.av ι (hr.le ⟨y, hs hy, rfl⟩)
      exact ⟨w, ⟨y, hy, hw.symm⟩, hw⟩)
    refine (dense_preimage_push m.av hq π hπ (hd ▸ hd0) h0).mono ?_
    rintro _ ⟨w, ⟨y, hy, e⟩, rfl⟩
    exact ⟨y, hy, w.isAlgPt hq, hs hy, e.symm⟩

theorem TieArOn.exists_family {A : SlopeTestRemainingChoices Y} {S : Set Y.ALB} (h : TieArOn A S) {L : Y.ALB} (hL : L ∈ S) :
    ∃ (m : Y.Comp → ArMod (dimY Y)) (H : ∀ c, HermLB (m c).p), (Y.semipos L ↔ ∀ c, (H c).SemiPos (dimY Y)) ∧
      (Y.nefFib L ↔ ∀ c, NefFib (H c)) ∧ ∀ c, IsRelModel A c L (m c) (H c) := by
  obtain ⟨sp, nf, h₀, h⟩ := h
  have key := fun c => (h c).elim fun _ h => h.elim fun _ h => IsBundleModel.exists_rel h.1 (h.2 L hL)
  choose m H h₁ h₂ h₃ using key
  exact ⟨m, H, (h₀ L hL).1.trans (forall_congr' h₁), (h₀ L hL).2.trans (forall_congr' h₂), h₃⟩

theorem TieArOn.exists_rel {A : SlopeTestRemainingChoices Y} {S : Set Y.ALB} (h : TieArOn A S) {L : Y.ALB} (hL : L ∈ S) (c : Y.Comp) :
    ∃ (m : ArMod (dimY Y)) (H : HermLB m.p) (n : ℕ) (ν : ℝ) (r : m.X → Y.Pt → Prop), 0 < n ∧ 0 < ν ∧
      H.IsSelfInter (ν * (n : ℝ) ^ (dimY Y + 1) * Y.arSelfC L c) ∧
      gdeg H (dimY Y) = ν * (n : ℝ) ^ dimY Y * Y.geoC L c ∧
      (Y.semipos L → H.SemiPos (dimY Y)) ∧ (Y.nefFib L → NefFib H) ∧
      (∀ x, IsAlgPt x → ∃ y, r x y) ∧ (∀ y, Y.compPt y = c → ∃ x, r x y) ∧
      (∀ x y, r x y → IsAlgPt x ∧ Y.compPt y = c ∧ IsPtHt H x (n * A.ht L y)) ∧
      ∀ Z, A.dense c Z → Dense {x : m.X | ∃ y ∈ Z, r x y} := by
  obtain ⟨m, H, h₁, h₂, h₃⟩ := h.exists_family hL
  obtain ⟨n, ν, r, a₁, a₂, a₃, a₄, a₅⟩ := h₃ c
  exact ⟨m c, H c, n, ν, r, a₁, a₂, a₃, a₄, fun h => h₁.1 h c, fun h => h₂.1 h c, a₅⟩

theorem TieAr.exists_rel {A : SlopeTestRemainingChoices Y} (h : TieAr A) {L : Y.ALB} (hs : Y.semipos L) (hn : Y.nefFib L) (c : Y.Comp) :
    ∃ (m : ArMod (dimY Y)) (H : HermLB m.p), H.SemiPos (dimY Y) ∧ NefFib H ∧ IsRelModel A c L m H :=
  have ⟨m, H, h₁, h₂, h₃⟩ := h.on_pos.exists_family (L := L) ⟨hs, hn⟩
  ⟨m c, H c, h₁.1 hs c, h₂.1 hn c, h₃ c⟩

theorem IsCompModel.dense_comp {A : SlopeTestRemainingChoices Y} {c : Y.Comp} {m : ArMod (dimY Y)} {b : Y.Pt → m.X}
    (h : IsCompModel A c m b) : A.dense c (Y.compPt ⁻¹' {c}) ∧ ¬ A.dense c ∅ := by
  obtain ⟨⟨ι, -⟩, hr, hZ⟩ := h
  refine ⟨(hZ _).2 ⟨le_rfl, ?_⟩, fun h0 => ?_⟩
  · rw [hr]
    exact (dense_range_base m.av ι).mono (by rintro _ ⟨z, rfl⟩; exact z.isAlgPt m.av)
  · simpa using ((hZ _).1 h0).2.nonempty

def thick (Y : ShimX D.what₂.Tau) (F : Type) : ShimX D.what₂.Tau :=
  { Y with
    Pt := Y.Pt × F
    phiDR := fun p y => Y.phiDR p y.1
    phiMod := fun p y => Y.phiMod p y.1
    phiFr := fun p y => Y.phiFr p y.1
    compPt := fun y => Y.compPt y.1
    normDetT := fun p τ y => Y.normDetT p τ y.1
    normDetH := fun p τ y => Y.normDetH p τ y.1 }

def thickeningHeights (A : SlopeTestRemainingChoices Y) (F : Type) : SlopeTestRemainingChoices (thick Y F) where
  dir := A.dir
  w := A.w
  Ps := A.Ps
  ht L y := A.ht L y.1
  dense c Z := Z ⊆ (thick Y F).compPt ⁻¹' {c} ∧ A.dense c (Prod.fst '' Z)

theorem TieArOn.thick {A : SlopeTestRemainingChoices Y} {S : Set Y.ALB} (h : TieArOn A S) (F : Type) [Nonempty F] :
    TieArOn (thickeningHeights A F) S := by
  obtain ⟨sp, nf, h₀, h⟩ := h
  refine ⟨sp, nf, h₀, fun c => ?_⟩
  obtain ⟨m, b, ⟨hι, hr, hZ⟩, hb⟩ := h c
  refine ⟨m, fun y => b y.1, ⟨hι, ?_, fun Z => ?_⟩, fun L hL => ?_⟩
  · rw [← hr]
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨y.1, hy, rfl⟩,
      by rintro ⟨y, hy, rfl⟩; exact ⟨(y, Classical.arbitrary F), hy, rfl⟩⟩
  · refine and_congr_right fun hs => (hZ _).trans ?_
    refine Iff.trans ?_ (iff_of_eq (congrArg Dense (Set.image_image b Prod.fst (show Set (Y.Pt × F) from Z))))
    exact and_iff_right (by rintro _ ⟨y, hy, rfl⟩; exact hs hy)
  · obtain ⟨X', i, q, π, hπ, H, n, d, hq, s, hd, hd0, hn, h₁, h₂, h₃, h₄, h₅⟩ := hb L hL
    exact ⟨X', i, q, π, hπ, H, n, d, hq, s, hd, hd0, hn, h₁, h₂, h₃, h₄, fun y hy => h₅ y.1 hy⟩

namespace ProjEx

def htFn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) : X → ℝ :=
  Classical.epsilon fun h => L.IsArithHeight h

abbrev dm (D : D7) : ℕ := Formalism.DegreeFormula.dimFl D.what₂.Tau 2

abbrev emb : ℤ →+* AlgebraicClosure ℚ := Int.castRingHom _

def bun (N : ℕ) (a : ℕ × ℝ) : HermLB (PSpace.str ℤ N) :=
  ((GlobalTheory.ProjSpace.hermitianTwistingSheaf ℤ N).pow a.1).shift (fun _ => a.2) fun _ => rfl

def shim (D : D7) : ShimX D.what₂.Tau where
  N := 2
  j := 1
  j_pos := le_rfl
  j_lt := one_lt_two
  lev := ∅
  lev_prime := by simp
  Comp := Bool
  vol := 1
  chern := 0
  chern_homog _ _ _ _ := rfl
  arDeg _ _ := 0
  arDeg_homog _ _ _ _ _ _ := rfl
  arMix _ _ _ := 0
  arMix_HT _ _ _ _ := rfl
  arMix_DR _ _ _ _ := rfl
  CurveHT _ := Unit
  degHT _ _ _ := 0
  CurveDR _ := Unit
  degDR _ _ _ := 0
  FibComp _ := Unit
  fibInBd _ _ := False
  Pt := Bool × GeomPt (PSpace.str ℤ (dm D)) emb
  phiDR _ _ _ := 0
  phiMod _ _ _ := 0
  phiFr _ _ _ := 0
  XC := Bool
  rfn _ := Real.exp 1
  rfn_ge _ := le_rfl
  hLo _ := 1
  hUp _ := 1
  hLo_le _ := ⟨one_pos, le_rfl⟩
  connN _ := 0
  curvN _ := 0
  compOf c := c
  normDetInf _ _ := 1
  compPt := Prod.fst
  normDetT _ _ _ := 1
  normDetH _ _ _ := 1
  htDetT _ _ _ := 0
  ALB := Bool → ℕ × ℝ
  arSelf L := ∑ c, htFn (bun (dm D) (L c)) (genericPoint (ArMod.proj (dm D)).X)
  arSelfC L c := htFn (bun (dm D) (L c)) (genericPoint (ArMod.proj (dm D)).X)
  arSelf_sum _ := rfl
  geo L := ∑ c, gdeg (bun (dm D) (L c)) (dm D)
  geoC L c := gdeg (bun (dm D) (L c)) (dm D)
  geo_sum _ := rfl
  arVol L := ∑ c, (arVol (bun (dm D) (L c)) (dm D)).toReal
  semipos L := ∀ c, (bun (dm D) (L c)).SemiPos (dm D)
  nefFib L := ∀ c, NefFib (bun (dm D) (L c))
  arNef L := ∀ c, (bun (dm D) (L c)).IsNef (dm D)
  Mbar _ _ _ _ := (1, 0)

def aux (D : D7) : SlopeTestRemainingChoices (shim D) where
  dir _ _ := 0
  w _ := 1
  Ps _ _ := 0
  ht L y := htFn (bun (dm D) (L y.1)) y.2.base / Nat.card ((PSpace ℤ (dm D)).residueField y.2.base →+* ℂ)
  dense c Z := Z ⊆ Prod.fst ⁻¹' {c} ∧ Dense (GeomPt.base '' (Prod.mk c ⁻¹' Z))

theorem tieArOn_univ (hE : GlobalTheory.Published.ArExists) (D : D7) : TieArOn (aux D) Set.univ := by
  refine ⟨fun L c => (bun (dm D) (L c)).SemiPos (dm D), fun L c => NefFib (bun (dm D) (L c)),
    fun L _ => ⟨Iff.rfl, Iff.rfl⟩, fun c => ?_⟩
  have av := (ArMod.proj (dm D)).av
  refine ⟨ArMod.proj (dm D), fun y => y.2.base, ⟨⟨emb, ?_⟩, ?_, fun Z => ?_⟩, fun L _ => ?_⟩
  · have := GlobalTheory.ProjSpace.isIntegral_of_isDomain (AlgebraicClosure ℚ) (dm D)
    exact (GlobalTheory.ProjSpace.isPullback_baseChange (dm D) emb).isoPullback.hom.homeomorph.irreducibleSpace_iff.1
      inferInstance
  · ext x
    refine ⟨by rintro ⟨y, -, rfl⟩; exact y.2.isAlgPt av, fun hx => ?_⟩
    obtain ⟨w, hw⟩ := exists_geomPt av emb hx
    exact ⟨(c, w), rfl, hw⟩
  · refine and_congr_right fun hs => iff_of_eq (congrArg Dense ?_)
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(c, w), hw, rfl⟩
    · rintro ⟨⟨a, w⟩, hw, rfl⟩
      obtain rfl : a = c := hs hw
      exact ⟨w, hw, rfl⟩
  · have hh : (bun (dm D) (L c)).IsArithHeight (htFn (bun (dm D) (L c))) :=
      Classical.epsilon_spec ((@hE ℤ _ _ (ArMod.proj (dm D)).int _ _ av).1 _)
    have h1 : Module.finrank ℤ (ArMod.proj (dm D)).k = 1 := Module.finrank_self ℤ
    refine ⟨_, (ArMod.proj (dm D)).int, _, 𝟙 _, Category.id_comp _, bun (dm D) (L c), 1, 1, av,
      inferInstance, Scheme.Hom.residueDegree_id _, one_pos, one_pos, ⟨_, hh, ?_⟩, ?_, Iff.rfl, Iff.rfl, ?_⟩
    · simp only [h1, Nat.cast_one, one_pow, one_mul]
      rfl
    · simp only [h1, Nat.cast_one, one_pow, one_mul]
      rfl
    · rintro ⟨a, w⟩ ha x - e
      obtain rfl : a = c := ha
      obtain rfl : x = w.base := e
      have h0 : (Nat.card ((PSpace ℤ (dm D)).residueField w.base →+* ℂ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.2 (w.card_emb_pos av).ne'
      refine ⟨_, hh, ?_⟩
      rw [Nat.cast_one, one_mul]
      exact (div_mul_cancel₀ _ h0).symm

theorem tieAr (hE : GlobalTheory.Published.ArExists) (D : D7) : TieAr (aux D) := (tieArOn_univ hE D).tieAr

theorem tieAr_thick (hE : GlobalTheory.Published.ArExists) (D : D7) : TieAr (thickeningHeights (aux D) ℕ) :=
  ((tieArOn_univ hE D).thick ℕ).tieAr

theorem mem_approx (D : D7) {s₀ : ℝ} (h : 0 < s₀) : (fun _ => (1, 0) : (shim D).ALB) ∈ approx (aux D) s₀ := by
  obtain ⟨s, h₁, h₂⟩ := exists_rat_btwn h
  refine ⟨2, 0, s, le_rfl, fun _ _ => ⟨0, by simp⟩, by exact_mod_cast h₁, h₂.le, ?_, rfl⟩
  have e : (aux D).sh 0 s = fun _ _ => 0 := by
    funext τ i
    simp [SlopeTestRemainingChoices.sh, aux]
  rw [e]
  simp [Dominant]

example (D : D7) : (bun (dm D) (1, 0)).B = lbPow (GlobalTheory.ProjSpace.O1 ℤ (dm D)) 1 := rfl

example (N : ℕ) : Module.finrank ℤ (ArMod.proj N).k = 1 ∧
    (𝟙 (ArMod.proj N).X : _ ⟶ _).residueDegree (genericPoint (ArMod.proj N).X) = 1 :=
  ⟨Module.finrank_self ℤ, Scheme.Hom.residueDegree_id _⟩

example (D : D7) : (aux D).dense true (Prod.fst ⁻¹' {true}) ∧ ¬ (aux D).dense false (Prod.fst ⁻¹' {true}) := by
  have hd := dense_range_base (ArMod.proj (dm D)).av emb
  refine ⟨⟨le_rfl, hd.mono ?_⟩, fun h => ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl, rfl⟩
  · obtain ⟨_, z, -⟩ := hd.nonempty
    exact Bool.noConfusion (h.1 (show (true, z) ∈ Prod.fst ⁻¹' {true} from rfl))

end ProjEx

end GlobalTheory.Mean4O
