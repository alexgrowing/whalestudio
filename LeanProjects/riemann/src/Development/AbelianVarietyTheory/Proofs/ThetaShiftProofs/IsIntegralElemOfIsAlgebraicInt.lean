import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.ArcConst

def AlgZ {A : Type} [CommRing A] (s : A) : Prop := IsAlgebraic ℤ s

theorem algZ_of {A : Type} [CommRing A] [inst : Algebra ℤ A] {s : A} (h : IsAlgebraic ℤ s) : AlgZ s := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact h

theorem AlgZ.map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {s : A} (h : AlgZ s) : AlgZ (f s) :=
  IsAlgebraic.algHom f.toIntAlgHom h

theorem AlgZ.sub {A : Type} [CommRing A] {s t : A} (h : AlgZ s) (h' : AlgZ t) : AlgZ (s - t) :=
  IsAlgebraic.sub (R := ℤ) h h'

theorem isIntegralElem_of_isAlgebraic_int {K A : Type} [Field K] [CharZero K] [CommRing A] (f : K →+* A)
    {s : A} (hs : AlgZ s) : f.IsIntegralElem s := by
  let := f.toAlgebra
  have h : IsAlgebraic K s := IsAlgebraic.extendScalars (R := ℤ) (A_alg := hs) (RingHom.injective_int (algebraMap ℤ K))
  exact h.isIntegral

theorem isUnit_of_isIntegralElem {K A : Type} [Field K] [CommRing A] [IsDomain A] (f : K →+* A)
    {s : A} (hs : f.IsIntegralElem s) (h0 : s ≠ 0) : IsUnit s := by
  let := f.toAlgebra
  exact IsIntegral.isUnit (R := K) hs h0

theorem exists_of_localization {K R S : Type} [Field K] [CharZero K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (f : K →+* R)
    {s : S} (hs : AlgZ s) : ∃ r : R, algebraMap R S r = s ∧ AlgZ r := by
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have h1 : ((algebraMap R S).comp f).IsIntegralElem s := isIntegralElem_of_isAlgebraic_int _ hs
  have h2 : IsIntegral R s := by
    obtain ⟨p, hp, hp0⟩ := h1
    exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hp0⟩
  let g : S →ₐ[R] FractionRing R := IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R (FractionRing R))
    (fun y => IsLocalization.map_units (M := nonZeroDivisors R) (FractionRing R) ⟨y.1, hM y.2⟩)
  have hg : Function.Injective g := by
    let : Algebra S (FractionRing R) := g.toRingHom.toAlgebra
    have : IsScalarTower R S (FractionRing R) := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
    have : IsFractionRing S (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S (FractionRing R)
    exact IsFractionRing.injective S (FractionRing R)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h2.map g)
  have hrs : algebraMap R S r = s := hg (by rw [g.commutes]; exact hr)
  refine ⟨r, hrs, ?_⟩
  rw [← hrs] at hs
  exact (isAlgebraic_algHom_iff (algebraMap R S).toIntAlgHom hinj).1 hs

theorem powerSeries_const {K : Type} [Field K] [CharZero K] {p : PowerSeries K} (hp : AlgZ p) :
    ∃ x : K, p = PowerSeries.C (R := K) x := by
  refine ⟨PowerSeries.constantCoeff p, ?_⟩
  by_contra hne
  have h1 : AlgZ (PowerSeries.C (R := K) (PowerSeries.constantCoeff p)) :=
    (hp.map (PowerSeries.constantCoeff (R := K))).map (PowerSeries.C (R := K))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (PowerSeries.C (R := K)) (hp.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (PowerSeries.constantCoeff (R := K))
  simp at h3

theorem mvPolynomial_const {σ L : Type} [Field L] [CharZero L] {P : MvPolynomial σ L} (hP : AlgZ P) :
    ∃ y : L, P = MvPolynomial.C y ∧ AlgZ y := by
  refine ⟨MvPolynomial.constantCoeff P, ?_, hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))⟩
  by_contra hne
  have h1 : AlgZ (MvPolynomial.C (σ := σ) (MvPolynomial.constantCoeff P)) :=
    (hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))).map (MvPolynomial.C (σ := σ) (R := L))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (MvPolynomial.C (σ := σ) (R := L)) (hP.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (MvPolynomial.constantCoeff (R := L) (σ := σ))
  simp at h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcDet_ne_zero (Dw : Datum H) (K : Type) [Field K] : arcDet Dw K ≠ 0 := by
  classical
  intro h0
  have h := congrArg (MvPolynomial.eval (fun t : ArcLt Dw => if t.2.1 = t.2.2 then (1 : LaurentSeries K) else 0)) h0
  rw [arcDet, map_prod, map_zero, Finset.prod_eq_one] at h
  · exact one_ne_zero h
  · intro τ _
    rw [RingHom.map_det]
    convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := LaurentSeries K)
    ext1 i k
    simp [Matrix.one_apply]

theorem algebraMap_injective (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
  IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) (S := ArcS Dw K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))

theorem isDomain (Dw : Datum H) (K : Type) [Field K] : IsDomain (ArcS Dw K) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))

theorem arcι_C_injective (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective ((arcι Dw K).comp (PowerSeries.C (R := K))) :=
  have := isDomain Dw K
  RingHom.injective _

theorem exists_const (Dw : Datum H) (K : Type) [Field K] [CharZero K] (s : ArcS Dw K) (hs : AlgZ s) :
    ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x) := by
  have : CharZero (LaurentSeries K) := (HahnSeries.C : K →+* LaurentSeries K).charZero_iff (RingHom.injective _) |>.1 ‹_›
  have : IsIntegrallyClosed (MvPolynomial (ArcLt Dw) (LaurentSeries K)) := inferInstance
  obtain ⟨P, hP, hPa⟩ := exists_of_localization (K := LaurentSeries K) (R := MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (S := ArcS Dw K) (Submonoid.powers (arcDet Dw K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K)) MvPolynomial.C hs
  obtain ⟨y, rfl, hy⟩ := mvPolynomial_const hPa
  obtain ⟨p, hp, hpa⟩ := exists_of_localization (K := K) (R := PowerSeries K) (nonZeroDivisors _) le_rfl
    (PowerSeries.C (R := K)) hy
  obtain ⟨x, rfl⟩ := powerSeries_const hpa
  refine ⟨x, ?_⟩
  rw [← hP, ← hp]
  rfl

theorem algebraic_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] [CharZero K], IsDomain (ArcS Dw K) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) ∧ (∀ s : ArcS Dw K, IsAlgebraic ℤ s → ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x)) ∧ ∀ (F : Type) [Field F] [NumberField F] (f : F →+* ArcS Dw K), ∃ f₀ : F →+* K, f = ((arcι Dw K).comp (PowerSeries.C (R := K))).comp f₀ := by
  intro E _ _ _ H Dw K _ _
  refine ⟨isDomain Dw K, algebraMap_injective Dw K, fun s hs => exists_const Dw K s (algZ_of hs), fun F _ _ f => ?_⟩
  have hinj := arcι_C_injective Dw K
  have hex : ∀ a : F, ∃ x : K, ((arcι Dw K).comp (PowerSeries.C (R := K))) x = f a := fun a => by
    have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨x, hx⟩ := exists_const Dw K (f a) ((algZ_of ha).map f)
    exact ⟨x, hx.symm⟩
  choose g hg using hex
  refine ⟨{ toFun := g, map_one' := hinj ?_, map_mul' := fun a b => hinj ?_, map_zero' := hinj ?_,
            map_add' := fun a b => hinj ?_ }, RingHom.ext fun a => (hg a).symm⟩
  · rw [hg, map_one, map_one]
  · rw [hg, map_mul, map_mul, hg, hg]
  · rw [hg, map_zero, map_zero]
  · rw [hg, map_add, map_add, hg, hg]

end GlobalTheory.ArcConst
