import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateQuotient
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.RegularLocalRing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

namespace FunctorialResolution.EmbeddedResolution

private theorem algebraMap_coordPolynomialRing_injective_of_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (algebraMap (CoordPolynomialRing k m) S) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro a ha
  by_contra h
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S)
    (mem_nonZeroDivisors_of_ne_zero h)
  have h1 : (1 : S) = 0 := by
    apply hreg
    show a • (1 : S) = a • (0 : S)
    rw [smul_zero, Algebra.smul_def, ha, zero_mul]
  exact one_ne_zero h1

private theorem isRadical_span_singleton_of_isRadical_map_atPrime {S : Type u} [CommRing S] (a : S)
    (h : ∀ (Q : Ideal S) [Q.IsPrime],
      (Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S))).IsRadical) :
    (Ideal.span ({a} : Set S)).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  by_contra hxI
  obtain ⟨K, hKmem⟩ : ∃ K : Ideal S, ∀ b : S, b ∈ K ↔ b * x ∈ Ideal.span ({a} : Set S) :=
    ⟨{ carrier := {s : S | s * x ∈ Ideal.span ({a} : Set S)}
       zero_mem' := by
         show (0 : S) * x ∈ Ideal.span ({a} : Set S)
         rw [zero_mul]
         exact Ideal.zero_mem _
       add_mem' := by
         intro b c hb hc
         show (b + c) * x ∈ Ideal.span ({a} : Set S)
         rw [add_mul]
         exact Ideal.add_mem _ hb hc
       smul_mem' := by
         intro c b hb
         show (c • b) * x ∈ Ideal.span ({a} : Set S)
         rw [smul_eq_mul, mul_assoc]
         exact Ideal.mul_mem_left _ c hb },
     fun b => Iff.rfl⟩
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ K := by rw [htop]; exact Submodule.mem_top
    have h2 := (hKmem 1).mp h1
    rw [one_mul] at h2
    exact hxI h2
  obtain ⟨Q, hQmax, hKQ⟩ := Ideal.exists_le_maximal K hKne
  have hQp : Q.IsPrime := hQmax.isPrime
  have hrad := h Q
  have hpow : (algebraMap S (Localization.AtPrime Q) x) ^ n ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  have hxmem : algebraMap S (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) :=
    hrad (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  rw [Ideal.map_span, Set.image_singleton] at hxmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxmem
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj (M := Q.primeCompl) c
  have key : algebraMap S (Localization.AtPrime Q) (x * (s : S)) =
      algebraMap S (Localization.AtPrime Q) (a * y) := by
    have h1 : algebraMap S (Localization.AtPrime Q) (x * (s : S))
        = (c * algebraMap S (Localization.AtPrime Q) (s : S)) *
            algebraMap S (Localization.AtPrime Q) a := by
      rw [map_mul, ← hc]; ring
    rw [h1, hys, map_mul]; ring
  obtain ⟨dd, hd⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  have hmem0 : ((dd : S) * (s : S)) * x ∈ Ideal.span ({a} : Set S) := by
    have heq : ((dd : S) * (s : S)) * x = (dd : S) * (x * (s : S)) := by ring
    rw [heq, hd]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self a))
  have hmem : ((dd : S) * (s : S)) ∈ K := (hKmem _).mpr hmem0
  have hQmem : ((dd : S) * (s : S)) ∈ Q := hKQ hmem
  rcases hQp.mem_or_mem hQmem with hcase | hcase
  · exact dd.2 hcase
  · exact s.2 hcase

theorem etaleChartCoord_injective (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (etaleChartCoord k m S) := by
  have hinj := algebraMap_coordPolynomialRing_injective_of_etale k m S
  intro i j hij
  have h : (MvPolynomial.X (ULift.up i) : CoordPolynomialRing k m)
      = MvPolynomial.X (ULift.up j) := by
    apply hinj
    rw [← etaleChartCoord_def, ← etaleChartCoord_def]
    exact hij
  exact congrArg ULift.down (MvPolynomial.X_injective h)

theorem linearIndependent_toCotangent_etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (IsLocalRing.maximalIdeal A).toCotangent
            ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → IsLocalRing.CotangentSpace A) := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exfalso
      have := hs
      have h10 : (1 : S) = (0 : S) := Subsingleton.elim _ _
      have hA : (1 : A) = 0 := by
        calc (1 : A) = algebraMap S A 1 := (map_one _).symm
          _ = algebraMap S A 0 := by rw [h10]
          _ = 0 := map_zero _
      exact one_ne_zero hA
    · exact hs
  obtain ⟨d, w, hwq, hwJ, hspan, hdim⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m S q A J hJ
  have hwm : ∀ i, algebraMap S A (w i) ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin d → IsLocalRing.CotangentSpace A,
      ∀ i, y i = (IsLocalRing.maximalIdeal A).toCotangent ⟨algebraMap S A (w i), hwm i⟩ :=
    ⟨_, fun i => rfl⟩
  have key : ∀ (b : A), b ∈ Ideal.span (Set.range fun i => algebraMap S A (w i)) →
      ∀ (hb : b ∈ IsLocalRing.maximalIdeal A),
        (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈
          Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro b hb0
    have hb' : b ∈ Submodule.span A (Set.range fun i => algebraMap S A (w i)) := hb0
    clear hb0
    induction hb' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, by rw [hy i]⟩
    | zero =>
        intro hz'
        have h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hzm' : z' ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz'
        have hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add]
        exact Submodule.add_mem _ (ihz hzm) (ihz' hzm')
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]
        exact Submodule.smul_mem _ _ (ih hzm)
  have hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard0 : ((d : ℕ) : WithBot ℕ∞) =
      ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) :
        WithBot ℕ∞) :=
    hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm
  have hcard : Fintype.card (Fin d) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast hcard0
  have hliY : LinearIndependent (IsLocalRing.ResidueField A) y :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard
  have hchoice : ∀ j : { x : Fin m // x ∈ J },
      ∃ i : Fin d, w i = etaleChartCoord k m S (j : Fin m) := fun j => hwJ (j : Fin m) j.2
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro j₁ j₂ hjj
    have h1 : etaleChartCoord k m S (j₁ : Fin m) = etaleChartCoord k m S (j₂ : Fin m) := by
      rw [← hf j₁, ← hf j₂, hjj]
    exact Subtype.ext (etaleChartCoord_injective k m S h1)
  have hcomp := hliY.comp f hfinj
  have heq : y ∘ f = fun j : { x : Fin m // x ∈ J } =>
      (IsLocalRing.maximalIdeal A).toCotangent
        ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ := by
    funext j
    have h1 : (⟨algebraMap S A (w (f j)), hwm (f j)⟩ : IsLocalRing.maximalIdeal A)
        = ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :=
      Subtype.ext (congrArg (algebraMap S A) (hf j))
    show y (f j) = _
    rw [hy (f j)]
    exact congrArg _ h1
  rw [← heq]
  exact hcomp

theorem isRadical_span_singleton_prod_algebraMap_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsRadical := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A := by
    intro j hj
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q
      (etaleChartCoord k m S j)).mpr (hJ j hj)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A J hJ hJA
  have hmain := _root_.IsRegularLocalRing.isRadical_span_singleton_prod
    (fun j : { x : Fin m // x ∈ J } => algebraMap S A (etaleChartCoord k m S (j : Fin m)))
    (fun j => hJA (j : Fin m) j.2) hli
  rw [← Finset.prod_coe_sort J (fun j => algebraMap S A (etaleChartCoord k m S j))]
  exact hmain

theorem isRadical_map_span_singleton_prod_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (T : Finset (Fin m)) :
    (Ideal.map (algebraMap S A)
      (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S))).IsRadical := by
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Fin m),
      J = T.filter (fun j => etaleChartCoord k m S j ∈ q) := ⟨_, rfl⟩
  have hJsub : J ⊆ T := by rw [hJdef]; exact Finset.filter_subset _ _
  have hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q := by
    intro j hj
    rw [hJdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hunit : IsUnit (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) := by
    refine Finset.prod_induction _ _ (fun u v hu hv => hu.mul hv) isUnit_one ?_
    intro j hj
    have h1 := Finset.mem_sdiff.mp hj
    have hj' : etaleChartCoord k m S j ∉ q := by
      intro hmem
      exact h1.2 (by rw [hJdef]; exact Finset.mem_filter.mpr ⟨h1.1, hmem⟩)
    exact IsLocalization.map_units A (⟨etaleChartCoord k m S j, hj'⟩ : q.primeCompl)
  have hsplit : ∏ j ∈ T, algebraMap S A (etaleChartCoord k m S j)
      = (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) *
        ∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j) := by
    rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hJsub]
  rw [Ideal.map_span, Set.image_singleton, map_prod, hsplit,
    Ideal.span_singleton_mul_left_unit hunit _]
  exact isRadical_span_singleton_prod_algebraMap_etaleChartCoord k m S q A J hJ

theorem isRadical_span_singleton_prod_etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (T : Finset (Fin m)) :
    (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S)).IsRadical := by
  refine isRadical_span_singleton_of_isRadical_map_atPrime (∏ j ∈ T, etaleChartCoord k m S j) ?_
  intro Q hQ
  have : Q.IsPrime := hQ
  exact isRadical_map_span_singleton_prod_etaleChartCoord k m S Q (Localization.AtPrime Q) T

end FunctorialResolution.EmbeddedResolution
