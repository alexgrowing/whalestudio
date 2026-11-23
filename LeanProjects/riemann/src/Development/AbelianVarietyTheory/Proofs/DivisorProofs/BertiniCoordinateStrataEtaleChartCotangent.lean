import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoordinateStratumEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVaniStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.StrataBertini

theorem isLocalization_atPrime_quotient {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p] (I : Ideal A) (hI : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization.AtPrime (S ⧸ I.map (algebraMap A S)) (p.map (Ideal.Quotient.mk I)) := by
  constructor
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∉ p := fun h => hx (Ideal.mem_map_of_mem _ h)
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units S (⟨a, ha⟩ : p.primeCompl)).map _
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I s, ?_⟩⟩, ?_⟩
    · exact fun hs => s.2 ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [← map_mul, h]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, ← map_sub] at hxy
    rw [IsLocalization.mem_map_algebraMap_iff p.primeCompl S] at hxy
    obtain ⟨⟨⟨i, hi⟩, m⟩, hm⟩ := hxy
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl S] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨⟨Ideal.Quotient.mk I (c * m), ?_⟩, ?_⟩
    · exact fun hs => (p.primeCompl.mul_mem c.2 m.2) ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · show Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I a = Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I b
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : (↑c * ↑m * (a - b) : A) = ↑c * i := by linear_combination hc
      rw [this]
      exact I.mul_mem_left _ hi

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem linearIndependent_option_cotangent {S : Type*} [CommRing S] [IsLocalRing S] {J : Type*}
    [Fintype J] (w : Option J → S) (hw : ∀ j, w j ∈ maximalIdeal S)
    (hind : LinearIndependent (ResidueField S)
      (fun j : J => ((maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ : CotangentSpace S)))
    (hnot : w none ∉ maximalIdeal S ^ 2 ⊔ Ideal.span (Set.range (fun j : J => w (some j)))) :
    LinearIndependent (ResidueField S)
      (fun j : Option J => ((maximalIdeal S).toCotangent ⟨w j, hw j⟩ : CotangentSpace S)) := by
  rw [linearIndependent_option]
  refine ⟨hind, fun hmem => hnot ?_⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  choose b hb using fun j => IsLocalRing.residue_surjective (c j)
  have hc' : ∑ j, b j • (maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ =
      (maximalIdeal S).toCotangent ⟨w none, hw none⟩ := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, ← hb j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have h0 : (maximalIdeal S).toCotangent
      (⟨w none, hw none⟩ - ∑ j, b j • ⟨w (some j), hw (some j)⟩) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hc', sub_self]
  rw [Ideal.toCotangent_eq_zero] at h0
  have h1 : w none = (w none - ∑ j, b j * w (some j)) + ∑ j, b j * w (some j) := by ring
  rw [h1]
  refine Submodule.add_mem_sup ?_ ?_
  · simpa using h0
  · exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem key (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (U : Y.Opens) (z : Fin n → Γ(Y, U)) (hfr : IsFrame (dOn q z))
    (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)) (J : Finset (Fin n)) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) →
      (∀ j : J, Y.presheaf.germ U y hy (z j) ∈ maximalIdeal (Y.presheaf.stalk y)) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∈ maximalIdeal (Y.presheaf.stalk y) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∉
        maximalIdeal (Y.presheaf.stalk y) ^ 2 ⊔
          Ideal.span (Set.range (fun j : J => Y.presheaf.germ U y hy (z j))) := by
  have hU : IsAffineOpen U := hfr.affine
  set I : Ideal Γ(Y, U) := Ideal.span (z '' (J : Set (Fin n))) with hIdef
  letI : Algebra ℂ (Γ(Y, U) ⧸ I) := ((Ideal.Quotient.mk I).comp (algX q U)).toAlgebra
  haveI : Algebra.Smooth ℂ (Γ(Y, U) ⧸ I) := GlobalTheory.T.smooth_coordinateStratum_etaleChart Y q n U z hfr J
  obtain ⟨Q1, hQ1, hQ1u⟩ :=
    GlobalTheory.bertini_cotangent_independent ℂ (Γ(Y, U) ⧸ I) (fun i => Ideal.Quotient.mk I (f i)) 1
  have hinj : Function.Injective (Prod.snd : Fin 1 × ι → ι) :=
    fun a b h => Prod.ext (Subsingleton.elim _ _) h
  refine ⟨MvPolynomial.rename Prod.snd Q1, fun h0 => hQ1 (MvPolynomial.rename_injective _ hinj
    (by rw [h0, map_zero])), ?_⟩
  intro u hu y hy hf hz ht
  have hu' : MvPolynomial.eval (u ∘ Prod.snd) Q1 ≠ 0 := by rwa [MvPolynomial.eval_rename] at hu
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  set p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal with hpdef
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hy⟩
  have hgerm : ∀ a, algebraMap Γ(Y, U) (Y.presheaf.stalk y) a = Y.presheaf.germ U y hy a :=
    fun a => rfl
  have hpm : ∀ a, a ∈ p ↔ Y.presheaf.germ U y hy a ∈ maximalIdeal (Y.presheaf.stalk y) := by
    intro a
    rw [← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y) p, ← hgerm]
    rfl
  have hIp : I ≤ p := Ideal.span_le.2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (hpm _).2 (hz ⟨j, hj⟩))
  haveI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  set IS := I.map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) with hISdef
  have hISm : IS ≤ maximalIdeal (Y.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (fun a ha => (hpm a).1 (hIp ha))
  haveI : Nontrivial (Y.presheaf.stalk y ⧸ IS) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hISm)
  haveI : IsLocalRing (Y.presheaf.stalk y ⧸ IS) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y ⧸ IS) (p.map (Ideal.Quotient.mk I)) :=
    isLocalization_atPrime_quotient p I hIp
  have hmk : ∀ a ∈ maximalIdeal (Y.presheaf.stalk y),
      Ideal.Quotient.mk IS a ∈ maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hun
    obtain ⟨c, hc⟩ := hun.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_one (Ideal.Quotient.mk IS), Ideal.Quotient.eq] at hc
    have h1 : a * c' ∈ maximalIdeal (Y.presheaf.stalk y) := Ideal.mul_mem_right _ _ ha
    have h2 := Ideal.sub_mem _ h1 (hISm hc)
    rw [sub_sub_cancel] at h2
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have hfi : ∃ i, Ideal.Quotient.mk I (f i) ∉ p.map (Ideal.Quotient.mk I) := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨i, ?_⟩
    rw [Ideal.mem_quotient_iff_mem hIp, hpm]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) ((Y.mem_basicOpen _ _ hy).1 hi)
  have htR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) =
      Ideal.Quotient.mk IS (Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i)) := by
    rw [← hgerm, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul, map_mul]
    rfl
  have hli := hQ1u (u ∘ Prod.snd) hu' (p.map (Ideal.Quotient.mk I)) (Y.presheaf.stalk y ⧸ IS) hfi
  have hmemR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈
      maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    rw [htR]; exact hmk _ ht
  have hne := hli.ne_zero ⟨0, hmemR⟩
  rw [Ne, Ideal.toCotangent_eq_zero] at hne
  intro hmem2
  apply hne
  show algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈ _
  rw [htR]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem2
  have hbI : b ∈ IS := by
    refine (Ideal.span_le.2 ?_) hb
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) (Ideal.subset_span ⟨j, j.2, rfl⟩)
  rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hbI, add_zero]
  have hma : Ideal.Quotient.mk IS a ∈ (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk IS) ^ 2 := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmk) 2 hma

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

theorem bertini_strata_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hfr ι _ f
  choose Q hQ0 hQ using fun J : Finset (Fin n) => key Y q n U z hfr ι f J
  refine ⟨∏ J, Q J, Finset.prod_ne_zero_iff.2 fun J _ => hQ0 J, fun u hu y hy hf J h => ?_⟩
  rw [map_prod] at hu
  have huJ := Finset.prod_ne_zero_iff.1 hu J (Finset.mem_univ _)
  exact linearIndependent_option_cotangent
    (fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) h
    (GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hfr y hy J (fun j => h (some j)))
    (hQ J u huJ y hy hf (fun j => h (some j)) (h none))

end GlobalTheory.StrataBertini
