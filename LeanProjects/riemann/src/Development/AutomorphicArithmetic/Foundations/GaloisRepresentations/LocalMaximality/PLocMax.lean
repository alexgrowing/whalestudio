import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma red_art {R : Type} [CommRing R] [IsArtinianRing R] [IsReduced R] (y : R) :
    ∃ z, y * (1 - y * z) = 0 := by
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd y (1 : R)
  simp only [smul_eq_mul, mul_one] at hw
  refine ⟨w, IsReduced.eq_zero _ ⟨n + 1, ?_⟩⟩
  have h : y ^ n * (1 - y * w) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hw, sub_self]
  rw [mul_pow, pow_succ, pow_succ]
  calc y ^ n * y * ((1 - y * w) ^ n * (1 - y * w))
      = y * (1 - y * w) ^ n * (y ^ n * (1 - y * w)) := by ac_rfl
    _ = 0 := by rw [h, mul_zero]

private theorem exists_const_sub_mem_span_tco_of_mem_rA {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (f : F) (hf : f ∈ rA ℂ (xv x) {0}) :
    ∃ c : ℂ, ∃ hb : algebraMap F L f ∈ rB ℂ L (xv x) {0},
      (⟨_, hb⟩ : rB ℂ L (xv x) {0}) - algebraMap ℂ _ c ∈ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
  have memB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F L g ∈ rB ℂ L (xv x) {0} := by
    intro g hg
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := (⟨g, hg⟩ : rA ℂ (xv x) {0}))
  unfold rA at hf
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine ⟨1, memB _ (Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, 0, rfl⟩), ?_⟩
      convert Ideal.zero_mem _
      rw [sub_eq_zero]
      apply Subtype.ext
      simp
    · refine ⟨0, tco_mem ℂ L (xv x) k, ?_⟩
      rw [map_zero, sub_zero]
      exact Ideal.subset_span ⟨k, rfl⟩
  | algebraMap c0 =>
    refine ⟨c0, memB _ (Subalgebra.algebraMap_mem _ c0), ?_⟩
    convert Ideal.zero_mem _
    rw [sub_eq_zero]
    apply Subtype.ext
    simp [IsScalarTower.algebraMap_apply ℂ F L]
  | add f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c + c', by rw [map_add]; exact Subalgebra.add_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ h h' using 1
    apply Subtype.ext
    simp only [map_add, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_algebraMap]
    ring
  | mul f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c * c', by rw [map_mul]; exact Subalgebra.mul_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ (Ideal.mul_mem_right (⟨_, hb'⟩ : rB ℂ L (xv x) {0}) _ h)
      (Ideal.mul_mem_left _ (algebraMap ℂ (rB ℂ L (xv x) {0}) c) h') using 1
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap]
    ring

private lemma fin_quot {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ L (xv x)) :
    Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := by
  classical
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F L d (xv x) hc {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun z => Ideal.Quotient.mk _ (⟨z.1, z.2⟩ : rB ℂ L (xv x) {0})), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) ∈
      Submodule.span (rA ℂ (xv x) {0}) (s : Set (integralClosure (rA ℂ (xv x) {0}) L)) := by
    rw [hs]
    trivial
  change Ideal.Quotient.mk _ (⟨(⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).1,
    (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).2⟩ : rB ℂ L (xv x) {0}) ∈ _
  generalize (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) = z at hy ⊢
  induction hy using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  | zero =>
    convert Submodule.zero_mem _ using 1
    exact map_zero (Ideal.Quotient.mk _)
  | add u w _ _ hu hw =>
    convert Submodule.add_mem _ hu hw using 1
    exact map_add (Ideal.Quotient.mk _) _ _
  | smul r u _ hu =>
    obtain ⟨c, hb, hc'⟩ := exists_const_sub_mem_span_tco_of_mem_rA (L := L) d x r.1 r.2
    have e : (⟨((r • u : integralClosure (rA ℂ (xv x) {0}) L) : L), (r • u).2⟩ : rB ℂ L (xv x) {0}) =
        ⟨_, hb⟩ * ⟨u.1, u.2⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
      exact Or.inl rfl
    rw [e, map_mul, Ideal.Quotient.eq.mpr hc', Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hu

theorem UpperTheory.Gal.productCup_of_system.locMax_of :
    ValBasic → LocMax := by
  intro _ F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨b, hb, hbv, heb, hev⟩ := hv
  rw [mul_zero] at hev
  haveI : Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := fin_quot d x hc
  haveI : IsArtinianRing ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := IsArtinianRing.of_finite ℂ _
  haveI : IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := hred
  obtain ⟨zq, hz⟩ := red_art (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))) ⟨b * v, hbv⟩)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hmem : (⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) ∈
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, map_mul]
    exact hz
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have he1 : e.1 (1 - ⟨b * v, hbv⟩ * z) = 1 := by
    rw [map_sub, map_one, map_mul]
    change 1 - e.1 ⟨b * v, hbv⟩ * e.1 z = 1
    rw [hev, zero_mul, sub_zero]
  have hes : e.1 (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z)) ≠ 0 := by
    rw [map_mul, he1, mul_one]
    exact heb
  have hs0 : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) ≠ 0 := by
    intro h
    apply hes
    rw [show (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) = 0 from Subtype.ext h, map_zero]
  have key : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v =
      ∑ l, (c l : L) * tt L x l := by
    have h1 : (((⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) =
        ∑ l, (c l : L) * tt L x l := by
      rw [← hcsum]
      simp [tt]
    rw [← h1]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    ring
  refine ⟨fun l => (c l : L) * ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹,
    fun l => ⟨⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z), hes, ?_⟩, ?_⟩
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact (c l).2
  · calc v = ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹ *
          (((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [key, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
