import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsIdealTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace IdealTwistFamily

section Forms

variable {R : Type u} [CommRing R] {N : ℕ}

theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _

theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩

theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]

theorem exists_finset_forms [IsNoetherianRing R] (J : Ideal (Poly R N))
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) :
    ∃ H : Finset (Poly R N), (↑H : Set (Poly R N)) ⊆ J ∧ Ideal.span (↑H : Set (Poly R N)) = J ∧
      ∀ g ∈ (↑H : Set (Poly R N)), g.IsHomogeneous g.totalDegree := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian J : J.FG)
  have hsub : (↑(G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g) : Set (Poly R N)) ⊆ J := by
    intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, hg, i, -, rfl⟩ := hh
    exact hJ g (hG ▸ Ideal.subset_span hg) i
  refine ⟨G.biUnion fun g => (Finset.range (g.totalDegree + 1)).image
      fun i => homogeneousComponent i g, hsub, le_antisymm (Ideal.span_le.mpr hsub) ?_, ?_⟩
  · rw [← hG]
    refine Submodule.span_le.mpr fun g hg => ?_
    have hsum := sum_homogeneousComponent g
    rw [SetLike.mem_coe, ← hsum]
    refine Ideal.sum_mem _ fun i hi => Ideal.subset_span ?_
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
    exact ⟨g, hg, i, hi, rfl⟩
  · intro h hh
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image,
      Finset.mem_coe] at hh
    obtain ⟨g, -, i, -, rfl⟩ := hh
    exact isHomogeneous_totalDegree (homogeneousComponent_isHomogeneous i g)

end Forms

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span (chartRing S x I) {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

theorem exists_unit_mul_mem_of_span {I J : Chart x} (h : I.1 ⊆ J.1)
    (M : Submodule (chartRing S x I) Ω) {G : Set Ω}
    (hG : ∀ g ∈ G, ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * g ∈ M)
    {y : Ω} (hy : y ∈ Submodule.span (chartRing S x J) G) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨1, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (y + z) = b • ((a : Ω) * y) + a • ((b : Ω) * z) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.add_mem (M.smul_mem b hay) (M.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbc⟩ := exists_isUnit_mul_mem h c
    refine ⟨b * a, by rw [map_mul]; exact hb.mul ha, ?_⟩
    have : ((b * a : chartRing S x I) : Ω) * (c • y) =
        (⟨_, hbc⟩ : chartRing S x I) • ((a : Ω) * y) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.smul_mem _ hay

theorem idealMod_loc {I J : Chart x} (h : I.1 ⊆ J.1) (J' : Ideal (Poly S N)) {y : Ω}
    (hy : y ∈ idealMod J' J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ idealMod J' I := by
  refine exists_unit_mul_mem_of_span h _ ?_ hy
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
    field_simp
  · change aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) ∈ idealMod J' I
    rw [show aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) =
      aeval x f / aeval x (X i ^ e) by field_simp]
    exact Submodule.subset_span ⟨f, X i ^ e, e, hf, pow_mem (X_mem_monos hi) e, hfe,
      isHomogeneous_X_pow i e, rfl⟩

theorem idealMod_fg [IsNoetherianRing S] (J' : Ideal (Poly S N))
    (hJ' : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') (I : Chart x) :
    (idealMod J' I).FG := by
  classical
  obtain ⟨H, hHJ, hspan, hH⟩ := exists_finset_forms J' hJ'
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have heq : idealMod J' I = Submodule.span (chartRing S x I)
      ((fun g : Poly S N => aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) ''
        (↑H : Set (Poly S N))) := by
    apply le_antisymm
    · rw [idealMod, Submodule.span_le]
      rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      have hs0 := eval_ne_zero_of_mem_monos I hs
      rw [← hspan] at hf
      have hmem := mem_span_forms_of_mem_ideal totalDegree hH hf hfe
      refine Submodule.span_induction (p := fun p _ => aeval x p / aeval x s ∈
        Submodule.span (chartRing S x I) ((fun g : Poly S N =>
          aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) '' (↑H : Set (Poly S N))))
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨g, hg, h', d', hh', hd, rfl⟩
        have hX : aeval x (X i ^ g.totalDegree : Poly S N) ≠ 0 := by
          rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
        let c : chartRing S x I := ⟨aeval x (h' * X i ^ g.totalDegree) / aeval x s,
          h' * X i ^ g.totalDegree, s, e, hs, hd ▸ hh'.mul (isHomogeneous_X_pow i _), hse, rfl⟩
        have hc : aeval x (h' * g) / aeval x s =
            c • (aeval x g / aeval x (X i ^ g.totalDegree : Poly S N)) := by
          rw [chartRing_smul_def]
          change _ = aeval x (h' * X i ^ g.totalDegree) / aeval x s * _
          rw [map_mul, map_mul]
          field_simp
        rw [hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
      · simp
      · intro p q _ _ hp hq
        rw [map_add, add_div]
        exact Submodule.add_mem _ hp hq
      · intro r p _ hp
        rw [map_smul, smul_div_assoc]
        exact Submodule.smul_of_tower_mem _ r hp
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, X i ^ g.totalDegree, g.totalDegree, hHJ hg,
        pow_mem (X_mem_monos hi) _, hH g hg, isHomogeneous_X_pow i _, rfl⟩
  rw [heq]
  exact Submodule.fg_span (H.finite_toSet.image _)

theorem twist_mem_iff (Q : LineBundle S x) (J' : Ideal (Poly S N)) (I J : Chart x)
    (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ (Q.twist (idealSys x J')).sub J ↔ ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (Q.twist (idealSys x J')).sub I := by
  constructor
  · intro hy
    refine exists_unit_mul_mem_of_span (G := {z | ∃ q ∈ (idealSys x J').sub J, ∃ y ∈ Q.sub J,
      z = q • y}) h ((Q.twist (idealSys x J')).sub I) ?_ hy
    rintro _ ⟨q, hq, z, hz, rfl⟩
    obtain ⟨a, ha, haq⟩ := idealMod_loc h J' hq
    obtain ⟨b, hb, hbz⟩ := (Q.mem_iff I J h z).mp hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (q • z) = ((a : Ω) * q) • ((b : Ω) • z) := by
      simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
    rw [this]
    exact Submodule.subset_span ⟨_, haq, _, hbz, rfl⟩
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (Q.twist (idealSys x J')).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

end Chart

theorem proof : IdealTwistFamily.Statement := by
  intro S _ _ Ω _ _ N x Q J' hJ'
  refine ⟨{ Q.twist (idealSys x J') with mem_iff := twist_mem_iff Q J' }, rfl, fun I => ?_⟩
  change ((Q.twist (idealSys x J')).sub I).FG
  rw [twist_sub_eq_mul]
  exact (idealMod_fg J' hJ' I).mul (Q.fg I)

end IdealTwistFamily

end

end GroundTheory.Heights₂.Heights.Kleiman
