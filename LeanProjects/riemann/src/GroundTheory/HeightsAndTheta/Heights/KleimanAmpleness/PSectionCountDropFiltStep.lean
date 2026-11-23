import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt.Step

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_frac_of_mem_idealMod {J : Ideal (Poly S N)} {I : Chart x} {z : Ω}
    (hz : z ∈ idealMod J I) : ∃ (h t : Poly S N) (d : ℕ), h ∈ J ∧ t ∈ monos I.1 ∧
      h.IsHomogeneous d ∧ t.IsHomogeneous d ∧ z = aeval x h / aeval x t := by
  refine Submodule.span_induction (p := fun z _ ↦ ∃ (h t : Poly S N) (d : ℕ), h ∈ J ∧
      t ∈ monos I.1 ∧ h.IsHomogeneous d ∧ t.IsHomogeneous d ∧ z = aeval x h / aeval x t)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  · exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  · rintro _ _ _ _ ⟨h, t, d, hh, ht, hhd, htd, rfl⟩ ⟨h', t', d', hh', ht', hhd', htd', rfl⟩
    refine ⟨h * t' + t * h', t * t', d + d', J.add_mem (J.mul_mem_right _ hh) (J.mul_mem_left _ hh'),
      mul_mem ht ht', (hhd.mul htd').add (htd.mul hhd'), htd.mul htd', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I ht) (eval_ne_zero_of_mem_monos I ht')]
    simp only [map_add, map_mul]
  · rintro a _ _ ⟨h, t, d, hh, ht, hhd, htd, rfl⟩
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
    refine ⟨f * h, s * t, e + d, J.mul_mem_left _ hh, mul_mem hs ht, hf.mul hhd, hse.mul htd, ?_⟩
    rw [chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]

theorem idealMod_sup_span_le {J₁ : Ideal (Poly S N)}
    (hJ : ∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) {g : Poly S N} {e : ℕ}
    (hg : g.IsHomogeneous e) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (J₁ ⊔ Ideal.span {g}) I ≤
      idealMod J₁ I ⊔ Submodule.span (chartRing S x I) {aeval x g / x i ^ e} := by
  classical
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  obtain ⟨j, hj, cg, hcg, hjc⟩ := Submodule.mem_sup.mp hf
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hcg
  have hf' : f = homogeneousComponent d j + homogeneousComponent d (c * g) := by
    rw [← map_add, hjc, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hfd),
      if_pos rfl]
  rw [SetLike.mem_coe, hf', map_add, add_div]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨_, s, d, hJ j hj d, hs,
    homogeneousComponent_isHomogeneous d j, hsd, rfl⟩) ?_
  rw [show c * g = ∑ k ∈ Finset.range (c.totalDegree + 1), homogeneousComponent k c * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum, map_sum, Finset.sum_div]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
    ((homogeneousComponent_isHomogeneous k c).mul hg))]
  split_ifs with hk
  · have hdeg : (homogeneousComponent k c * X i ^ e : Poly S N).IsHomogeneous d := by
      rw [hk]; exact (homogeneousComponent_isHomogeneous k c).mul (isHomogeneous_X_pow i e)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, _, s, d, hs, hdeg, hsd, rfl⟩, ?_⟩
    rw [chartRing_smul_def]
    simp only [map_mul, map_pow, aeval_X]
    field_simp
  · rw [map_zero, zero_div]; exact Submodule.zero_mem _

theorem mem_idealMod_of_mul_mem {J₁ pp : Ideal (Poly S N)} (hJ : primeOf (S := S) x ≤ J₁)
    {g : Poly S N} {e : ℕ} (hpp : ∀ f, f ∈ pp ↔ f * g ∈ J₁) (hg : g.IsHomogeneous e)
    {I : Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) (a : chartRing S x I)
    (ha : (a : Ω) * (aeval x g / x i ^ e) ∈ idealMod J₁ I) : (a : Ω) ∈ idealMod pp I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  obtain ⟨f, s, d, hs, hf, hsd, haf⟩ := a.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  rw [haf] at ha ⊢
  obtain ⟨h, t, d', hh, ht, hhd, htd, heq⟩ := exists_frac_of_mem_idealMod ha
  have ht0 := eval_ne_zero_of_mem_monos I ht
  have hP : f * g * t - h * s * X i ^ e ∈ primeOf (S := S) x := by
    have h2 : (h * s * X i ^ e : Poly S N).IsHomogeneous (d + e + d') := by
      have := (hhd.mul hsd).mul (isHomogeneous_X_pow (R := S) i e)
      rwa [show d' + d + e = d + e + d' by ring] at this
    refine (mem_primeOf_of_isHomogeneous x (((hf.mul hg).mul htd).sub h2)).mpr ?_
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hs0 (pow_ne_zero _ hxi)) ht0] at heq
    simp only [map_sub, map_mul, map_pow, aeval_X]
    linear_combination heq
  have hfg : f * t * g ∈ J₁ := by
    have h1 : h * s * X i ^ e ∈ J₁ := J₁.mul_mem_right _ (J₁.mul_mem_right _ hh)
    have := J₁.add_mem (hJ hP) h1
    rwa [sub_add_cancel, mul_right_comm] at this
  refine Submodule.subset_span ⟨f * t, s * t, d + d', (hpp _).mpr hfg, mul_mem hs ht,
    hf.mul htd, hsd.mul htd, ?_⟩
  rw [map_mul, map_mul, mul_div_mul_right _ _ ht0]

theorem mul_mem_idealMod_of_mem {J₁ pp : Ideal (Poly S N)} {g : Poly S N} {e : ℕ}
    (hpp : ∀ f, f ∈ pp ↔ f * g ∈ J₁) (hg : g.IsHomogeneous e) {I : Chart x} {i : Fin (N + 1)}
    (hi : i ∈ I.1) {b : Ω} (hb : b ∈ idealMod pp I) :
    aeval x g / x i ^ e * b ∈ idealMod J₁ I := by
  obtain ⟨h, t, d, hh, ht, hhd, htd, rfl⟩ := exists_frac_of_mem_idealMod hb
  refine Submodule.subset_span ⟨h * g, t * X i ^ e, d + e, (hpp h).mp hh,
    mul_mem ht (pow_mem (X_mem_monos hi) e), hhd.mul hg, htd.mul (isHomogeneous_X_pow i e), ?_⟩
  simp only [map_mul, map_pow, aeval_X]
  ring

section CechZero

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R] {G : Cell U → Type*}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

def toH0 : LinearMap.ker (Cech.d G ρ 0) →ₗ[R] Cech.H G ρ 0 := Submodule.mkQ _

theorem eq_zero_of_toH0_eq_zero_degree_zero (c : LinearMap.ker (Cech.d G ρ 0)) (h : toH0 c = 0) :
    (c : Cech.Cochain G 0) = 0 := by
  have h1 := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at h1
  exact (Submodule.mem_bot R).mp h1

end CechZero

theorem mem_secs_iff' {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

theorem exists_chart {J₁ : Ideal (Poly S N)}
    (hJ : ∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) {g : Poly S N} {e : ℕ}
    (hg : g.IsHomogeneous e) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1)
    (Qi : Submodule (chartRing S x I) Ω) {s : Ω}
    (hs : s ∈ idealMod (J₁ ⊔ Ideal.span {g}) I * Qi) :
    ∃ y ∈ twistMod S x (-(e : ℤ)) I * Qi, s - aeval x g * y ∈ idealMod J₁ I * Qi := by
  have hs' : s ∈ (idealMod J₁ I ⊔ Submodule.span (chartRing S x I) {aeval x g / x i ^ e}) * Qi :=
    (Submodule.mul_le.mpr fun m hm n hn ↦
      Submodule.mul_mem_mul (idealMod_sup_span_le hJ hg I hi hm) hn) hs
  rw [Submodule.sup_mul] at hs'
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs'
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hb
  refine ⟨x i ^ (-(e : ℤ)) * q, ?_, ?_⟩
  · rw [twistMod_eq_span _ I hi]
    exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hq
  · have h : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
      rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [h, add_sub_cancel_right]
    exact ha

theorem mem_chart_of_mul_mem {J₁ pp : Ideal (Poly S N)} (hJ : primeOf (S := S) x ≤ J₁)
    {g : Poly S N} {e : ℕ} (hpp : ∀ f, f ∈ pp ↔ f * g ∈ J₁) (hg : g.IsHomogeneous e)
    (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (Qi Q' : Submodule (chartRing S x I) Ω)
    (hQ : Qi * Q' = 1) {y : Ω} (hy : y ∈ twistMod S x (-(e : ℤ)) I * Qi)
    (hgy : aeval x g * y ∈ idealMod J₁ I * Qi) :
    y ∈ idealMod pp I * (twistMod S x (-(e : ℤ)) I * Qi) := by
  rw [twistMod_eq_span _ I hi] at hy ⊢
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hy
  have hγ : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
    rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hγ] at hgy
  have hle : Submodule.span (chartRing S x I) {q} * Q' ≤ idealMod pp I := by
    refine Submodule.mul_le.mpr fun m hm n hn ↦ ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    have hqn : q * n ∈ (1 : Submodule (chartRing S x I) Ω) := hQ ▸ Submodule.mul_mem_mul hq hn
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hqn
    have ha' : (a : Ω) = q * n := ha
    have h1 := Submodule.mul_mem_mul hgy hn
    rw [mul_assoc (idealMod J₁ I), hQ, mul_one] at h1
    have h2 : (a : Ω) * (aeval x g / x i ^ e) ∈ idealMod J₁ I := by
      rw [ha']
      convert h1 using 1
      ring
    have h3 := mem_idealMod_of_mul_mem hJ hpp hg hi a h2
    rw [smul_mul_assoc, ← ha']
    exact Submodule.smul_mem _ c h3
  have hq1 : q ∈ idealMod pp I * Qi := by
    have h1 : q ∈ Submodule.span (chartRing S x I) {q} * (Qi * Q') := by
      rw [hQ, mul_one]; exact Submodule.mem_span_singleton_self q
    rw [mul_comm Qi Q', ← mul_assoc] at h1
    exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1
  rw [mul_left_comm]
  exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hq1

theorem mul_mem_chart {J₁ pp : Ideal (Poly S N)} {g : Poly S N} {e : ℕ}
    (hpp : ∀ f, f ∈ pp ↔ f * g ∈ J₁) (hg : g.IsHomogeneous e) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) (Qi : Submodule (chartRing S x I) Ω) {y : Ω}
    (hy : y ∈ idealMod pp I * (twistMod S x (-(e : ℤ)) I * Qi)) :
    aeval x g * y ∈ idealMod J₁ I * Qi := by
  rw [twistMod_eq_span _ I hi] at hy
  have h1 := Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (R := chartRing S x I) (aeval x g)) hy
  rw [mul_left_comm (idealMod pp I), ← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton,
    ← mul_assoc] at h1
  have hle : Submodule.span (chartRing S x I) {aeval x g * x i ^ (-(e : ℤ))} * idealMod pp I ≤
      idealMod J₁ I := by
    refine Submodule.mul_le.mpr fun m hm n hn ↦ ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [smul_mul_assoc, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    exact Submodule.smul_mem _ c (mul_mem_idealMod_of_mem hpp hg hi hn)
  exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1

theorem proof : Statement.{u, w} := by
  classical
  intro S _ Ω _ _ N x Q J₁ pp g e hJh hJ hg hpp
  set F₁ : SubSystem S x Ω := Q.twist (twistSys S x (-(e : ℤ))) with hF₁
  set F₂ : SubSystem S x Ω := F₁.twist (idealSys x pp) with hF₂
  set V := (Q.twist (idealSys x (J₁ ⊔ Ideal.span {g}))).secs with hV
  have hsub : ∀ (J : Ideal (Poly S N)) (I : Chart x),
      (Q.twist (idealSys x J)).sub I = idealMod J I * Q.sub I :=
    fun J I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF₁s : ∀ I, F₁.sub I = twistMod S x (-(e : ℤ)) I * Q.sub I :=
    fun I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF₂s : ∀ I, F₂.sub I = idealMod pp I * (twistMod S x (-(e : ℤ)) I * Q.sub I) := fun I ↦ by
    rw [hF₂, SubSystem.twist_sub_eq_mul_of_line, hF₁s]; rfl
  have hE : ∀ s ∈ V, ∀ I : Chart x,
      ∃ y ∈ F₁.sub I, s - aeval x g * y ∈ (Q.twist (idealSys x J₁)).sub I := by
    intro s hs I
    obtain ⟨i, hi⟩ := I.2.1
    have hsI := mem_secs_iff'.mp hs I
    rw [hsub] at hsI
    rw [hF₁s, hsub]
    exact exists_chart hJh hg I hi _ hsI
  have hU : ∀ I (y : Ω), y ∈ F₁.sub I → aeval x g * y ∈ (Q.twist (idealSys x J₁)).sub I →
      y ∈ F₂.sub I := by
    intro I y hy hgy
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨Q', hQ'⟩ := Q.invertible I
    rw [hF₁s] at hy
    rw [hsub] at hgy
    rw [hF₂s]
    exact mem_chart_of_mul_mem hJ hpp hg I hi _ Q' hQ' hy hgy
  have hC : ∀ I (y : Ω), y ∈ F₂.sub I → aeval x g * y ∈ (Q.twist (idealSys x J₁)).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF₂s] at hy
    rw [hsub]
    exact mul_mem_chart hpp hg I hi _ hy
  let yc : V → ∀ I, F₁.sub I := fun s I ↦ ⟨(hE s s.2 I).choose, (hE s s.2 I).choose_spec.1⟩
  have hyc : ∀ (s : V) I, (s : Ω) - aeval x g * (yc s I : Ω) ∈ (Q.twist (idealSys x J₁)).sub I :=
    fun s I ↦ (hE s s.2 I).choose_spec.2
  have hcls : ∀ I (y y' : F₁.sub I),
      aeval x g * ((y : Ω) - y') ∈ (Q.twist (idealSys x J₁)).sub I →
      (Submodule.Quotient.mk y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = Submodule.Quotient.mk y' := by
    intro I y y' h
    rw [Submodule.Quotient.eq]
    exact hU I _ (y - y').2 h
  let v : V → ∀ I, F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I := fun s I ↦ Submodule.Quotient.mk (yc s I)
  have hcompat : ∀ s I J h, SubSystem.quotRes F₁ F₂ I J h (v s I) = v s J := by
    intro s I J h
    refine hcls J _ _ ?_
    have h1 := sub_mem (hyc s J) ((Q.twist (idealSys x J₁)).mono I J h _ (hyc s I))
    change aeval x g * ((yc s I : Ω) - (yc s J : Ω)) ∈ _
    convert h1 using 1
    ring
  have hcoc : ∀ s, Cech.d (fun I ↦ F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (fun I ↦ v s I.1) = 0 := fun s ↦ Cech.d_zero_of_compat _ (hcompat s)
  let ψ : V →ₗ[S] LinearMap.ker
      (Cech.d (fun I ↦ F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0) :=
    { toFun := fun s ↦ ⟨fun I ↦ v s I.1, hcoc s⟩
      map_add' := fun s t ↦ by
        apply Subtype.ext
        funext I
        change v (s + t) I.1 = v s I.1 + v t I.1
        rw [← Submodule.Quotient.mk_add]
        refine hcls I.1 _ _ ?_
        have h1 := sub_mem (add_mem (hyc s I.1) (hyc t I.1)) (hyc (s + t) I.1)
        convert h1 using 1
        simp only [Submodule.coe_add]
        ring
      map_smul' := fun c s ↦ by
        apply Subtype.ext
        funext I
        change v (c • s) I.1 = c • v s I.1
        rw [← Submodule.Quotient.mk_smul]
        refine hcls I.1 _ _ ?_
        have h1 := sub_mem (Submodule.smul_of_tower_mem _ c (hyc s I.1)) (hyc (c • s) I.1)
        convert h1 using 1
        simp only [Submodule.coe_smul, Submodule.coe_smul_of_tower, Algebra.smul_def]
        ring }
  refine ⟨toH0.comp ψ, fun s hs ↦ ?_⟩
  have hs := eq_zero_of_toH0_eq_zero_degree_zero (ψ s) hs
  have hzero : ∀ I : Cech.Idx (support x) 0, (yc s I.1 : Ω) ∈ F₂.sub I.1 := by
    intro I
    have h1 : v s I.1 = 0 := congrFun hs I
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mp h1
  refine mem_secs_iff'.mpr fun J ↦ ?_
  obtain ⟨j, hj⟩ := J.2.1
  let K : Chart x := ⟨{j}, Finset.singleton_nonempty j, Finset.singleton_subset_iff.mpr (J.2.2 hj)⟩
  have hK : (s : Ω) ∈ (Q.twist (idealSys x J₁)).sub K := by
    have h1 := add_mem (hyc s K) (hC K _ (hzero ⟨K, Finset.card_singleton j⟩))
    rwa [sub_add_cancel] at h1
  exact (Q.twist (idealSys x J₁)).mono K J (Finset.singleton_subset_iff.mpr hj) _ hK

end SectionCount.Drop.Filt.Step

end

end GroundTheory.Heights₂.Heights.Kleiman
