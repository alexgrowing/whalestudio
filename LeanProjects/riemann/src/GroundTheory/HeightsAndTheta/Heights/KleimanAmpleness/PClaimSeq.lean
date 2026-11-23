import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsZeroIdealChart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

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

end Forms

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem form_mul_mem_twistMod {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x h * o ∈ twistMod k x (c + d) I) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    exact Submodule.subset_span ⟨h * f, s, e, d + e', hs, hh.mul hf, hse, by push_cast; omega,
      by rw [map_mul, mul_div_assoc]⟩
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have := Submodule.smul_mem _ a hz
    rw [chartRing_smul_def] at this ⊢
    rwa [mul_left_comm]

theorem div_mem_chartRing {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
  obtain ⟨a, rfl⟩ := ho
  have hq : x i ^ (e : ℤ) / aeval x s ∈ chartRing k x I :=
    ⟨X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X, zpow_natCast]⟩
  rw [chartRing_smul_def, mul_div_assoc]
  exact mul_mem a.2 hq

variable (T : StepData k x)

theorem StepData.form_mem_J {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by
  have hG : ∀ g ∈ {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o}, g.IsHomogeneous g.totalDegree :=
    fun g ⟨c, hc, _⟩ => isHomogeneous_totalDegree hc
  have hmem := mem_span_forms_of_mem_ideal _ hG hf he
  refine Submodule.span_induction (p := fun f _ => ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, ⟨c, hc, hg⟩, h, d', hh, hd, rfl⟩
    by_cases h0 : g = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [h0, mul_zero, map_zero, zero_mul, mul_zero]⟩
    obtain ⟨o, ho, hgo⟩ := hg I δ hδ
    rw [hc.totalDegree h0] at hd
    refine ⟨aeval x h * o, ?_, by rw [map_mul, mul_assoc, hgo, mul_left_comm]⟩
    have := form_mul_mem_twistMod hh I ho
    rwa [show (c : ℤ) + d' = e by omega] at this
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_mul, mul_zero]⟩
  · rintro _ _ _ _ ⟨o, ho, h1⟩ ⟨o', ho', h2⟩
    exact ⟨o + o', Submodule.add_mem _ ho ho', by rw [map_add, add_mul, h1, h2, mul_add]⟩
  · rintro a _ _ ⟨o, ho, h1⟩
    refine ⟨a • o, (twistMod k x e I).smul_of_tower_mem a ho, ?_⟩
    rw [map_smul, smul_mul_assoc, h1, mul_smul_comm]

def StepData.Jg : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z | ∃ (f : Poly k N)
      (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, T.J.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; rw [smul_comm]; exact Submodule.smul_mem _ a hz
  fg := by
    classical
    set G : Set (Poly k N) := {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o} with hGdef
    have hJ : T.J = Ideal.span G := rfl
    have hfg : (Submodule.span (Poly k N) G).FG := IsNoetherian.noetherian _
    obtain ⟨G₀, hG₀, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
    have hG : ∀ g ∈ (G₀ : Set (Poly k N)), g.IsHomogeneous g.totalDegree :=
      fun g hg => by obtain ⟨c, hc, _⟩ := hG₀ hg; exact isHomogeneous_totalDegree hc
    let gj : Fin G₀.card → Poly k N := fun j => (G₀.equivFin.symm j : Poly k N)
    refine ⟨G₀.card, fun j => ((gj j).totalDegree : ℤ), fun j => aeval x (gj j), fun j => ?_, fun c => ?_⟩
    · refine Submodule.subset_span ⟨gj j, _, ?_, hG _ (G₀.equivFin.symm j).2, rfl, rfl⟩
      rw [hJ]; exact Ideal.subset_span (hG₀ (G₀.equivFin.symm j).2)
    · rw [Submodule.span_le]
      rintro _ ⟨f, e, hf, he, rfl, rfl⟩
      rw [hJ, Ideal.span, hspan] at hf
      have hm := mem_span_forms_of_mem_ideal _ hG hf he
      refine Submodule.span_induction (p := fun f _ => aeval x f ∈ _) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨g, hg, h, d', hh, hd, rfl⟩
        refine Submodule.subset_span ⟨G₀.equivFin ⟨g, hg⟩, h, d', hh, ?_, ?_⟩
        · simp only [gj, Equiv.symm_apply_apply]; omega
        · simp only [gj, Equiv.symm_apply_apply, map_mul, smul_eq_mul]
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz; rw [map_smul]; exact Submodule.smul_mem _ a hz

theorem StepData.Jg_tilde (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod T.J I)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨f, e', hf, hfe, rfl, rfl⟩
      have he : e' = e := by omega
      subst he
      exact Submodule.subset_span ⟨f, s, e', hf, hs, hfe, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c z _ hz; rw [smul_comm]; exact (idealMod T.J I).smul_of_tower_mem c hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hf, hfe, rfl, rfl⟩, sub_self _, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem StepData.isUnit_D (I : Chart x) : IsUnit (T.D.sub I) := by
  obtain ⟨i, hi⟩ := I.2.1
  have h0 : (twistSys k x 0).sub I = 1 := by
    change twistMod k x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  have hO : IsUnit ((twistSys k x (T.m - T.c₁)).sub I) :=
    IsUnit.of_mul_eq_one ((twistSys k x (-(T.m - T.c₁))).sub I) (by rw [twistSys_sub_mul, add_neg_cancel, h0])
  obtain ⟨Q', hQ'⟩ := T.M.invertible I
  rw [StepData.D, twistMul_sub]
  exact hO.mul ((IsUnit.of_mul_eq_one _ hQ').pow _)

theorem StepData.idealMod_mul_D (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun a ha δ hδ => ?_
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := idealMod_mem_form T.J I ha
    obtain ⟨o, ho, hgo⟩ := T.form_mem_J hg hge I hδ
    refine Submodule.mem_span_singleton.mpr ⟨⟨o / aeval x s, div_mem_chartRing I ho hs hse⟩, ?_⟩
    rw [chartRing_smul_def]
    change o / aeval x s * T.si = aeval x g / aeval x s * δ
    rw [div_mul_eq_mul_div (aeval x g), hgo]
    ring
  · obtain ⟨Q', hQ'⟩ := (T.isUnit_D I).exists_right_inv
    have hle : Submodule.span (chartRing k x I) {T.si} * Q' ≤ idealMod T.J I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ c (hZ k Ω N x T I b fun δ hδ => ?_)
      have h1 : b * δ ∈ T.D.sub I * Q' := by
        rw [mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      rw [hQ', Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      rw [← hy]; exact y.2
    calc Submodule.span (chartRing k x I) {T.si}
        = Submodule.span (chartRing k x I) {T.si} * Q' * T.D.sub I := by
          rw [mul_assoc, mul_comm Q', hQ', mul_one]
      _ ≤ idealMod T.J I * T.D.sub I := Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (hle ha) hb

end Chart

theorem ClaimSeq.proof (hZ : ZeroIdealChart.Statement.{u, w}) : ClaimSeq.Statement.{u, w} := by
  intro k _ Ω _ _ N x T
  refine ⟨T.Jg, fun c => rfl, fun b c I z => ?_⟩
  have hm : (twistSys k x T.m).sub I = (twistSys k x T.c₁).sub I * (twistSys k x (T.m - T.c₁)).sub I := by
    rw [twistSys_sub_mul, show T.c₁ + (T.m - T.c₁) = T.m by ring]
  have hc : (twistSys k x (c + T.c₁)).sub I = (twistSys k x c).sub I * (twistSys k x T.c₁).sub I := by
    rw [twistSys_sub_mul]
  have hJD := T.idealMod_mul_D hZ I
  have hL : T.L.sub I = (twistSys k x T.c₁).sub I * T.D.sub I := by
    rw [StepData.L, StepData.D, twistMul_sub, twistMul_sub, hm, mul_assoc]
  have key : ((T.Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I =
      Submodule.span (chartRing k x I) {T.si} * ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, T.Jg_tilde I, hc, ← hJD, hL]
    ring
  rw [key, Submodule.mem_span_singleton_mul]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
