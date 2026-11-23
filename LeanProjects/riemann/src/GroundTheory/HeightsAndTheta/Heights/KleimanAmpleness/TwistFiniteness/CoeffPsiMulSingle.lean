import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.IsUnitPhiOfMemMonos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

theorem map_C_mem_monos {I : Finset (Fin (N + 1))} {t : Poly S N} (ht : t ∈ monos (S := S) I) :
    MvPolynomial.map (C : S →+* Sy S r) t ∈ monos (S := Sy S r) I := by
  induction ht using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]; exact X_mem_monos (Finset.mem_coe.mp hi)
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem single_mem_TMod (M0 : FinGradedSub (S := S) (x := x) Ω)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    {a : ℤ} {m : Ω} (hm : m ∈ M0.piece a) :
    (toA x η).symm (single (a, (0 : ℤ)) m) ∈ TMod x η S n0 d0 g0 := by
  suffices key : ∀ z ∈ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = a ∧ z = aeval x f • g0 j},
      (toA x η).symm (single (a, (0 : ℤ)) z) ∈ TMod x η S n0 d0 g0 from key m (hspan a hm)
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, f, e, hf, he, rfl⟩ := hz
    have : (toA x η).symm (single (a, (0 : ℤ)) (aeval x f • g0 j)) =
        (MvPolynomial.map (C : S →+* Sy S r) f : Poly (Sy S r) N) • genT x η n0 d0 g0 j := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, genT, AddEquiv.apply_symm_apply, phi_map_C x η S hf,
        single_mul_single, smul_eq_mul, ← he]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => rw [single_zero, map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [single_add, map_add]; exact add_mem hp hq
  | smul s p _ hp =>
    have : (toA x η).symm (single (a, (0 : ℤ)) (s • p)) =
        (C (C s) : Poly (Sy S r) N) • (toA x η).symm (single (a, (0 : ℤ)) p) := by
      apply (toA x η).injective
      rw [AddEquiv.apply_symm_apply, toA_smulP, AddEquiv.apply_symm_apply, phi_C, psi, aeval_C,
        algebraMap_LA, single_mul_single, Algebra.smul_def]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hp

def toChart (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) : Chart x :=
  ⟨I.1, I.2.1, fun i hi => (mem_support x).mpr (hI i hi)⟩

theorem pow_sub_le (B : SubSystem S x Ω)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (I : Chart x) (b : ℕ) :
    (B.pow b).sub I ≤ Submodule.span (chartRing S x I)
      {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} := by
  induction b with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨1, isHomogeneous_one _ _, by simp⟩)
  | succ b ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hgen I] at hq
    have hmul : q * y ∈ Submodule.span (chartRing S x I) (Set.range η) *
        Submodule.span (chartRing S x I)
          {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} :=
      Submodule.mul_mem_mul hq (ih hy)
    rw [Submodule.span_mul_span] at hmul
    rw [smul_eq_mul]
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨X j * h, ?_, by rw [map_mul, aeval_X]⟩
    simpa [add_comm] using (isHomogeneous_X S j).mul hh

variable (M0 : FinGradedSub (S := S) (x := x) Ω)

def genSet (I : Chart x) (b : ℕ) : Set Ω :=
  {ω | ∃ (f : Poly S N) (e : ℕ) (h : MvPolynomial (Fin (r + 1)) S) (m : Ω) (a : ℤ) (t : Poly S N) (e' : ℕ),
    f.IsHomogeneous e ∧ h.IsHomogeneous b ∧ m ∈ M0.piece a ∧ t ∈ monos (S := S) I.1 ∧
    t.IsHomogeneous e' ∧ (e' : ℤ) = e + a ∧ ω = aeval x f * aeval η h * m / aeval x t}

theorem chart_mul_mem_span (I : Chart x) (b : ℕ) (c : chartRing S x I) {ω : Ω}
    (hω : ω ∈ Submodule.span S (genSet x η S M0 I b)) :
    (c : Ω) * ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  obtain ⟨f', t', e'', ht', hf', hte', hc⟩ := c.2
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hz
    refine Submodule.subset_span ⟨f' * f, e'' + e, h, m, a, t' * t, e'' + e', hf'.mul hf, hh, hm,
      mul_mem ht' ht, hte'.mul hte, by push_cast; omega, ?_⟩
    rw [hc]
    have h1 := eval_ne_zero_of_mem_monos I ht'
    have h2 := eval_ne_zero_of_mem_monos I ht
    simp only [map_mul]
    field_simp
  | zero => rw [mul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [mul_add]; exact add_mem hp hq
  | smul s p _ hp => rw [mul_smul_comm]; exact Submodule.smul_mem _ s hp

theorem twist_sub_le (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I) (I : Chart x) (b : ℕ) :
    ∀ ω ∈ (G.twist (B.pow b)).sub I, ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  let W : Submodule (chartRing S x I) Ω :=
    { carrier := Submodule.span S (genSet x η S M0 I b)
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c ω hω => chart_mul_mem_span x η S M0 I b c hω }
  suffices hle : (G.twist (B.pow b)).sub I ≤ W from fun ω hω => hle hω
  change Submodule.span _ _ ≤ W
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  have hq' := pow_sub_le x η S B.toSubFamily.toSubSystem hgen I b hq
  rw [← hG I] at hy
  have hmul := Submodule.mul_mem_mul hq' hy
  rw [FinGradedSub.tilde, Submodule.span_mul_span] at hmul
  rw [smul_eq_mul]
  refine (Submodule.span_le.mpr ?_) hmul
  rintro _ ⟨_, ⟨h, hh, rfl⟩, _, ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨1, 0, h, m, a, t, e, isHomogeneous_one _ _, hh, hm, ht, hte, by omega, ?_⟩
  rw [map_one, one_mul, smul_eq_mul]
  field_simp

variable {n0 d0 g0} in
theorem gen_pre
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ genSet x η S M0 (toChart x I hI) b) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hω
  let mm : TMod x η S n0 d0 g0 := ⟨_, single_mem_TMod x η S n0 d0 g0 M0 hspan hm⟩
  let p : Poly (Sy S r) N := MvPolynomial.map (C : S →+* Sy S r) f * C h
  have hp : p.IsHomogeneous e := by
    simpa using (hf.map (C : S →+* Sy S r)).mul (isHomogeneous_C (Fin (N + 1)) h)
  have hmm : mm ∈ (tgraded x η S n0 d0 g0).piece a := by
    change toA x η ((toA x η).symm _) ∈ tgr a
    rw [AddEquiv.apply_symm_apply]
    exact single_mem_tgr _ _ _
  have hpm := (tgraded x η S n0 d0 g0).smul_mem e a p mm hp hmm
  let s : monos (S := Sy S r) I.1 := ⟨MvPolynomial.map (C : S →+* Sy S r) t, map_C_mem_monos S ht⟩
  refine ⟨(LocalizedModule.mk (p • mm) s : LocalizedModule (monos (S := Sy S r) I.1) (TMod x η S n0 d0 g0)),
    Submodule.subset_span ⟨p • mm, s, a + e, e', hpm, hte.map _, by omega, rfl⟩, ?_⟩
  apply locL_mk_eq
  rw [AddEquiv.apply_symm_apply]
  change phi x η S (MvPolynomial.map (C : S →+* Sy S r) t) * _ = toA x η (p • (mm : Amb x η))
  rw [toA_smulP, AddEquiv.apply_symm_apply, phi_map_C x η S hte, map_mul, phi_map_C x η S hf, phi_C,
    psi_of_isHomogeneous η S hh]
  simp only [single_mul_single]
  have ht0 := eval_ne_zero_of_mem_monos (toChart x I hI) ht
  congr 1
  · ext
    · simp; omega
    · simp
  · field_simp

variable {n0 d0 g0} in

theorem chart_pre (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ (G.twist (B.pow b)).sub (toChart x I hI)) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  have h1 := twist_sub_le x η S M0 G B hgen hG (toChart x I hI) b ω hω
  clear hω
  induction h1 using Submodule.span_induction with
  | mem z hz => exact gen_pre x η S M0 hspan I hI b hz
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, single_zero, map_zero]⟩
  | add p q _ _ hp hq =>
    obtain ⟨z1, hz1, e1⟩ := hp
    obtain ⟨z2, hz2, e2⟩ := hq
    exact ⟨z1 + z2, add_mem hz1 hz2, by rw [map_add, e1, e2, single_add, map_add]⟩
  | smul s p _ hp =>
    obtain ⟨z1, hz1, e1⟩ := hp
    refine ⟨(C s : Sy S r) • z1, Submodule.smul_mem _ _ hz1, ?_⟩
    rw [LinearMap.map_smul_of_tower, e1]
    apply (toA x η).injective
    rw [toA_smulSy, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, psi, aeval_C, algebraMap_LA,
      single_mul_single, Algebra.smul_def]
    simp

theorem coeff_psi_mul_single (c : Sy S r) (b' b : ℕ) (s' : Ω) :
    (psi η S c * single ((0 : ℤ), (b' : ℤ)) s').coeff ((0 : ℤ), (b : ℤ)) =
      ∑ d ∈ Finset.range (c.totalDegree + 1),
        if d + b' = b then aeval η (homogeneousComponent d c) * s' else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent c]
  rw [map_sum, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [psi_of_isHomogeneous η S (homogeneousComponent_isHomogeneous d c), single_mul_single, coeff_single,
    Finsupp.single_apply]
  by_cases hdb : d + b' = b
  · rw [if_pos hdb, if_pos (by ext <;> simp; omega)]
  · rw [if_neg hdb, if_neg (by intro h; apply hdb; have := congrArg Prod.snd h; simp at this; omega)]

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
