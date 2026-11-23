import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDevissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SnapperHyperplaneMid

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

section Quot

def mulQ (F₁ G₁ G₂ : SubSystem k x Ω) (u : Ω) (hmap : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₁.sub I) (I : Chart x) :
    F₁.sub I →ₗ[k] G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I :=
  (SubSystem.quotSub G₁ G₂ I).mkQ ∘ₗ
    { toFun := fun y => ⟨u * y, hmap I y y.2⟩
      map_add' := fun y y' => Subtype.ext (mul_add u (y : Ω) y')
      map_smul' := fun c y => Subtype.ext (mul_smul_comm c u (y : Ω)) }

theorem eulerCharQuot_eq_of_mul (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (u : Ω)
    (hmap : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₁.sub I)
    (honto : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - u * y ∈ G₂.sub I)
    (hker : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₂.sub I ↔ y ∈ F₂.sub I) :
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂ := by
  have hk : ∀ I, LinearMap.ker (mulQ F₁ G₁ G₂ u hmap I) = SubSystem.quotSub F₁ F₂ I := by
    intro I
    ext y
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact hker I y y.2
  have hs : ∀ I, Function.Surjective (mulQ F₁ G₁ G₂ u hmap I) := by
    intro I z
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, hy, hyz⟩ := honto I z z.2
    refine ⟨⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    change u * y - (z : Ω) ∈ G₂.sub I
    rw [← neg_sub]
    exact neg_mem hyz
  let φ : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => (Submodule.quotEquivOfEq _ _ (hk I).symm).trans (LinearMap.quotKerEquivOfSurjective _ (hs I))
  have hφ : ∀ I J h m, φ J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (φ I m) := by
    intro I J h m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    simp only [φ, Submodule.mkQ_apply, SubSystem.quotRes, LinearEquiv.trans_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Quot

section Chart

theorem not_mem_of_mem_monos {pp : Ideal (Poly k N)} (hp : pp.IsPrime) {I : Finset (Fin (N + 1))}
    (hI : ∀ l ∈ I, (X l : Poly k N) ∉ pp) {s : Poly k N} (hs : s ∈ monos I) : s ∉ pp := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    exact hI l hl
  | one => exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hp.mem_or_mem h).elim ha hb

theorem exists_eq_of_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {z : Ω} (hz : z ∈ idealMod pp I) :
    ∃ (g s : Poly k N) (e : ℕ), g ∈ pp ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      z = aeval x g / aeval x s := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    exact ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := ha
    obtain ⟨g', s', e', hg', hs', hge', hse', rfl⟩ := hb
    refine ⟨g * s' + s * g', s * s', e + e', pp.add_mem (pp.mul_mem_right _ hg) (pp.mul_mem_left _ hg'),
      mul_mem hs hs', (hge.mul hse').add (hse.mul hge'), hse.mul hse', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hs) (eval_ne_zero_of_mem_monos I hs')]
    simp only [map_add, map_mul]
  | smul a b _ hb =>
    obtain ⟨f, s₀, e₀, hs₀, hf, hse₀, ha⟩ := a.2
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := hb
    refine ⟨f * g, s₀ * s, e₀ + e, pp.mul_mem_left _ hg, mul_mem hs₀ hs, hf.mul hge, hse₀.mul hse, ?_⟩
    rw [chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]

theorem one_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {l : Fin (N + 1)} (hl : l ∈ I.1)
    (hX : (X l : Poly k N) ∈ pp) : (1 : Ω) ∈ idealMod pp I :=
  Submodule.subset_span ⟨X l, X l, 1, hX, X_mem_monos hl, isHomogeneous_X _ _, isHomogeneous_X _ _, by
    rw [aeval_X, div_self ((mem_support x).mp (I.2.2 hl))]⟩

theorem mem_idealMod_of_mul {pp : Ideal (Poly k N)} (hp : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {i j : Fin (N + 1)} (hi : (X i : Poly k N) ∉ pp) {I : Chart x} {r q : Ω} (hr : r ∈ chartRing k x I)
    (hq : q ∈ idealMod pp I) (h : x i * r = x j * q) : r ∈ idealMod pp I := by
  by_cases hI : ∃ l ∈ I.1, (X l : Poly k N) ∈ pp
  · obtain ⟨l, hl, hX⟩ := hI
    have := Submodule.smul_mem (idealMod pp I) (⟨r, hr⟩ : chartRing k x I) (one_mem_idealMod hl hX)
    rwa [chartRing_smul_def, mul_one] at this
  push Not at hI
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hr
  obtain ⟨g, s', e', hg, hs', hge, hse', rfl⟩ := exists_eq_of_mem_idealMod hq
  have h0 := eval_ne_zero_of_mem_monos I hs
  have h0' := eval_ne_zero_of_mem_monos I hs'
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff h0 h0'] at h
  have hhom : (X i * f * s' - X j * g * s).IsHomogeneous (1 + e + e') := by
    refine (((isHomogeneous_X k i).mul hf).mul hse').sub ?_
    have := ((isHomogeneous_X k j).mul hge).mul hse
    rwa [show 1 + e' + e = 1 + e + e' by omega] at this
  have hev : aeval x (X i * f * s' - X j * g * s) = 0 := by
    simp only [map_sub, map_mul, aeval_X]
    rw [h, sub_self]
  have hmem : X i * f * s' ∈ pp := by
    have h1 := pp.add_mem (hle ((mem_primeOf_of_isHomogeneous x hhom).mpr hev))
      (pp.mul_mem_right s (pp.mul_mem_left (X j) hg))
    rwa [sub_add_cancel] at h1
  have hf' : f ∈ pp := by
    rcases hp.mem_or_mem hmem with h2 | h2
    · rcases hp.mem_or_mem h2 with h3 | h3
      · exact absurd h3 hi
      · exact h3
    · exact absurd h2 (not_mem_of_mem_monos hp hI hs')
  exact Submodule.subset_span ⟨f, s, e, hf', hs, hf, hse, rfl⟩

theorem idealMod_sup_le {pp : Ideal (Poly k N)} (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    {i j : Fin (N + 1)} {I : Chart x} (hj : j ∈ I.1) :
    idealMod (pp ⊔ Ideal.span {(X i : Poly k N)}) I ≤
      idealMod pp I ⊔ Submodule.span (chartRing k x I) {x i / x j} := by
  have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [SetLike.mem_coe, ← homogeneousComponent_eq_self hfe, map_add, map_add, add_div]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span
    ⟨homogeneousComponent e g, s, e, hh g hg e, hs, homogeneousComponent_isHomogeneous e g, hse, rfl⟩))
    (Submodule.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form h (X i) (isHomogeneous_X k i) e
  generalize homogeneousComponent e (h * X i) = v at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h', d', hh', hd', rfl⟩ := hv
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨aeval x (h' * X j) / aeval x s, h' * X j, s, e, hs, hd' ▸ hh'.mul (isHomogeneous_X k j), hse,
      rfl⟩, ?_⟩
    rw [chartRing_smul_def]
    simp only [map_mul, aeval_X]
    field_simp
  | zero => simp
  | add v w _ _ hv hw => rw [map_add, add_div]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
    rw [map_smul, smul_div_assoc]
    exact Submodule.smul_of_tower_mem _ c hv

theorem eulerCharQuot_mid (pp : Ideal (Poly k N)) (hp : pp.IsPrime)
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hle : primeOf (S := k) x ≤ pp)
    (i : Fin (N + 1)) (hi : (X i : Poly k N) ∉ pp) (M : SubSystem k x Ω)
    (hM : ∀ I, ∃ M' : Submodule (chartRing k x I) Ω, M.sub I * M' = 1) :
    eulerCharQuot k ((M.twist (twistSys k x 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)})))
        ((M.twist (twistSys k x 1)).twist (idealSys x pp)) =
      eulerCharQuot k M (M.twist (idealSys x pp)) := by
  have hO : ∀ (I : Chart x) (j : Fin (N + 1)), j ∈ I.1 →
      (twistSys k x 1).sub I = Submodule.span (chartRing k x I) {x j} := fun I j hj => by
    rw [show (twistSys k x 1).sub I = twistMod k x 1 I from rfl, twistMod_eq_span 1 I hj, zpow_one]
  have hsub : ∀ (K : Ideal (Poly k N)) (I : Chart x),
      ((M.twist (twistSys k x 1)).twist (idealSys x K)).sub I =
        idealMod K I * ((twistSys k x 1).sub I * M.sub I) :=
    fun K I => by rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]; rfl
  have hsub' : ∀ I : Chart x, (M.twist (idealSys x pp)).sub I = idealMod pp I * M.sub I :=
    fun I => by rw [SubSystem.twist_sub_eq_mul_of_line]; rfl
  refine eulerCharQuot_eq_of_mul _ _ _ _ (x i) ?_ ?_ ?_
  · intro I y hy
    obtain ⟨j, hj⟩ := I.2.1
    have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
    rw [hsub, hO I j hj]
    have hu : x i / x j ∈ idealMod (pp ⊔ Ideal.span {(X i : Poly k N)}) I :=
      Submodule.subset_span ⟨X i, X j, 1, Ideal.mem_sup_right (Ideal.mem_span_singleton_self _),
        X_mem_monos hj, isHomogeneous_X _ _, isHomogeneous_X _ _, by rw [aeval_X, aeval_X]⟩
    have := Submodule.mul_mem_mul hu (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (x j)) hy)
    rwa [← mul_assoc (x i / x j), div_mul_cancel₀ _ hxj] at this
  · intro I z hz
    obtain ⟨j, hj⟩ := I.2.1
    have hxj : x j ≠ 0 := (mem_support x).mp (I.2.2 hj)
    rw [hsub, hO I j hj] at hz
    rw [hsub, hO I j hj]
    have hz' := mul_le_mul' (idealMod_sup_le hh (i := i) hj) le_rfl hz
    rw [Submodule.sup_mul] at hz'
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.mp hz'
    rw [← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton, div_mul_cancel₀ _ hxj] at hv
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_span_singleton_mul.mp hv
    exact ⟨m, hm, by rwa [add_sub_cancel_right]⟩
  · intro I y hy
    obtain ⟨j, hj⟩ := I.2.1
    rw [hsub, hsub', hO I j hj]
    constructor
    · intro h2
      obtain ⟨M', hM'⟩ := hM I
      have key : ∀ m' ∈ M', y * m' ∈ idealMod pp I := by
        intro m' hm'
        have h3 := Submodule.mul_mem_mul h2 hm'
        rw [mul_assoc, mul_assoc, hM', mul_one, mul_comm, Submodule.mem_span_singleton_mul] at h3
        obtain ⟨q, hq, hqe⟩ := h3
        have hr : y * m' ∈ (1 : Submodule (chartRing k x I) Ω) := hM' ▸ Submodule.mul_mem_mul hy hm'
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
        have hr' : y * m' ∈ chartRing k x I := hr ▸ r.2
        exact mem_idealMod_of_mul hp hle hi hr' hq (by rw [← mul_assoc, hqe])
      have hy1 : y ∈ Submodule.span (chartRing k x I) {y} * (M' * M.sub I) := by
        rw [mul_comm M', hM', mul_one]
        exact Submodule.mem_span_singleton_self y
      rw [← mul_assoc] at hy1
      refine mul_le_mul' (Submodule.mul_le.mpr fun a ha b hb => ?_) le_rfl hy1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c (key b hb)
    · intro h2
      have hxi : x i ∈ Submodule.span (chartRing k x I) {x j} := hO I j hj ▸ mem_twistMod_one I i
      have := Submodule.mul_mem_mul hxi h2
      rwa [mul_left_comm] at this

end Chart

end SnapperHyperplaneMid

theorem SnapperHyperplaneMid.proof : SnapperHyperplaneMid.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a t L n c
  let Mb := (twistPowsBundle (twistBundle k x a) t L n).tensorProd (twistBundle k x c)
  have hM : Mb.toSubSystem =
      ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle (twistBundle k x a) t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ (b : ℤ) (K : Ideal (Poly k N)),
      (((twistSys k x b).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
          (twistSys k x c) =
        (((twistSys k x b).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)).twist
          (idealSys x K) := by
    intro b K
    rw [twistPows_twist_comm (twistSys k x b) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  have hQ : ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) =
      Mb.toSubSystem.twist (twistSys k x 1) := by
    rw [hM, ← twistSys_twist_eq_add a 1, twistPows_twist_comm (twistSys k x a) (twistSys k x 1),
      SubSystem.twist_assoc _ (twistSys k x 1) (twistSys k x c),
      SubSystem.twist_comm (twistSys k x 1) (twistSys k x c), ← SubSystem.twist_assoc]
  unfold pieceChar
  rw [hG (a + 1) (pp ⊔ Ideal.span {(X i : Poly k N)}), hG (a + 1) pp, hG a pp, hQ, ← hM]
  exact SnapperHyperplaneMid.eulerCharQuot_mid pp hp hh hle i hi Mb.toSubSystem Mb.invertible

end

end GroundTheory.Heights₂.Heights.Kleiman
