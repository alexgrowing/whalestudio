import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsJoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem exists_mul_eq_prod_pow {J : Finset (Fin (N + 1))} {s : Poly k N} (hs : s ∈ monos J) :
    ∃ (t : Poly k N) (m d : ℕ), t.IsHomogeneous d ∧ s * t = (∏ i ∈ J, X i) ^ m := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨∏ i' ∈ J.erase i, X i', 1, ∑ _i' ∈ J.erase i, 1,
      IsHomogeneous.prod _ _ _ fun i' _ => isHomogeneous_X k i', ?_⟩
    rw [pow_one, Finset.mul_prod_erase J (fun i' => (X i' : Poly k N)) (Finset.mem_coe.mp hi)]
  | one => exact ⟨1, 0, 0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t₁, m₁, d₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, m₂, d₂, ht₂, h₂⟩ := hb
    exact ⟨t₁ * t₂, m₁ + m₂, d₁ + d₂, ht₁.mul ht₂, by rw [pow_add, ← h₁, ← h₂]; ring⟩

theorem exists_mem_chartRing_mul_pow (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by
  classical
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨t, m, d, ht, hst⟩ := exists_mul_eq_prod_pow (k := k) hs
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hJ0 : xProd J ≠ 0 := xProd_ne_zero J
  have hI0 : xProd I ≠ 0 := xProd_ne_zero I
  have hevJ : aeval x (∏ i ∈ J.1, (X i : Poly k N)) = xProd J := by simp [xProd, map_prod]
  have hevI : aeval x (∏ i ∈ I.1, (X i : Poly k N)) = xProd I := by simp [xProd, map_prod]
  have hst' : aeval x s * aeval x t = xProd J ^ m := by rw [← map_mul, hst, map_pow, hevJ]
  have ht0 : aeval x t ≠ 0 := right_ne_zero_of_mul (hst' ▸ pow_ne_zero m hJ0)
  have hpJ : (∏ i ∈ J.1, (X i : Poly k N)).IsHomogeneous J.1.card := by
    simpa using IsHomogeneous.prod J.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hpI : (∏ i ∈ I.1, (X i : Poly k N)).IsHomogeneous I.1.card := by
    simpa using IsHomogeneous.prod I.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hdeg : e + d = J.1.card * m := by
    have h2 : (s * t).IsHomogeneous (J.1.card * m) := by rw [hst]; exact hpJ.pow m
    have hne : s * t ≠ 0 := by
      rw [hst]
      exact pow_ne_zero _ fun h0 => hJ0 (by rw [← hevJ, h0, map_zero])
    exact (hse.mul ht).inj_right h2 hne
  obtain ⟨i', hi'⟩ : ∃ i', I.1.card = i' + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  refine ⟨aeval x (f * t * (∏ i ∈ J.1, X i) ^ (m * i')) /
      aeval x ((∏ i ∈ I.1, X i) ^ (m * J.1.card)), m,
    ⟨f * t * (∏ i ∈ J.1, X i) ^ (m * i'), (∏ i ∈ I.1, X i) ^ (m * J.1.card),
      I.1.card * (m * J.1.card),
      pow_mem (Submonoid.prod_mem _ fun i hi => X_mem_monos hi) _, ?_, hpI.pow _, rfl⟩, ?_⟩
  · have h3 := (hf.mul ht).mul (hpJ.pow (m * i'))
    convert h3 using 1
    rw [hdeg, hi']
    ring
  · have key : aeval x f / aeval x s = aeval x f * aeval x t / xProd J ^ m := by
      rw [← hst', mul_div_mul_right _ _ ht0]
    rw [key]
    simp only [map_mul, map_pow, hevJ, hevI]
    rw [hi', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero _ hJ0) (mul_ne_zero (pow_ne_zero _ hI0) (pow_ne_zero _ hJ0))]
    ring

theorem ampleChart_mul {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z₁ z₂ : Ω}
    (h₁ : z₁ ∈ ampleChart H m hh I) (h₂ : z₂ ∈ ampleChart H m hh I) :
    z₁ * z₂ ∈ ampleChart H m hh I := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  refine ⟨n₁ + n₂, ?_⟩
  rw [SubSystem.pow_sub_eq_pow] at hn₁ hn₂ ⊢
  rw [mul_add, pow_add]
  have h3 := Submodule.mul_mem_mul hn₁ hn₂
  convert h3 using 1
  ring

theorem mem_ampleChart_of_mem_chartRing {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I :=
  ⟨0, by
    rw [pow_zero, mul_one, mul_zero, SubSystem.pow_sub_eq_pow, pow_zero]
    exact Submodule.mem_one.mpr ⟨⟨c, hc⟩, rfl⟩⟩

theorem ampleChart_pow {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by
  induction n with
  | zero => rw [pow_zero]; exact mem_ampleChart_of_mem_chartRing (one_mem _)
  | succ n ih => rw [pow_succ]; exact ampleChart_mul ih hz

theorem exists_pow_mul_mem_ampleRing {L : SubSystem k x Ω} {hl b c : Ω} {J : Chart x}
    (hb : b ∈ ampleRing L 1 hl)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart L 1 hl I)
    (hc : c ∈ chartRing k x J) : ∃ E : ℕ, b ^ E * c ∈ ampleRing L 1 hl := by
  classical
  have hI : ∀ I : Chart x, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → b ^ E * c ∈ ampleChart L 1 hl I := by
    intro I
    obtain ⟨e, he⟩ := hbJ I
    obtain ⟨c', m, hc', hcc⟩ := exists_mem_chartRing_mul_pow I J hc
    have hbI : b ∈ ampleChart L 1 hl I := Set.mem_iInter.mp hb I
    refine ⟨e * m, fun E hE => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hE
    have h4 : b ^ (e * m + d) * c =
        b ^ d * (c' * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ m) := by
      rw [hcc]; ring
    rw [h4]
    exact ampleChart_mul (ampleChart_pow hbI d)
      (ampleChart_mul (mem_ampleChart_of_mem_chartRing hc') (ampleChart_pow he m))
  choose E₀ hE₀ using hI
  exact ⟨∑ I, E₀ I, Set.mem_iInter.mpr fun I =>
    hE₀ I _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I))⟩

theorem mem_of_pow_mul_mem {B : Subalgebra k Ω} {n : ℕ} {a b : Fin n → Ω} {z : Ω}
    (ha : ∀ i, a i ∈ B) (hb : ∀ i, b i ∈ B) (hab : ∑ i, a i * b i = 1)
    (hz : ∀ i, ∃ E : ℕ, b i ^ E * z ∈ B) : z ∈ B := by
  choose E hE using hz
  have htop : Ideal.span (Set.range fun i => (⟨b i, hb i⟩ : B)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ⟨a i, ha i⟩, Subtype.ext ?_⟩
    simpa using hab
  have h2 := Ideal.span_pow_eq_top _ htop (∑ j, E j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  obtain ⟨c, hc⟩ := h2
  have hcoe : ∑ i, (c i : Ω) * b i ^ (∑ j, E j) = 1 := by
    have h5 := congrArg (fun y : B => (y : Ω)) hc
    simpa using h5
  have hsum : z = ∑ i, (c i : Ω) * (b i ^ (∑ j, E j) * z) := by
    calc z = (∑ i, (c i : Ω) * b i ^ (∑ j, E j)) * z := by rw [hcoe, one_mul]
      _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  refine sum_mem fun i _ => mul_mem (c i).2 ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) : E i ≤ ∑ j, E j)
  have h6 : b i ^ (∑ j, E j) * z = b i ^ d * (b i ^ E i * z) := by rw [hd]; ring
  rw [h6]
  exact mul_mem (pow_mem (hb i) _) (hE i)

theorem div_pow_mem_of_mem_pow {B : Subalgebra k Ω} {T : Set Ω} {s : Ω}
    (hT : ∀ y ∈ T, y / s ∈ B) : ∀ n : ℕ, ∀ y ∈ T ^ n, y / s ^ n ∈ B := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    rw [Set.mem_one.mp hy, pow_zero, div_one]
    exact one_mem B
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy
    rw [pow_succ, mul_div_mul_comm]
    exact mul_mem (ih u hu) (hT v hv)

theorem exists_pow_mul_mem_of_mem_span {B : Subalgebra k Ω} {J : Chart x} {T : Set Ω}
    {s b z : Ω} {n : ℕ} (hs : s ≠ 0) (hb : b ∈ B) (hT : ∀ y ∈ T, y / s ^ n ∈ B)
    (hcoef : ∀ c ∈ chartRing k x J, ∃ E : ℕ, b ^ E * c ∈ B)
    (hz : z * s ^ n ∈ Submodule.span (chartRing k x J) T) : ∃ E : ℕ, b ^ E * z ∈ B := by
  have key : ∀ y ∈ Submodule.span (chartRing k x J) T, ∃ E : ℕ, b ^ E * y / s ^ n ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨0, by rw [pow_zero, one_mul]; exact hT y hy⟩
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨E₁, h₁⟩ := h₁
      obtain ⟨E₂, h₂⟩ := h₂
      refine ⟨E₁ + E₂, ?_⟩
      have h7 : b ^ (E₁ + E₂) * (y₁ + y₂) / s ^ n =
          b ^ E₂ * (b ^ E₁ * y₁ / s ^ n) + b ^ E₁ * (b ^ E₂ * y₂ / s ^ n) := by ring
      rw [h7]
      exact add_mem (mul_mem (pow_mem hb _) h₁) (mul_mem (pow_mem hb _) h₂)
    | smul c y _ h =>
      obtain ⟨E, h⟩ := h
      obtain ⟨E', hE'⟩ := hcoef c c.2
      refine ⟨E' + E, ?_⟩
      rw [chartRing_smul_def]
      have h8 : b ^ (E' + E) * ((c : Ω) * y) / s ^ n = b ^ E' * (c : Ω) * (b ^ E * y / s ^ n) := by
        ring
      rw [h8]
      exact mul_mem hE' h
  obtain ⟨E, hE⟩ := key _ hz
  refine ⟨E, ?_⟩
  have h9 : b ^ E * (z * s ^ n) / s ^ n = b ^ E * z := by
    field_simp
  rwa [h9] at hE

variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

theorem mem_of_mem_ampleRing_twist (hL : IsVeryAmpleBy L h)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I) {l : Fin (r₁ + 1)}
    {j : Fin (s₁ + 1)} (hl : h l ≠ 0) (hj : g j ≠ 0) {B : Subalgebra k Ω}
    (hB : ∀ a b, h a * g b / (h l * g j) ∈ B) {z : Ω}
    (hz : z ∈ ampleRing (L.twist G) 1 (h l * g j)) : z ∈ B := by
  obtain ⟨n, A, Bv, JJ, hA, hBv, hsum, hcov⟩ := hL.affine l hl
  have hK : ∀ y ∈ ampleRing L 1 (h l), y ∈ B := by
    intro y hy
    refine Algebra.adjoin_le ?_ (hL.closed l hl hy)
    rintro _ ⟨a, rfl⟩
    show h a / h l ∈ B
    have h10 : h a / h l = h a * g j / (h l * g j) := (mul_div_mul_right _ _ hj).symm
    rw [h10]
    exact hB a j
  refine mem_of_pow_mul_mem (fun i => hK _ (hA i)) (fun i => hK _ (hBv i)) hsum fun i => ?_
  obtain ⟨m, hm⟩ := Set.mem_iInter.mp hz (JJ i)
  rw [one_mul, SubSystem.pow_sub_eq_pow, SubSystem.twist_sub_eq_mul, ← hL.generates (JJ i),
    ← hgg (JJ i), Submodule.span_mul_span, Submodule.span_pow] at hm
  refine exists_pow_mul_mem_of_mem_span (mul_ne_zero hl hj) (hK _ (hBv i))
    (div_pow_mem_of_mem_pow (fun y hy => ?_) m) (fun c hc => ?_) hm
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
    exact hB a b
  · obtain ⟨E, hE⟩ := exists_pow_mul_mem_ampleRing (hBv i) (hcov i) hc
    exact ⟨E, hK _ hE⟩

theorem isVeryAmpleBy_twist {R : ℕ} (hL : IsVeryAmpleBy L h) (hgs : ∀ j, g j ∈ G.secs)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I)
    (e : Fin (R + 1) ≃ Fin (r₁ + 1) × Fin (s₁ + 1)) :
    IsVeryAmpleBy (L.twist G) (fun p => h (e p).1 * g (e p).2) := by
  have hgI : ∀ j I, g j ∈ G.sub I := fun j I => (Submodule.mem_iInf _).mp (hgs j) I
  have hmono : ∀ (l : Fin (r₁ + 1)) (j : Fin (s₁ + 1)) (I : Chart x) (z : Ω),
      z ∈ ampleChart L 1 (h l) I → z ∈ ampleChart (L.twist G) 1 (h l * g j) I := by
    intro l j I z hz
    obtain ⟨n, hn⟩ := hz
    refine ⟨n, ?_⟩
    rw [one_mul, SubSystem.pow_sub_eq_pow] at hn ⊢
    rw [SubSystem.twist_sub_eq_mul, mul_pow (L.sub I) (G.sub I), mul_pow (h l) (g j), ← mul_assoc]
    exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ (hgI j I) n)
  have hmonoR : ∀ (l : Fin (r₁ + 1)) (j : Fin (s₁ + 1)) (z : Ω),
      z ∈ ampleRing L 1 (h l) → z ∈ ampleRing (L.twist G) 1 (h l * g j) := fun l j z hz =>
    Set.mem_iInter.mpr fun I => hmono l j I z (Set.mem_iInter.mp hz I)
  refine ⟨fun p => ?_, fun I => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · refine (Submodule.mem_iInf _).mpr fun I => ?_
    change h (e p).1 * g (e p).2 ∈ (L.twist G).sub I
    rw [SubSystem.twist_sub_eq_mul]
    exact Submodule.mul_mem_mul ((Submodule.mem_iInf _).mp (hL.mem_secs _) I) (hgI _ I)
  · rw [SubSystem.twist_sub_eq_mul, ← hL.generates I, ← hgg I, Submodule.span_mul_span]
    congr 1
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact Set.mul_mem_mul ⟨_, rfl⟩ ⟨_, rfl⟩
    · intro hz
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨e.symm (a, b), by simp⟩
  · intro a ha
    refine mem_of_mem_ampleRing_twist (B := ampleBase (S := k) (fun q => h (e q).1 * g (e q).2) p)
      hL hgg (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp) (fun a' b' => ?_) ha
    unfold ampleBase
    apply Algebra.subset_adjoin
    exact ⟨e.symm (a', b'), by simp⟩
  · obtain ⟨n, A, Bv, JJ, hA, hBv, hsum, hcov⟩ := hL.affine (e p).1 (left_ne_zero_of_mul hp)
    refine ⟨n, A, Bv, JJ, fun i => hmonoR _ _ _ (hA i), fun i => hmonoR _ _ _ (hBv i), hsum,
      fun i I => ?_⟩
    obtain ⟨e', he'⟩ := hcov i I
    exact ⟨e', hmono _ _ _ _ he'⟩

end Lemmas

theorem VeryAmpleTwistGenerated.proof : VeryAmpleTwistGenerated.Statement.{u, w} := by
  rintro k _ Ω _ _ N x L G - hG ⟨r, h, hL⟩ hGg
  classical

  have hfin : ∀ I : Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.secs ∧
      G.sub I ≤ Submodule.span (chartRing k x I) (T : Set Ω) := by
    intro I
    obtain ⟨G', hG'⟩ := hG I
    obtain ⟨F, hF⟩ := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one _ hG')
    have hsp : ∀ f ∈ F, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.secs ∧
        f ∈ Submodule.span (chartRing k x I) (T : Set Ω) := fun f hf =>
      Submodule.mem_span_finite_of_mem_span (by rw [hGg I, ← hF]; exact Submodule.subset_span hf)
    choose! Tf hTf using hsp
    refine ⟨F.biUnion Tf, fun z hz => ?_, ?_⟩
    · obtain ⟨f, hf, hz⟩ := Finset.mem_biUnion.mp hz
      exact (hTf f hf).1 hz
    · rw [← hF, Submodule.span_le]
      intro f hf
      refine Submodule.span_mono (fun z hz => ?_) (hTf f hf).2
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨f, hf, hz⟩)
  choose T hTs hTg using hfin
  set U : Finset Ω := Finset.univ.biUnion T with hU
  have hUs : (U : Set Ω) ⊆ G.secs := fun z hz => by
    obtain ⟨I, -, hz⟩ := Finset.mem_biUnion.mp hz
    exact hTs I hz
  let g : Fin (U.card + 1) → Ω := Fin.cons 0 fun i => (U.equivFin.symm i : Ω)
  have hgs : ∀ j, g j ∈ G.secs := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [g, Fin.cons_zero]
      exact zero_mem _
    · simp only [g, Fin.cons_succ]
      exact hUs (U.equivFin.symm i).2
  have hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I := by
    intro I
    apply le_antisymm
    · exact (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hgs j)).trans
        (SubSystem.span_secs_le G I)
    · refine (hTg I).trans (Submodule.span_mono (s := (T I : Set Ω)) (t := Set.range g) fun z hz => ?_)
      have hzU : z ∈ U := Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, hz⟩
      exact ⟨(U.equivFin ⟨z, hzU⟩).succ, by simp [g]⟩
  have hR : (r + 1) * (U.card + 1) - 1 + 1 = (r + 1) * (U.card + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  exact ⟨_, _, isVeryAmpleBy_twist hL hgs hgg ((finCongr hR).trans finProdFinEquiv.symm)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
