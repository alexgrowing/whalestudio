import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutDimLowerSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutDimLowerAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_monos_mul_mem_twistMod_all (L : LineBundle S x) (I : Chart x) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    ∃ U ∈ monos (S := S) I.1, ∃ dU : ℕ, U.IsHomogeneous dU ∧
      ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
  classical
  have hyU := mul_mem_chartRing_union L.toSubFamily I
  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)
  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  refine ⟨U, hUm, dU, hUh, fun K δ hδ => ?_⟩
  rw [← hG K] at hδ
  induction hδ using Submodule.span_induction with
  | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
      ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hb

end CutDimLowerAux

theorem CutDimLower.proof : CutDimLower.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x n pp L s qq hW hs hqq hjq
  obtain ⟨j, hj⟩ := hjq
  have hpp : pp.IsPrime := hW.isPrime
  have hqp : qq.IsPrime := hqq.1.1
  have hle : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hqq.1.2
  have hppq : pp ≤ qq := le_sup_left.trans hle
  have hZq : zeroIdeal L.toSubSystem s ≤ qq := le_sup_right.trans hle

  have hvan : ∀ {F : Poly k N} {e : ℕ}, F.IsHomogeneous e → aeval x F = 0 → F ∈ pp := fun hF h0 =>
    hW.le ((mem_primeOf_of_isHomogeneous x hF).mpr h0)
  have hxj : x j ≠ 0 := by
    intro h0
    exact hj (hppq (hvan (isHomogeneous_X k j) (by rw [aeval_X, h0])))
  set J : Chart x := singleChart hxj with hJdef
  have hjJ : j ∈ J.1 := Finset.mem_singleton_self j
  have hmono : ∀ {t : Poly k N}, t ∈ monos (S := k) J.1 → t ∉ qq := fun ht =>
    monos_not_mem (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hj) ht

  have hone : (1 : Ω) ∉ idealMod (x := x) qq J := by
    intro h1
    obtain ⟨g, t, e, hg, ht, hge, hte, h1⟩ := idealMod_mem_form qq J h1
    have ht0 := eval_ne_zero_of_mem_monos J ht
    have hgt : aeval x g = aeval x t := by
      rw [eq_div_iff ht0, one_mul] at h1; exact h1.symm
    have hd : g - t ∈ qq := hppq (hvan (hge.sub hte) (by rw [map_sub, hgt, sub_self]))
    exact hmono ht (by simpa using sub_mem hg hd)

  obtain ⟨Q', hQ'⟩ := L.invertible J
  have hLQ : ∀ l ∈ L.sub J, ∀ q ∈ Q', l * q ∈ chartRing k x J := by
    intro l hl q hq
    have h := Submodule.mul_mem_mul hl hq
    rw [hQ', Submodule.mem_one] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact y.2
  obtain ⟨l, hl, q, hq, hu⟩ : ∃ l ∈ L.sub J, ∃ q ∈ Q', l * q ∉ idealMod (x := x) qq J := by
    by_contra hcon
    push Not at hcon
    have h1 : L.sub J * Q' ≤ idealMod (x := x) qq J := Submodule.mul_le.mpr fun l hl q hq => hcon l hl q hq
    rw [hQ'] at h1
    exact hone (h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩))

  have hsJ : s ∈ L.sub J := (Submodule.mem_iInf _).mp hs J
  obtain ⟨f, t0, e, ht0, hf, ht0e, ha⟩ := hLQ s hsJ q hq
  have ht00 := eval_ne_zero_of_mem_monos J ht0
  have hfz : s * q * aeval x t0 = aeval x f := (eq_div_iff ht00).mp ha

  obtain ⟨U, hUm, dU, hUh, hUK⟩ := exists_monos_mul_mem_twistMod_all L J q
    (fun δ hδ => by rw [mul_comm]; exact hLQ δ hδ q hq)
  have hfU : f * U ∈ zeroIdeal L.toSubSystem s := by
    refine Ideal.subset_span ⟨e + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x t0 * (aeval x U * (q * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod ht0e K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]; ring
  have hfq : f ∈ qq := (hqp.mem_or_mem (hZq hfU)).resolve_right (hmono hUm)

  obtain ⟨U', t2, eU, ht2, hU'h, ht2e, hUdef⟩ := hLQ l hl q hq
  have hU'q : U' ∉ qq := fun h => hu (hUdef ▸ Submodule.subset_span ⟨U', t2, eU, h, ht2, hU'h, ht2e, rfl⟩)
  have ht20 := eval_ne_zero_of_mem_monos J ht2
  have hU'v : aeval x U' = l * q * aeval x t2 := ((eq_div_iff ht20).mp hUdef).symm
  have hgen : ∀ h ∈ {f' : Poly k N | ∃ c : ℕ, f'.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ L.toSubSystem.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f' * δ = s * o},
      ∃ t : Poly k N, t ∉ qq ∧ t * h ∈ pp ⊔ Ideal.span {f} := by
    rintro h ⟨c, hc, hh⟩
    obtain ⟨o, ho, hho⟩ := hh J l hl
    rw [twistMod_eq_span (c : ℤ) J hjJ, Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    obtain ⟨B, t1, eb, ht1, hB, ht1e, hb⟩ := b.2
    have ht10 := eval_ne_zero_of_mem_monos J ht1
    have hBv : aeval x B = (b : Ω) * aeval x t1 := ((eq_div_iff ht10).mp hb).symm
    rw [chartRing_smul_def, zpow_natCast] at hho
    have hF1 : (U' * h * t0 * t1).IsHomogeneous (eU + c + e + eb) := ((hU'h.mul hc).mul ht0e).mul ht1e
    have hF2 : (f * (B * X j ^ c * t2)).IsHomogeneous (eU + c + e + eb) := by
      have := hf.mul ((hB.mul (isHomogeneous_X_pow j c)).mul ht2e)
      rwa [show e + (eb + c + eU) = eU + c + e + eb by ring] at this
    have hFv : aeval x (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) = 0 := by
      simp only [map_sub, map_mul, map_pow, aeval_X]
      rw [hU'v, hBv, ← hfz]
      linear_combination (q * aeval x t2 * aeval x t0 * aeval x t1) * hho
    refine ⟨U' * t0 * t1, ?_, ?_⟩
    · intro hmem
      rcases hqp.mem_or_mem hmem with h1 | h1
      · rcases hqp.mem_or_mem h1 with h2 | h2
        · exact hU'q h2
        · exact hmono ht0 h2
      · exact hmono ht1 h1
    · have hsplit : U' * t0 * t1 * h =
          (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) + f * (B * X j ^ c * t2) := by ring
      rw [hsplit]
      exact add_mem (Ideal.mem_sup_left (hvan (hF1.sub hF2) hFv))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

  have hmin : qq ∈ (pp ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqp, sup_le hppq ((Ideal.span_singleton_le_iff_mem qq).mpr hfq)⟩, ?_⟩
    rintro r ⟨hr, hfr⟩ hrq
    refine hqq.2 ⟨hr, sup_le (le_sup_left.trans hfr) (Ideal.span_le.mpr ?_)⟩ hrq
    intro h hh
    obtain ⟨t, htq, hth⟩ := hgen h hh
    exact (hr.mem_or_mem (hfr hth)).resolve_left fun h' => htq (hrq h')

  have hQ := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have := hpp
  have : (qq.map (Ideal.Quotient.mk pp)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient k
    (qq.map (Ideal.Quotient.mk pp))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hppq), hW.dim] at key
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (Poly k N ⧸ qq) = D at key hnn ⊢
  generalize (qq.map (Ideal.Quotient.mk pp)).height = H at key hQ
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe d =>
    have key' : H + d = ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast key
    suffices ((n + 1 : ℕ) : ℕ∞) ≤ d by exact_mod_cast this
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction H using ENat.recTopCoe with
      | top => simp at hQ
      | coe h =>
        have h1 : h ≤ 1 := by exact_mod_cast hQ
        have h2 : h + m = n + 1 + 1 := by exact_mod_cast key'
        exact_mod_cast (by omega : n + 1 ≤ m)

end

end GroundTheory.Heights₂.Heights.Kleiman
