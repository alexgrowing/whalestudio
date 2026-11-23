import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsZeroIdealChart
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ZeroIdealChartAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def chartUnion (I K : Chart x) : Chart x :=
  ⟨I.1 ∪ K.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 K.2.2⟩

theorem monos_union_split {I K : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos (I ∪ K)) :
    ∃ u ∈ monos (S := S) I, ∃ v ∈ monos (S := S) K, u * v = s := by
  unfold monos at hs
  rw [Finset.coe_union, Set.image_union, Submonoid.closure_union, Submonoid.mem_sup] at hs
  exact hs

theorem aeval_mem_twistMod {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (K : Chart x) :
    aeval x f ∈ twistMod S x (e : ℤ) K :=
  Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp, by simp⟩

theorem exists_monos_mul_mem_twistMod (I K : Chart x) (b : Ω)
    (hb : b ∈ chartRing S x (chartUnion I K)) :
    ∃ u ∈ monos (S := S) I.1, ∃ d : ℕ, u.IsHomogeneous d ∧ aeval x u * b ∈ twistMod S x (d : ℤ) K := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hb
  obtain ⟨u, hu, v, hv, rfl⟩ := monos_union_split hs
  obtain ⟨du, hdu⟩ := monos_isHomogeneous hu
  obtain ⟨dv, hdv⟩ := monos_isHomogeneous hv
  have huv0 := eval_ne_zero_of_mem_monos (chartUnion I K) hs
  have hu0 := eval_ne_zero_of_mem_monos I hu
  have hv0 := eval_ne_zero_of_mem_monos K hv
  have he : du + dv = e := (hdu.mul hdv).inj_right hse (fun h => huv0 (by rw [h, map_zero]))
  refine ⟨u, hu, du, hdu, Submodule.subset_span ⟨f, v, dv, e, hv, hf, hdv, by omega, ?_⟩⟩
  rw [map_mul]
  field_simp

theorem twistMod_mul_mem {K : Chart x} {a b : Ω} {c c' : ℤ} (ha : a ∈ twistMod S x c K)
    (hb : b ∈ twistMod S x c' K) : a * b ∈ twistMod S x (c + c') K := by
  have h := Submodule.mul_mem_mul (M := (twistSys S x c).sub K) (N := (twistSys S x c').sub K) ha hb
  rw [twistSys_sub_mul] at h
  exact h

theorem mul_mem_chartRing_union (D : SubFamily S x Ω) (I K : Chart x) (y : Ω)
    (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∀ δ ∈ D.sub (chartUnion I K), y * δ ∈ chartRing S x (chartUnion I K) := by
  intro δ hδ
  obtain ⟨a, ⟨w, hw⟩, haδ⟩ := (D.mem_iff I (chartUnion I K) Finset.subset_union_left δ).mp hδ
  have hinv : ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul w)
    rw [hw] at this
    exact this
  have h1 : y * ((a : Ω) • δ) ∈ chartRing S x (chartUnion I K) :=
    chartRing_mono Finset.subset_union_left (hy _ haδ)
  have h2 : y * δ = ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (y * ((a : Ω) • δ)) := by
    rw [smul_eq_mul, mul_left_comm y, ← mul_assoc, hinv, one_mul]
  rw [h2]
  exact mul_mem (w⁻¹ : (chartRing S x (chartUnion I K))ˣ).1.2 h1

end ZeroIdealChartAux

theorem ZeroIdealChart.proof : ZeroIdealChart.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T I y hy
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul T.M T.p (T.m - T.c₁)
  have hLD : L.toSubSystem = T.D := hL
  have hsub : ∀ K, T.D.sub K = L.sub K := fun K => by rw [← hLD]

  have hsi : T.si ∈ T.D.sub I := (Submodule.mem_iInf _).mp T.si_mem I
  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy _ hsi
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * T.si * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyL : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := fun δ hδ => hy δ (by rw [hsub]; exact hδ)
  have hyU := mul_mem_chartRing_union L.toSubFamily I

  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing k x (chartUnion I p.1) := fun p =>
    hyU p.1 y hyL _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := k) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly k N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := k) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod k x (dU : ℤ) p.1 := by
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
  have hUK : ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod k x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ T.J := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ (by rw [← hsub]; exact hδ))
    · rw [map_mul, ← hfz]
      ring

  refine Submodule.subset_span ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end

end GroundTheory.Heights₂.Heights.Kleiman
