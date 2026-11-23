import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem linearIndependent_laurentMonomials {k F ι : Type} [Field k] [Field F] [Algebra k F]
    [Fintype ι] (y : ι → F) (hy : AlgebraicIndependent k y) (hy0 : ∀ i, y i ≠ 0) :
    LinearIndependent k (fun n : ι → ℤ => ∏ i, y i ^ n i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg n hn
  set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef
  have hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B := by
    intro m hm i
    have h1 : |m i| ≤ ∑ i, |m i| :=
      Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |m i| ≤ B :=
      Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|)
        (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm
    linarith [neg_abs_le (m i)]
  let e : (ι → ℤ) → (ι →₀ ℕ) := fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)
  have he : Set.InjOn e s := by
    intro m hm m' hm' h
    funext i
    have h' := congrArg (fun f : ι →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h'
    have := Int.toNat_of_nonneg (hB m hm i)
    have := Int.toNat_of_nonneg (hB m' hm' i)
    omega
  set P : F := ∏ i, y i ^ B with hPdef
  have hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) =
      P * ∏ i, y i ^ m i := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add₀ (hy0 i), ← zpow_natCast]
    congr 1
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rw [Int.toNat_of_nonneg (hB m hm i)]
    ring
  have hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k))) := by
    have := (MvPolynomial.basisMonomials ι k).linearIndependent.map'
      (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply] using this
  have hws : LinearIndependent k
      (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))) :=
    hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))
  rw [Fintype.linearIndependent_iff] at hws
  refine hws (fun m => g m) ?_ ⟨n, hn⟩
  calc ∑ m : s, g m • MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))
      = ∑ m : s, P * (g m • ∏ i, y i ^ (m : ι → ℤ) i) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hkey m m.2, mul_smul_comm]
    _ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]
    _ = 0 := by rw [hg, mul_zero]

open KaehlerDifferential in
private theorem prod_zpow_eq_prod_div_zpow_of_sum_eq_zero {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (m : Fin (d + 1) → ℤ) (hm : ∑ j, m j = 0) :
    ∏ j, x j ^ m j = ∏ i : Fin d, (x i.succ / x 0) ^ m i.succ := by
  have h0 : m 0 = -∑ i : Fin d, m i.succ := by
    rw [Fin.sum_univ_succ] at hm
    linarith
  have hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]
  rw [Fin.prod_univ_succ, h0]
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]

open KaehlerDifferential in

theorem _root_.GlobalTheory.exists_isRes : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    _root_.GlobalTheory.PD.IsPd k x → ∃ ρ : F →ₗ[k] k, _root_.GlobalTheory.PD.IsRes k x ρ := by
  intro k _ F _ _ d x hx
  classical
  let v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F := fun m => ∏ j, x j ^ m.1 j
  have hv : LinearIndependent k v := by
    have hL := linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0)
      hx.indep
      (fun i => div_ne_zero (hx.ne _) (hx.ne 0))
    have hinj : Function.Injective
        (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ) := by
      intro a b h
      apply Subtype.ext
      have hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ := fun i => congrFun h i
      have ha := a.2
      have hb := b.2
      rw [Fin.sum_univ_succ] at ha hb
      have hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ :=
        Finset.sum_congr rfl fun i _ => hs i
      funext j
      refine Fin.cases ?_ (fun i => hs i) j
      linarith
    have := hL.comp _ hinj
    convert this using 1
    funext m
    exact prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2
  let z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} := ⟨0, by simp⟩
  have h1 : v z₀ = 1 := by simp [v, z₀]
  have hnot := hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)
  rw [h1] at hnot
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_⟩
  delta _root_.GlobalTheory.PD.IsRes
  refine ⟨?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]
  · intro m hm hm0
    have hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀}) :=
      Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩
    have hzero : f (∏ j, x j ^ m j) = 0 := by
      exact LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)
    rw [LinearMap.smul_apply, hzero, smul_zero]

end GlobalTheory
