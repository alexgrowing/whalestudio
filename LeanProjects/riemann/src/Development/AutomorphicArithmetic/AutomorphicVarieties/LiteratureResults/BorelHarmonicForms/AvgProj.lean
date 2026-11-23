import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem avg_abs {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V)
    (h : ∀ v, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρ n v = v) :
    ∃ p : Module.End ℂ V, (∀ v u, ρ u (p v) = p v) ∧ (∀ v, (∀ u, ρ u v = v) → p v = v) ∧
      ∀ T : Module.End ℂ V, (∀ u, Commute T (ρ u)) → Commute T p := by
  classical
  obtain ⟨avg, havg⟩ : ∃ avg : Subgroup K → Module.End ℂ V,
      ∀ N, avg N = (N.index : ℂ)⁻¹ • ∑ᶠ q : K ⧸ N, ρ q.out := ⟨_, fun _ => rfl⟩
  have hform : ∀ (N : Subgroup K) [Fintype (K ⧸ N)] (v : V),
      avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, ρ q.out v := by
    intro N _ v
    rw [havg, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : ∀ (N : Subgroup K) [N.FiniteIndex] [Fintype (K ⧸ N)],
      (Fintype.card (K ⧸ N) : ℂ) = N.index ∧ (N.index : ℂ) ≠ 0 := by
    intro N _ _
    refine ⟨by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card], ?_⟩
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hlift : ∀ (N : Subgroup K) (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ g : K, ρ ((g : K ⧸ N).out) v = ρ g v := by
    intro N v hv g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
    rw [hn, map_mul, Module.End.mul_apply, hv _ n.2]
  have hconj : ∀ (N : Subgroup K) [N.Normal] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, ∀ n ∈ N, ρ n (ρ k v) = ρ k v := by
    intro N hN v hv k n hn
    have h1 : k⁻¹ * n * k ∈ N := by
      simpa using hN.conj_mem n hn k⁻¹
    have h2 : n * k = k * (k⁻¹ * n * k) := by group
    rw [← Module.End.mul_apply, ← map_mul, h2, map_mul, Module.End.mul_apply, hv _ h1]
  have hinv : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ u : K, ρ u (avg N v) = avg N v := by
    intro N _ _ v hv u
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N v, map_smul, map_sum]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ u (ρ q.out v) = ρ ((u • q).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N v hv, MulAction.Quotient.smul_mk, hlift N v hv, smul_eq_mul, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (MulAction.toPerm u) (fun q : K ⧸ N => ρ q.out v)
  have hfixed : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), (∀ u, ρ u v = v) → avg N v = v := by
    intro N _ v hv
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N v]
    simp only [hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
  have hshift : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      ∀ k : K, avg N (ρ k v) = avg N v := by
    intro N _ _ v hv k
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N (ρ k v), hform N v]
    congr 1
    have hq : ∀ q : K ⧸ N, ρ q.out (ρ k v) = ρ ((q * (k : K ⧸ N)).out) v := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [hlift N _ (hconj N v hv k), ← QuotientGroup.mk_mul, hlift N v hv, map_mul,
          Module.End.mul_apply]
    simp only [hq]
    exact Equiv.sum_comp (Equiv.mulRight (k : K ⧸ N)) (fun q : K ⧸ N => ρ q.out v)
  let A : Submodule ℂ V := Submodule.span ℂ {x | ∃ k u, ρ k u - u = x}
  have hdiff : ∀ (N : Subgroup K) [N.FiniteIndex] (v : V), v - avg N v ∈ A := by
    intro N _ v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    have e : v - avg N v = (N.index : ℂ)⁻¹ • ∑ q : K ⧸ N, (v - ρ q.out v) := by
      rw [hform N v, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, (hcard N).1, inv_mul_cancel₀ (hcard N).2, one_smul]
    rw [e]
    refine A.smul_mem _ (A.sum_mem fun q _ => ?_)
    rw [← neg_sub]
    exact A.neg_mem (Submodule.subset_span ⟨q.out, v, rfl⟩)
  have hcomm : ∀ (N : Subgroup K) [N.FiniteIndex] (T : Module.End ℂ V),
      (∀ u, Commute T (ρ u)) → ∀ v, T (avg N v) = avg N (T v) := by
    intro N _ T hT v
    letI : Fintype (K ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
    rw [hform N v, hform N (T v), map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Module.End.mul_apply, (hT q.out).eq, Module.End.mul_apply]
  have hkill : ∀ a ∈ A, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧
      ∀ N' : Subgroup K, N'.Normal → N'.FiniteIndex → N' ≤ N →
        (∀ n ∈ N', ρ n a = a) ∧ avg N' a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, u, rfl⟩ := hx
      obtain ⟨N, hN, hNf, hu⟩ := h u
      refine ⟨N, hN, hNf, fun N' hN' hN'f hle => ?_⟩
      have hu' : ∀ n ∈ N', ρ n u = u := fun n hn => hu n (hle hn)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_sub, hconj N' u hu' k n hn, hu' n hn]
      · rw [map_sub, hshift N' u hu' k, sub_self]
    | zero =>
      refine ⟨⊤, inferInstance, inferInstance, fun N' _ _ _ => ⟨fun n _ => map_zero _, map_zero _⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      obtain ⟨N2, h2n, h2f, h2⟩ := hy
      refine ⟨N1 ⊓ N2, inferInstance, inferInstance, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f (hle.trans inf_le_left)
      obtain ⟨a2, b2⟩ := h2 N' hN' hN'f (hle.trans inf_le_right)
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_add, a1 n hn, a2 n hn]
      · rw [map_add, b1, b2, add_zero]
    | smul c x _ hx =>
      obtain ⟨N1, h1n, h1f, h1⟩ := hx
      refine ⟨N1, h1n, h1f, fun N' hN' hN'f hle => ?_⟩
      obtain ⟨a1, b1⟩ := h1 N' hN' hN'f hle
      refine ⟨fun n hn => ?_, ?_⟩
      · rw [map_smul, a1 n hn]
      · rw [map_smul, b1, smul_zero]
  have hzero : ∀ w ∈ A, (∀ u, ρ u w = w) → w = 0 := by
    intro w hw hfix
    obtain ⟨N, hN, hNf, hN'⟩ := hkill w hw
    rw [← hfixed N w hfix]
    exact (hN' N hN hNf le_rfl).2
  choose Nv hNv hNvf hNvfix using h
  let pf : V → V := fun v => avg (Nv v) v
  have hagree : ∀ (N : Subgroup K) [N.Normal] [N.FiniteIndex] (v : V), (∀ n ∈ N, ρ n v = v) →
      avg N v = pf v := by
    intro N _ _ v hv
    haveI := hNv v
    haveI := hNvf v
    rw [← sub_eq_zero]
    apply hzero
    · have e : avg N v - pf v = (v - pf v) - (v - avg N v) := by abel
      rw [e]
      exact A.sub_mem (hdiff _ v) (hdiff N v)
    · intro u
      rw [map_sub, hinv N v hv u, hinv (Nv v) v (hNvfix v) u]
  let p : Module.End ℂ V :=
    { toFun := pf
      map_add' := fun v w => by
        haveI := hNv v; haveI := hNvf v; haveI := hNv w; haveI := hNvf w
        have hv : ∀ n ∈ Nv v ⊓ Nv w, ρ n v = v := fun n hn => hNvfix v n hn.1
        have hw : ∀ n ∈ Nv v ⊓ Nv w, ρ n w = w := fun n hn => hNvfix w n hn.2
        have hvw : ∀ n ∈ Nv v ⊓ Nv w, ρ n (v + w) = v + w := fun n hn => by
          rw [map_add, hv n hn, hw n hn]
        rw [← hagree _ _ hvw, ← hagree _ _ hv, ← hagree _ _ hw, map_add]
      map_smul' := fun c v => by
        haveI := hNv v; haveI := hNvf v
        have hcv : ∀ n ∈ Nv v, ρ n (c • v) = c • v := fun n hn => by
          rw [map_smul, hNvfix v n hn]
        rw [RingHom.id_apply, ← hagree _ _ hcv, map_smul] }
  refine ⟨p, fun v u => ?_, fun v hv => ?_, fun T hT => ?_⟩
  · haveI := hNv v; haveI := hNvf v
    exact hinv (Nv v) v (hNvfix v) u
  · haveI := hNvf v
    exact hfixed (Nv v) v hv
  · refine LinearMap.ext fun v => ?_
    haveI := hNv v; haveI := hNvf v
    have hTv : ∀ n ∈ Nv v, ρ n (T v) = T v := fun n hn => by
      rw [← Module.End.mul_apply, ← (hT n).eq, Module.End.mul_apply, hNvfix v n hn]
    show T (pf v) = pf (T v)
    rw [← hagree (Nv v) (T v) hTv]
    exact hcomm (Nv v) T hT v

theorem UpperTheory.V.Lit.Bor.avgProj :
    UpperTheory.V.Lit.Bor.AvgProj := by
  intro G V _ _ _ _ _ ρ U hU hopen
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let ρU : Representation ℂ U V := ρ.comp U.subtype
  have h : ∀ v, ∃ N : Subgroup U, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρU n v = v := by
    intro v
    let S : Subgroup U :=
      { carrier := {u | ρ (u : G) v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set U) := (hopen v).preimage continuous_subtype_val
    haveI : Finite (U ⧸ S) := Subgroup.quotient_finite_of_isOpen S hS
    haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact ⟨S.normalCore, inferInstance, inferInstance, fun n hn => S.normalCore_le hn⟩
  obtain ⟨p, h1, h2, h3⟩ := avg_abs ρU h
  exact ⟨p, fun v u hu => h1 v ⟨u, hu⟩, fun v hv => h2 v (fun u => hv u u.2),
    fun T hT => h3 T (fun u => hT u u.2)⟩
