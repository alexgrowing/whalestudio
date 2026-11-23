import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace FlagRestrict

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo TensorProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (MRingOver (kap O) ι)} [Q.IsPrime]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V] {B : ChartBundle O (mseg x) N V}

theorem mseg_ne_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) : mseg x s ≠ 0 := by
  rw [← aeval_segForm (R := O)]
  exact aeval_ne_zero hPQ (isMultiHomog_segForm s) (red_segForm_notMem hs)

theorem isLocFrac_one : IsLocFrac O Q (1 : MRingOver O ι) 1 := by
  simpa using isLocFrac_C (Q := Q) (1 : O)

theorem smul_mem_stalk (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (ha : a ∈ locAlg x Q) {m : V}
    (hm : m ∈ stalk O x Q B) : a • m ∈ stalk O x Q B := by
  induction hm using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨F, G, hFG, s, hs, e, he, rfl⟩ := hv
    have h2 : a * (aeval x F / aeval x G) ∈ locAlg x Q := mul_mem ha (mem_locAlg hPQ hFG)
    obtain ⟨F', G', h', _, he'⟩ := mem_locAlg_iff.1 h2
    refine AddSubgroup.subset_closure ⟨F', G', h', s, hs, e, he, ?_⟩
    rw [smul_smul, he']
  | zero => rw [smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem lat_le_stalk {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) {e : V} (he : e ∈ B.lat s) :
    e ∈ stalk O x Q B :=
  AddSubgroup.subset_closure ⟨1, 1, isLocFrac_one, s, hs, e, he, by simp⟩

theorem resMap_apply (m : stalk O x Q B) :
    resMap O x Q B m = (Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B)).mkQ
      ((1 : FractionRing (MRingOver (kap O) ι ⧸ Q)) ⊗ₜ[ℤ] m) := rfl

theorem resMap_smul (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (ha : a ∈ locAlg x Q) (m : stalk O x Q B) :
    resMap O x Q B ⟨a • (m : V), smul_mem_stalk hPQ ha m.2⟩ = rs x Q a • resMap O x Q B m := by
  obtain ⟨F, G, hFG, _, rfl⟩ := mem_locAlg_iff.1 ha
  rw [rs_frac hPQ hFG]
  have hrel : resOf O Q F G ⊗ₜ[ℤ] m - (1 : FractionRing (MRingOver (kap O) ι ⧸ Q)) ⊗ₜ[ℤ]
      (⟨(aeval x F / aeval x G) • (m : V), smul_mem_stalk hPQ ha m.2⟩ : stalk O x Q B) ∈ resRel O x Q B :=
    ⟨F, G, hFG, m, _, rfl, rfl⟩
  have h0 := (Submodule.Quotient.mk_eq_zero
    (Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B))).2 (Submodule.subset_span hrel)
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h0
  rw [resMap_apply, resMap_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact h0.symm

theorem resMap_mem_resLat {s : ∀ k, ι k} {y : stalk O x Q B} (hy : (y : V) ∈ B.lat s) :
    resMap O x Q B y ∈ resLat O x Q B s :=
  AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_addSubgroupOf.2 hy)

theorem resLat_smul_mem (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (s : ∀ k, ι k)
    {c : FractionRing (MRingOver (kap O) ι ⧸ Q)} (hc : c ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s)
    {e : resFibre O x Q B} (he : e ∈ resLat O x Q B s) : c • e ∈ resLat O x Q B s := by
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 he
  rw [AddSubgroup.mem_addSubgroupOf] at hy
  obtain ⟨a, ha, ha', rfl⟩ := exists_lift hPQ s hc
  rw [← resMap_smul hPQ ha' y]
  exact resMap_mem_resLat (B.stable s a ha _ hy)

theorem resLat_overlap (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s t : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) (ht : mseg (genPt (kap O) Q) t ≠ 0) {e : resFibre O x Q B}
    (he : e ∈ resLat O x Q B s) : ∃ m : ℕ,
      (mseg (genPt (kap O) Q) s / mseg (genPt (kap O) Q) t) ^ m • e ∈ resLat O x Q B t := by
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 he
  rw [AddSubgroup.mem_addSubgroupOf] at hy
  obtain ⟨m, hm⟩ := B.overlap s t (mseg_ne_zero hPQ hs) (mseg_ne_zero hPQ ht) _ hy
  obtain ⟨h1, h2⟩ := seg_ratio (x := x) hPQ ht s
  refine ⟨m, ?_⟩
  rw [← h2, ← rs_pow hPQ h1, ← resMap_smul hPQ (pow_mem h1 m) y]
  exact resMap_mem_resLat hm

section Frame

variable (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) {f : Ω}
  (hf : f ∈ chartRing O (mseg x) s) (hf0 : rs x Q f ≠ 0) {b : Fin N → V}
  (hlat : ∀ e, (∃ n : ℕ, f ^ n • e ∈ B.lat s) ↔ ∃ a : Fin N → Ω,
    (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing O (mseg x) s) ∧ e = ∑ q, a q • b q)

include hPQ hs hf hf0 in
theorem inv_mem_locAlg : f⁻¹ ∈ locAlg x Q :=
  (inv_mem_of_rs_ne_zero hPQ (chartRing_sub hPQ hs hf).1 hf0).1

include hPQ hs hf hf0 in

theorem mem_locAlg_of_pow_mul {a : Ω} {n : ℕ} (ha : f ^ n * a ∈ chartRing O (mseg x) s) : a ∈ locAlg x Q := by
  have hf' : f ≠ 0 := ne_zero_of_rs_ne_zero hPQ hf0
  have e : a = f⁻¹ ^ n * (f ^ n * a) := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf', one_pow, one_mul]
  rw [e]
  exact mul_mem (pow_mem (inv_mem_locAlg hPQ hs hf hf0) n) (chartRing_sub hPQ hs ha).1

include hlat in
theorem frame_pow_mem (q : Fin N) : ∃ n : ℕ, f ^ n • b q ∈ B.lat s := by
  refine (hlat (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
  · rw [pow_zero, one_mul, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp [Pi.single_apply]

include hPQ hs hf hf0 hlat in

theorem frame_mem_stalk (q : Fin N) : b q ∈ stalk O x Q B := by
  obtain ⟨n, hn⟩ := frame_pow_mem hlat q
  have hf' : f ≠ 0 := ne_zero_of_rs_ne_zero hPQ hf0
  have e : b q = f⁻¹ ^ n • (f ^ n • b q) := by
    rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hf', one_pow, one_smul]
  rw [e]
  exact smul_mem_stalk hPQ (pow_mem (inv_mem_locAlg hPQ hs hf hf0) n) (lat_le_stalk hs hn)

include hPQ hs hf hf0 hlat in

theorem stalk_coords {m : V} (hm : m ∈ stalk O x Q B) :
    ∃ a : Fin N → Ω, (∀ q, a q ∈ locAlg x Q) ∧ m = ∑ q, a q • b q := by
  induction hm using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨F, G, hFG, t, ht, e, he, rfl⟩ := hv
    have hxt := mseg_ne_zero hPQ ht
    have hxs := mseg_ne_zero hPQ hs
    obtain ⟨k, hk⟩ := B.overlap t s hxt hxs e he
    obtain ⟨a, ha, hae⟩ := (hlat _).1 ⟨0, by simpa using hk⟩
    have ha' : ∀ q, a q ∈ locAlg x Q := fun q => by
      obtain ⟨n, hn⟩ := ha q
      exact mem_locAlg_of_pow_mul hPQ hs hf hf0 hn
    have hr : aeval x F / aeval x G * (mseg x s / mseg x t) ^ k ∈ locAlg x Q :=
      mul_mem (mem_locAlg hPQ hFG) (pow_mem (seg_ratio hPQ ht s).1 k)
    refine ⟨fun q => aeval x F / aeval x G * (mseg x s / mseg x t) ^ k * a q,
      fun q => mul_mem hr (ha' q), ?_⟩
    have he' : e = (mseg x s / mseg x t) ^ k • ∑ q, a q • b q := by
      rw [← hae, smul_smul, ← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero hxt hxs),
        one_pow, one_smul]
    rw [he', Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [smul_smul, mul_assoc]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨a', ha', rfl⟩ := hv
    exact ⟨a + a', fun q => add_mem (ha q) (ha' q), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg u _ hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact ⟨-a, fun q => neg_mem (ha q), by simp [neg_smul, Finset.sum_neg_distrib]⟩

include hPQ hs hf hf0 hlat in

theorem resMap_sum {a : Fin N → Ω} (ha : ∀ q, a q ∈ locAlg x Q) (m : stalk O x Q B)
    (hm : (m : V) = ∑ q, a q • b q) :
    resMap O x Q B m = ∑ q, rs x Q (a q) • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩ := by
  have e : m = ∑ q, (⟨a q • b q, smul_mem_stalk hPQ (ha q) (frame_mem_stalk hPQ hs hf hf0 hlat q)⟩ :
      stalk O x Q B) := by
    apply Subtype.ext
    rw [hm, AddSubmonoidClass.coe_finset_sum]
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun q _ => resMap_smul hPQ (ha q) ⟨b q, _⟩

include hPQ hs hf hf0 hlat in

theorem exists_coordMap (bas : Module.Basis (Fin N) Ω V) (hbas : ∀ q, bas q = b q) :
    ∃ φ : resFibre O x Q B →ₗ[FractionRing (MRingOver (kap O) ι ⧸ Q)]
        (Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q)),
      ∀ m : stalk O x Q B, φ (resMap O x Q B m) = fun q => rs x Q (bas.equivFun m q) := by
  have hmem : ∀ (m : stalk O x Q B) q, bas.equivFun m q ∈ locAlg x Q := by
    intro m q
    obtain ⟨a, ha, hm⟩ := stalk_coords hPQ hs hf hf0 hlat m.2
    have : bas.equivFun m = a := by
      rw [hm, show ∑ q, a q • b q = bas.equivFun.symm a by
        rw [Module.Basis.equivFun_symm_apply]; simp only [hbas], LinearEquiv.apply_symm_apply]
    rw [this]
    exact ha q
  let ψ : stalk O x Q B →+ (Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q)) :=
    { toFun := fun m q => rs x Q (bas.equivFun m q)
      map_zero' := by funext q; simp [rs_zero hPQ]
      map_add' := fun m m' => by
        funext q
        simp only [AddSubgroup.coe_add, map_add, Pi.add_apply]
        exact rs_add hPQ (hmem m q) (hmem m' q) }
  let Φ₀ : FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B →ₗ[ℤ]
      (Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q)) :=
    TensorProduct.lift (LinearMap.mk₂ ℤ (fun r m => r • ψ m) (fun r r' m => add_smul r r' (ψ m))
      (fun c r m => smul_assoc c r (ψ m)) (fun r m m' => by rw [map_add, smul_add])
      (fun c r m => by rw [map_zsmul, smul_comm]))
  have hΦ₀ : ∀ r m, Φ₀ (r ⊗ₜ m) = r • ψ m := fun r m => TensorProduct.lift.tmul r m
  let Φ : FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B →ₗ[FractionRing (MRingOver (kap O) ι ⧸ Q)]
      (Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q)) :=
    { toFun := Φ₀
      map_add' := map_add Φ₀
      map_smul' := fun c t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul r m => rw [TensorProduct.smul_tmul', hΦ₀, hΦ₀, smul_eq_mul, mul_smul]; rfl
        | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add] }
  have hΦ : ∀ r m, Φ (r ⊗ₜ m) = r • ψ m := hΦ₀
  have hker : Submodule.span _ (resRel O x Q B) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨F, G, hFG, m, m', hm', rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦ, one_smul]
    rw [sub_eq_zero]
    funext q
    change resOf O Q F G * rs x Q (bas.equivFun m q) = rs x Q (bas.equivFun m' q)
    rw [hm', map_smul, Pi.smul_apply, smul_eq_mul, rs_mul hPQ (mem_locAlg hPQ hFG) (hmem m q), rs_frac hPQ hFG]
  refine ⟨(Submodule.span _ (resRel O x Q B)).liftQ Φ hker, fun m => ?_⟩
  rw [resMap_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, hΦ, one_smul]
  rfl

include hPQ hs hf hf0 hlat in

theorem frame_res_basis (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent (FractionRing (MRingOver (kap O) ι ⧸ Q))
        (fun q => resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) ∧
      Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q))
        (Set.range fun q => resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) = ⊤ := by
  let bas : Module.Basis (Fin N) Ω V := Module.Basis.mk hb (by rw [hsp])
  have hbas : ∀ q, bas q = b q := fun q => Module.Basis.mk_apply _ _ q
  obtain ⟨φ, hφ⟩ := exists_coordMap hPQ hs hf hf0 hlat bas hbas
  constructor
  · apply LinearIndependent.of_comp φ
    have e : ∀ q q', φ (resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) q' =
        Pi.basisFun (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Fin N) q q' := by
      intro q q'
      rw [hφ, Pi.basisFun_apply]
      have h1 : bas.equivFun (b q) q' = Pi.single (M := fun _ => Ω) q 1 q' := by
        rw [← hbas q, Module.Basis.equivFun_self]
        simp [Pi.single_apply, eq_comm]
      change rs x Q (bas.equivFun (b q) q') = _
      rw [h1, Pi.single_apply, Pi.single_apply]
      split_ifs
      · exact rs_one hPQ
      · exact rs_zero hPQ
    have e' : φ ∘ (fun q => resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) =
        Pi.basisFun (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Fin N) := by
      funext q q'
      exact e q q'
    rw [e']
    exact (Pi.basisFun _ _).linearIndependent
  · refine Submodule.eq_top_iff'.2 fun z => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    induction t using TensorProduct.induction_on with
    | zero => rw [Submodule.Quotient.mk_zero]; exact zero_mem _
    | tmul r m =>
      have e : (Submodule.Quotient.mk (r ⊗ₜ[ℤ] m) : resFibre O x Q B) = r • resMap O x Q B m := by
        rw [resMap_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
      rw [e]
      refine Submodule.smul_mem _ r ?_
      obtain ⟨a, ha, hm⟩ := stalk_coords hPQ hs hf hf0 hlat m.2
      rw [resMap_sum hPQ hs hf hf0 hlat ha m hm]
      exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    | add u v hu hv => rw [Submodule.Quotient.mk_add]; exact add_mem hu hv

include hPQ hs hf hf0 hlat in

theorem frame_res_lat (e : resFibre O x Q B) :
    (∃ n : ℕ, rs x Q f ^ n • e ∈ resLat O x Q B s) ↔
      ∃ a : Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q),
        (∀ q, ∃ n : ℕ, rs x Q f ^ n * a q ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧
          e = ∑ q, a q • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩ := by
  have hfl : f ∈ locAlg x Q := (chartRing_sub hPQ hs hf).1
  have hfc : rs x Q f ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s := (chartRing_sub hPQ hs hf).2
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨y, hy, hye⟩ := AddSubgroup.mem_map.1 hn
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    obtain ⟨a, ha, hya⟩ := (hlat y).1 ⟨0, by simpa using hy⟩
    have ha' : ∀ q, a q ∈ locAlg x Q := fun q => by
      obtain ⟨n, hn⟩ := ha q
      exact mem_locAlg_of_pow_mul hPQ hs hf hf0 hn
    have hpow : rs x Q f ^ n ≠ 0 := pow_ne_zero _ hf0
    refine ⟨fun q => (rs x Q f ^ n)⁻¹ * rs x Q (a q), fun q => ?_, ?_⟩
    · obtain ⟨n', hn'⟩ := ha q
      refine ⟨n + n', ?_⟩
      rw [pow_add, mul_assoc, mul_comm (rs x Q f ^ n'), mul_assoc, ← mul_assoc (rs x Q f ^ n),
        mul_inv_cancel₀ hpow, one_mul, ← rs_pow hPQ hfl, ← rs_mul hPQ (ha' q) (pow_mem hfl n'), mul_comm]
      exact (chartRing_sub hPQ hs hn').2
    · have h1 : rs x Q f ^ n • e = ∑ q, rs x Q (a q) • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩ := by
        rw [← hye]
        exact resMap_sum hPQ hs hf hf0 hlat ha' y hya
      calc e = (rs x Q f ^ n)⁻¹ • (rs x Q f ^ n • e) := by rw [smul_smul, inv_mul_cancel₀ hpow, one_smul]
        _ = _ := by rw [h1, Finset.smul_sum]; simp only [smul_smul]
  · rintro ⟨a, ha, rfl⟩
    let Sat : AddSubgroup (resFibre O x Q B) :=
      { carrier := {e | ∃ n : ℕ, rs x Q f ^ n • e ∈ resLat O x Q B s}
        zero_mem' := ⟨0, by simp⟩
        add_mem' := by
          rintro e e' ⟨n, hn⟩ ⟨n', hn'⟩
          refine ⟨n + n', ?_⟩
          rw [smul_add, pow_add]
          refine add_mem ?_ ?_
          · rw [mul_comm, mul_smul]
            exact resLat_smul_mem hPQ s (pow_mem hfc n') hn
          · rw [mul_smul]
            exact resLat_smul_mem hPQ s (pow_mem hfc n) hn'
        neg_mem' := by
          rintro e ⟨n, hn⟩
          exact ⟨n, by rw [smul_neg]; exact neg_mem hn⟩ }
    change _ ∈ Sat
    refine sum_mem fun q _ => ?_
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨k, hk⟩ := frame_pow_mem hlat q
    refine ⟨n + k, ?_⟩
    have h2 : rs x Q f ^ k • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩ ∈ resLat O x Q B s := by
      rw [← rs_pow hPQ hfl, ← resMap_smul hPQ (pow_mem hfl k)]
      exact resMap_mem_resLat hk
    have e : rs x Q f ^ (n + k) • (a q • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) =
        (rs x Q f ^ n * a q) • (rs x Q f ^ k • resMap O x Q B ⟨b q, frame_mem_stalk hPQ hs hf hf0 hlat q⟩) := by
      rw [smul_smul, smul_smul, pow_add]
      ring_nf
    rw [e]
    exact resLat_smul_mem hPQ s hn h2

end Frame

end FlagRestrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
