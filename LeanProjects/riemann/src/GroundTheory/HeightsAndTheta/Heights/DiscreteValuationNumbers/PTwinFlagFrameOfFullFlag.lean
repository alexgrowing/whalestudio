import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)

namespace FlagFrameOfFullFlag

theorem flag_eq_span {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    [FiniteDimensional Ω E] {N : ℕ} (Vs : Fin (N + 1) → Submodule Ω E) (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (b : Fin N → E) (hb : LinearIndependent Ω b)
    (hmem : ∀ q, b q ∈ Vs q.succ) (j : Fin (N + 1)) :
    Vs j = Submodule.span Ω (b '' {q | (q : ℕ) < j}) := by
  have hj : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  have himg : b '' {q | (q : ℕ) < j} = Set.range (b ∘ Fin.castLE hj) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨Fin.castLE hj p, p.isLt, rfl⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q.succ ≤ j := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ]
      exact hq
    exact mono hq' (hmem q)
  · rw [himg, finrank_span_eq_card (hb.comp _ (Fin.castLE_injective hj)), Fintype.card_fin, dim]

theorem ideal_eq_top {R : Type*} [CommRing R] {k : ℕ} (f c : Fin k → R)
    (hsum : ∑ l, c l * f l = 1) (J : Ideal R) (hJ : ∀ l, ∃ n : ℕ, f l ^ n ∈ J) : J = ⊤ := by
  choose n hn using hJ
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan (∑ l, n l), Ideal.span_le]
  rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
  have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  show f l ^ (∑ l, n l) ∈ J
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact J.mul_mem_right _ (hn l)

theorem mem_of_pow_mul_mem {F Ω : Type*} [CommRing F] [Field Ω] [Algebra F Ω] (S : Subalgebra F Ω)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ S) (hc : ∀ l, c l ∈ S) (hsum : ∑ l, c l * f l = 1)
    (a : Ω) (ha : ∀ l, ∃ n : ℕ, f l ^ n * a ∈ S) : a ∈ S := by
  let J : Ideal S :=
    { carrier := {r | (r : Ω) * a ∈ S}
      add_mem' := fun {r t} hr ht => by
        simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul] at hr ht ⊢
        exact add_mem hr ht
      zero_mem' := by simp
      smul_mem' := fun r t ht => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at ht ⊢
        exact mul_mem r.2 ht }
  have hJ : J = ⊤ := by
    refine ideal_eq_top (fun l => (⟨f l, hf l⟩ : S)) (fun l => ⟨c l, hc l⟩) ?_ J ?_
    · apply Subtype.ext
      simpa using hsum
    · intro l
      obtain ⟨n, hn⟩ := ha l
      exact ⟨n, by simpa [J] using hn⟩
  have h1 : (1 : S) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

end FlagFrameOfFullFlag

open FlagFrameOfFullFlag in

theorem FlagFrameOfFullFlag.proof : FlagFrameOfFullFlag.Statement := by
  intro F _ Ω _ _ K _ ι _ x e hV N E _ _ B fl

  have hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show _ ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, h0]
  choose s0 hs0 using hx
  have hseg : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x s0 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hs0 k
  obtain ⟨k0, f0, c0, -, -, hsum0, hfr0⟩ := fl.frame s0 hseg
  have hk : 0 < k0 := by
    rcases Nat.eq_zero_or_pos k0 with h | h
    · subst h
      simp at hsum0
    · exact h
  obtain ⟨b0, hb0li, hb0sp, -, hb0tri⟩ := hfr0 ⟨0, hk⟩
  choose u0 hu0 using hb0tri
  have : FiniteDimensional Ω E :=
    Module.Finite.of_basis (Module.Basis.mk hb0li hb0sp.ge)

  have tri_mem : ∀ (b : Fin N → E) (u : Fin N → Ω),
      (∀ q, b q - u q • fl.gen q ∈ fl.Vs q.castSucc) → ∀ q, b q ∈ fl.Vs q.succ := by
    intro b u h q
    have h1 : fl.Vs q.castSucc ≤ fl.Vs q.succ := fl.mono (Fin.castSucc_le_succ q)
    have h2 := add_mem (h1 (h q)) (Submodule.smul_mem _ (u q) (fl.gen_mem q))
    simpa using h2
  have hVb0 := flag_eq_span fl.Vs fl.mono fl.dim b0 hb0li
    (tri_mem b0 _ fun q => (hu0 q).2)

  have hgen_sp : ∀ n : ℕ, ∀ q : Fin N, (q : ℕ) = n →
      b0 q ∈ Submodule.span Ω (Set.range fl.gen) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hq
      have h1 : b0 q - (u0 q * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x s0 (fl.deg q)) • fl.gen q ∈
          Submodule.span Ω (Set.range fl.gen) := by
        have h := (hu0 q).2
        rw [hVb0 q.castSucc] at h
        refine Submodule.span_le.mpr ?_ h
        rintro _ ⟨p, hp, rfl⟩
        simp only [Set.mem_ofPred_eq, Fin.val_castSucc] at hp
        exact ih p (by omega) p rfl
      have h2 := add_mem h1 (Submodule.smul_mem _
        (u0 q * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x s0 (fl.deg q))
        (Submodule.subset_span (⟨q, rfl⟩ : fl.gen q ∈ Set.range fl.gen)))
      simpa using h2
  have hgen_top : ⊤ ≤ Submodule.span Ω (Set.range fl.gen) := by
    rw [← hb0sp, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact hgen_sp q q rfl
  have hfin : Module.finrank Ω E = N := by
    rw [← finrank_top Ω E, ← fl.top, fl.dim, Fin.val_last]
  have hgen_li : LinearIndependent Ω fl.gen :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hgen_top (by simp [hfin])
  let w := Module.Basis.mk hgen_li hgen_top
  have hw : ⇑w = fl.gen := Module.Basis.coe_mk _ _
  have hVw : ∀ j, fl.Vs j = Submodule.span Ω (w '' {q | (q : ℕ) < j}) := by
    intro j
    rw [hw]
    exact flag_eq_span fl.Vs fl.mono fl.dim fl.gen hgen_li fl.gen_mem j

  have hmemV : ∀ (j : Fin (N + 1)) (v : E),
      v ∈ fl.Vs j ↔ ∀ q : Fin N, (j : ℕ) ≤ q → w.repr v q = 0 := by
    intro j v
    rw [hVw j, Module.Basis.mem_span_image]
    constructor
    · intro h q hq
      by_contra hne
      have h' := h (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
      simp only [Set.mem_ofPred_eq] at h'
      omega
    · intro h q hq
      simp only [Set.mem_ofPred_eq]
      by_contra hlt
      exact (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hq)) (h q (by omega))
  have hgw : ∀ q, w.repr (fl.gen q) = Finsupp.single q 1 := by
    intro q
    rw [← hw]
    exact w.repr_self q

  have repr_tri : ∀ (b : Fin N → E) (u M : Fin N → Ω),
      (∀ q, b q - (u q * M q) • fl.gen q ∈ fl.Vs q.castSucc) →
      ∀ q, w.repr (b q) q = u q * M q ∧ ∀ j, q < j → w.repr (b q) j = 0 := by
    intro b u M h q
    have h1 := (hmemV q.castSucc _).mp (h q) q (by simp)
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hgw, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, sub_eq_zero] at h1
    refine ⟨h1, fun j hj => (hmemV q.succ _).mp (tri_mem b (fun q => u q * M q) h q) j ?_⟩
    rw [Fin.val_succ]
    exact hj
  refine ⟨w, ⟨fun c hc i => ?_⟩⟩
  obtain ⟨k, f, cc, hf, hcc, hsum, hfr⟩ := fl.frame c hc
  have hM0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ ?_
    exact Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  ext y
  constructor
  ·
    rintro ⟨v, hv, hvj, rfl⟩
    refine ⟨w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i), ?_,
      (div_mul_cancel₀ _ hM0).symm⟩
    refine mem_of_pow_mul_mem _ f cc hf hcc hsum _ fun l => ?_
    obtain ⟨b, hbli, hbsp, hcrit, htri⟩ := hfr l
    choose u hu using htri
    obtain ⟨a, ha, hva⟩ := (hcrit v).mp ⟨0, by simpa using hv⟩
    have hvV : v ∈ fl.Vs i.succ := (hmemV _ v).mpr fun q hq => hvj q (by
      rw [Fin.val_succ] at hq
      exact hq)
    let β := Module.Basis.mk hbli hbsp.ge
    have hβ : ⇑β = b := Module.Basis.coe_mk _ _
    have hVβ := flag_eq_span fl.Vs fl.mono fl.dim b hbli (tri_mem b _ fun q => (hu q).2) i.succ
    have haβ : ⇑(β.repr v) = a := by
      have hsumβ : (∑ q, a q • b q) = ∑ q, a q • β q := by rw [hβ]
      rw [hva, hsumβ]
      exact β.repr_sum_self a
    have ha0 : ∀ q, i < q → a q = 0 := by
      intro q hq
      rw [hVβ, ← hβ, Module.Basis.mem_span_image] at hvV
      by_contra hne
      have h' := hvV (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by rw [haβ]; exact hne)))
      simp only [Set.mem_ofPred_eq, Fin.val_succ] at h'
      have := Fin.lt_def.mp hq
      omega
    have htri' := repr_tri b u (fun q => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg q))
      fun q => (hu q).2
    have hy : w.repr v i = a i * (u i * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i)) := by
      rw [hva, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul, (htri' i).1]
      · intro q _ hqi
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        rcases lt_or_gt_of_ne hqi with h | h
        · rw [(htri' q).2 i h, mul_zero]
        · rw [ha0 q h, zero_mul]
      · simp
    obtain ⟨n1, hn1⟩ := ha i
    obtain ⟨n2, hn2⟩ := (hu i).1.2.1
    refine ⟨n1 + n2, ?_⟩
    have heq : f l ^ (n1 + n2) * (w.repr v i / IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i)) =
        (f l ^ n1 * a i) * (f l ^ n2 * u i) := by
      rw [hy, ← mul_assoc, mul_div_cancel_right₀ _ hM0, pow_add]
      ring
    rw [heq]
    exact mul_mem hn1 hn2
  ·
    rintro ⟨r, hr, rfl⟩
    let R := chartRing F (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) c
    let J : Ideal R :=
      { carrier := {t | ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
          w.repr v i = (t : Ω) * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i)}
        add_mem' := by
          rintro t1 t2 ⟨v1, h1, z1, e1⟩ ⟨v2, h2, z2, e2⟩
          refine ⟨v1 + v2, add_mem h1 h2, fun j hj => by simp [z1 j hj, z2 j hj], ?_⟩
          simp [e1, e2, add_mul]
        zero_mem' := ⟨0, zero_mem _, fun j _ => by simp, by simp⟩
        smul_mem' := by
          rintro t1 t2 ⟨v2, h2, z2, e2⟩
          refine ⟨(t1 : Ω) • v2, B.stable c _ t1.2 v2 h2, fun j hj => by simp [z2 j hj], ?_⟩
          simp [e2, mul_assoc] }
    have hJ : J = ⊤ := by
      refine ideal_eq_top (fun l => (⟨f l, hf l⟩ : R)) (fun l => ⟨cc l, hcc l⟩) ?_ J ?_
      · apply Subtype.ext
        simpa using hsum
      · intro l
        obtain ⟨b, hbli, hbsp, hcrit, htri⟩ := hfr l
        choose u hu using htri
        have htri' := repr_tri b u (fun q => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg q))
          fun q => (hu q).2
        obtain ⟨n, hn⟩ := (hcrit (b i)).mpr
          ⟨fun q => if q = i then 1 else 0, fun q => ⟨0, by by_cases h : q = i <;> simp [h]⟩, by simp⟩
        obtain ⟨m, hm⟩ := (hu i).1.2.2
        refine ⟨n + m, ?_⟩
        show ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
          w.repr v i = (((⟨f l, hf l⟩ : R) ^ (n + m) : R) : Ω) *
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon x c (fl.deg i)
        refine ⟨(f l ^ m * (u i)⁻¹) • (f l ^ n • b i), B.stable c _ hm _ hn, fun j hj => ?_, ?_⟩
        · simp [(htri' i).2 j hj]
        · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, (htri' i).1,
            SubmonoidClass.coe_pow]
          have hu0 := (hu i).1.1
          field_simp
          ring
    have hrJ : (⟨r, hr⟩ : R) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨v, hv, hz, hvi⟩ := hrJ
    exact ⟨v, hv, hz, hvi⟩

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
