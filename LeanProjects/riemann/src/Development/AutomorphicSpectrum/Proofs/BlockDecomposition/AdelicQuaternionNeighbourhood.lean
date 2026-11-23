import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.Box

variable {F : Type} [Field F] [NumberField F]

theorem af_box (x : Af F) (W : Set (Af F)) (hW : W ∈ 𝓝 x) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ U : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F),
      (∀ v, U v ∈ 𝓝 (x v)) ∧
      (∀ v, v ∉ S → U v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
      ∀ y : Af F, (∀ v ∈ S, y v ∈ U v) →
        (∀ v, v ∉ S → y v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → y ∈ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hx : Set.Finite {v | x v ∉ A v} := x.2
  let S0 : Finset (HeightOneSpectrum (𝓞 F)) := hx.toFinset
  have hS0 : ∀ v, v ∉ S0 → x v ∈ A v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S0] using h)
  have hS : Filter.cofinite ≤ Filter.principal ((S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S0.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hS
  have hr : ∀ y : Af F, (∀ v, v ∉ S0 → y v ∈ A v) →
      y ∈ Set.range (RestrictedProduct.inclusion R A hS) := by
    intro y hy
    rw [RestrictedProduct.range_inclusion]
    exact Filter.eventually_principal.2 fun v hv => hy v hv
  obtain ⟨x', hx'⟩ := hr x hS0
  have hW' : RestrictedProduct.inclusion R A hS ⁻¹' W ∈ 𝓝 x' :=
    hemb.continuous.continuousAt.preimage_mem_nhds (by rw [hx']; exact hW)
  rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ)).isInducing.nhds_eq_comap, Filter.mem_comap] at hW'
  obtain ⟨t, ht, htW⟩ := hW'
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, u, hu, hIu⟩ := ht
  have hval : ∀ v, x' v = x v := fun v => by rw [← hx']; rfl
  refine ⟨S0 ∪ hI.toFinset, fun v => u v ∩ (if v ∈ S0 then Set.univ else A v), ?_, ?_, ?_⟩
  · intro v
    refine Filter.inter_mem (by rw [← hval]; exact hu v) ?_
    by_cases h : v ∈ S0
    · simp [h]
    · simpa [h] using (hAo v).mem_nhds (hS0 v h)
  · intro v hv z hz
    have h : v ∉ S0 := fun h => hv (Finset.mem_union_left _ h)
    have h2 := hz.2
    rw [if_neg h] at h2
    exact h2
  · intro y hy1 hy2
    have hyA : ∀ v, v ∉ S0 → y v ∈ A v := by
      intro v hv
      by_cases h : v ∈ S0 ∪ hI.toFinset
      · simpa [hv] using (hy1 v h).2
      · exact hy2 v h
    obtain ⟨y', hy'⟩ := hr y hyA
    have hval' : ∀ v, y' v = y v := fun v => by rw [← hy']; rfl
    have : y' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W := by
      refine htW (hIu fun v hv => ?_)
      have hv' : v ∈ S0 ∪ hI.toFinset := Finset.mem_union_right _ (by simpa using hv)
      show y' v ∈ u v
      rw [hval']
      exact (hy1 v hv').1
    have hz : RestrictedProduct.inclusion R A hS y' ∈ W := this
    rw [hy'] at hz
    exact hz

theorem pi_box {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (A : Set (∀ i, X i)) (hA : A ∈ 𝓝 x) :
    ∃ t : ∀ i, Set (X i), (∀ i, t i ∈ 𝓝 (x i)) ∧ ∀ y : ∀ i, X i, (∀ i, y i ∈ t i) → y ∈ A := by
  rw [nhds_pi, Filter.mem_pi] at hA
  obtain ⟨I, -, t, ht, hIt⟩ := hA
  exact ⟨t, ht, fun y hy => hIt fun i _ => hy i⟩

theorem adele_box (x : AF F) (W : Set (AF F)) (hW : W ∈ 𝓝 x) :
    ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Kp u),
      (∀ u, U u ∈ 𝓝 (proj u x)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → U (Sum.inr v) ⊆ Ov v) ∧
      ∀ y : AF F, (∀ u ∈ T, proj u y ∈ U u) →
        (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → proj (Sum.inr v) y ∈ Ov v) → y ∈ W := by
  classical
  have hW' : W ∈ 𝓝 ((x.1, x.2) : Ainf F × Af F) := hW
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hW'
  obtain ⟨t, ht, hIt⟩ := pi_box (X := fun w : InfinitePlace F => w.Completion) x.1 A hA
  obtain ⟨S, V, hV, hVO, hSV⟩ := af_box x.2 B hB
  refine ⟨Finset.univ.map Function.Embedding.inl ∪ S.map Function.Embedding.inr,
    fun u => match u with
      | .inl w => t w
      | .inr v => V v, ?_, ?_, ?_, ?_⟩
  · rintro (w | v)
    · exact ht w
    · exact hV v
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩)
  · intro v hv
    exact hVO v fun h => hv (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, h, rfl⟩))
  · intro y hy1 hy2
    have h1 : y.1 ∈ A := hIt y.1 fun w =>
      hy1 (Sum.inl w) (Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩))
    have h2 : y.2 ∈ B := by
      refine hSV y.2 (fun v hv => ?_) (fun v hv => ?_)
      · exact hy1 (Sum.inr v) (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, rfl⟩))
      · by_cases h : (Sum.inr v : Pl F) ∈ Finset.univ.map Function.Embedding.inl ∪
            S.map Function.Embedding.inr
        · rcases Finset.mem_union.1 h with h | h
          · obtain ⟨w, -, hw⟩ := Finset.mem_map.1 h
            cases hw
          · obtain ⟨v', hv', e⟩ := Finset.mem_map.1 h
            cases e
            exact absurd hv' hv
        · exact hy2 v h
    exact hAB (Set.mk_mem_prod h1 h2)

theorem basic_nhd {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)) :
    ∀ V ∈ 𝓝 a,
      ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
        (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
        ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
          (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) →
            b ∈ V := by
  classical
  intro V hV
  let e := qHomeo (d := d) (β := β) (R := AF F)
  have h0 : e.symm ⁻¹' V ∈ 𝓝 (a.re, a.imI, a.imJ, a.imK) := by
    refine e.symm.continuous.continuousAt.preimage_mem_nhds ?_
    have : e.symm (a.re, a.imI, a.imJ, a.imK) = a := e.symm_apply_apply a
    rw [this]
    exact hV
  obtain ⟨W1, h1, R1, hR1, hs1⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨W2, h2, R2, hR2, hs2⟩ := mem_nhds_prod_iff.1 hR1
  obtain ⟨W3, h3, W4, h4, hs3⟩ := mem_nhds_prod_iff.1 hR2
  obtain ⟨T1, U1, n1, i1, o1, c1⟩ := adele_box a.re W1 h1
  obtain ⟨T2, U2, n2, -, o2, c2⟩ := adele_box a.imI W2 h2
  obtain ⟨T3, U3, n3, -, o3, c3⟩ := adele_box a.imJ W3 h3
  obtain ⟨T4, U4, n4, -, o4, c4⟩ := adele_box a.imK W4 h4
  refine ⟨T1 ∪ T2 ∪ T3 ∪ T4,
    fun u => {q | q.re ∈ U1 u ∧ q.imI ∈ U2 u ∧ q.imJ ∈ U3 u ∧ q.imK ∈ U4 u}, ?_, ?_, ?_⟩
  · intro u
    have m1 : {q : Q d β (Kp u) | q.re ∈ U1 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_re (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n1 u)
    have m2 : {q : Q d β (Kp u) | q.imI ∈ U2 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imI (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n2 u)
    have m3 : {q : Q d β (Kp u) | q.imJ ∈ U3 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imJ (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n3 u)
    have m4 : {q : Q d β (Kp u) | q.imK ∈ U4 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imK (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n4 u)
    filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (i1 w)))
  · intro b hb1 hb2
    have t1 : T1 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t2 : T2 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t3 : T3 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t4 : T4 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have b1 : b.re ∈ W1 := c1 b.re (fun u hu => (hb1 u (t1 hu)).1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o1 v hv (hb1 _ h).1
      · exact (hb2 v h).1
    have b2 : b.imI ∈ W2 := c2 b.imI (fun u hu => (hb1 u (t2 hu)).2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o2 v hv (hb1 _ h).2.1
      · exact (hb2 v h).2.1
    have b3 : b.imJ ∈ W3 := c3 b.imJ (fun u hu => (hb1 u (t3 hu)).2.2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o3 v hv (hb1 _ h).2.2.1
      · exact (hb2 v h).2.2.1
    have b4 : b.imK ∈ W4 := c4 b.imK (fun u hu => (hb1 u (t4 hu)).2.2.2) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o4 v hv (hb1 _ h).2.2.2
      · exact (hb2 v h).2.2.2
    have hm : (b.re, b.imI, b.imJ, b.imK) ∈ e.symm ⁻¹' V :=
      hs1 (Set.mk_mem_prod b1 (hs2 (Set.mk_mem_prod b2 (hs3 (Set.mk_mem_prod b3 b4)))))
    have hb : e.symm (b.re, b.imI, b.imJ, b.imK) = b := e.symm_apply_apply b
    rw [Set.mem_preimage, hb] at hm
    exact hm

end GlobalTheory.CompanionTheory.PlaneSA.Box
