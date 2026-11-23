import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import GroundTheory.AutomorphicForms.IwahoriFactorization
import GroundTheory.AutomorphicForms.CuspidalAdmissible

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section Abstract

variable {G : Type*} [Group G]

private structure Dom (J B : Subgroup G) (L : Set G) (x : G) : Prop where
  inB : x ∈ B
  up : ∀ b ∈ J, b ∈ B → x * b * x⁻¹ ∈ J
  low : ∀ z ∈ L, x⁻¹ * z * x ∈ J

private def Fac (J B : Subgroup G) (L : Set G) : Prop :=
  ∀ k ∈ J, ∃ b ∈ J, b ∈ B ∧ ∃ z ∈ L, k = b * z

private abbrev Cs (J : Subgroup G) (x : G) : Set (G ⧸ J) :=
  {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}

variable {J B : Subgroup G} {L : Set G} {x y : G}

private theorem rep (hF : Fac J B L) (hx : Dom J B L x) {k : G} (hk : k ∈ J) :
    ∃ b ∈ J, b ∈ B ∧ (QuotientGroup.mk (k * x) : G ⧸ J) = QuotientGroup.mk (b * x) := by
  obtain ⟨b, hb, hbB, z, hz, rfl⟩ := hF k hk
  refine ⟨b, hb, hbB, ?_⟩
  rw [QuotientGroup.eq]
  have := J.inv_mem (hx.low z hz)
  convert this using 1
  group

private theorem swap (hF : Fac J B L) (hx : Dom J B L x) (hy : Dom J B L y) {l : G} (hl : l ∈ J) :
    ∃ a ∈ J, ∃ c ∈ J, x * l * y = a * (x * y) * c := by
  obtain ⟨b, hb, hbB, z, hz, rfl⟩ := hF l hl
  exact ⟨x * b * x⁻¹, hx.up b hb hbB, y⁻¹ * z * y, hy.low z hz, by group⟩

private theorem out_mk (J : Subgroup G) (g : G) :
    ∃ j ∈ J, (QuotientGroup.mk g : G ⧸ J).out = g * j := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : G ⧸ J).out, ?_, by group⟩
  exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm

private theorem cos_key (hF : Fac J B L) (hx : Dom J B L x) (hy : Dom J B L y) {c d : G ⧸ J}
    (hc : c ∈ Cs J x) (hd : d ∈ Cs J y) :
    ∃ b ∈ J, b ∈ B ∧ ∃ m ∈ J, m ∈ B ∧ c = QuotientGroup.mk (b * x) ∧
      (QuotientGroup.mk (c.out * d.out) : G ⧸ J) = QuotientGroup.mk (b * x * (m * y)) := by
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  obtain ⟨b, hb, hbB, e⟩ := rep hF hx hk
  rw [e]
  obtain ⟨j, hj, ej⟩ := out_mk J (b * x)
  obtain ⟨i, hi, ei⟩ := out_mk J (l * y)
  obtain ⟨m, hm, hmB, em⟩ := rep hF hy (J.mul_mem hj hl)
  refine ⟨b, hb, hbB, m, hm, hmB, rfl, ?_⟩
  rw [ej, ei, QuotientGroup.eq]
  have := J.mul_mem (J.inv_mem hi) (QuotientGroup.eq.1 em)
  convert this using 1
  group

private theorem cos_inj (hF : Fac J B L) (hx : Dom J B L x) (hy : Dom J B L y) {c c' d d' : G ⧸ J}
    (hc : c ∈ Cs J x) (hc' : c' ∈ Cs J x) (hd : d ∈ Cs J y) (hd' : d' ∈ Cs J y)
    (h : (QuotientGroup.mk (c.out * d.out) : G ⧸ J) = QuotientGroup.mk (c'.out * d'.out)) :
    c = c' ∧ d = d' := by
  obtain ⟨b, hb, hbB, m, hm, hmB, ec, e⟩ := cos_key hF hx hy hc hd
  obtain ⟨b', hb', hbB', m', hm', hmB', ec', e'⟩ := cos_key hF hx hy hc' hd'
  have h2 : (QuotientGroup.mk (b * x * (m * y)) : G ⧸ J) = QuotientGroup.mk (b' * x * (m' * y)) := by
    rw [← e, ← e', h]
  have ht := QuotientGroup.eq.1 h2
  have htB : (b * x * (m * y))⁻¹ * (b' * x * (m' * y)) ∈ B :=
    B.mul_mem (B.inv_mem (B.mul_mem (B.mul_mem hbB hx.inB) (B.mul_mem hmB hy.inB)))
      (B.mul_mem (B.mul_mem hbB' hx.inB) (B.mul_mem hmB' hy.inB))
  have hp := J.mul_mem (J.mul_mem hm (hy.up _ ht htB)) (J.inv_mem hm')
  have hcc : c = c' := by
    rw [ec, ec', QuotientGroup.eq]
    convert hp using 1
    group
  subst hcc
  refine ⟨rfl, ?_⟩
  have h3 := QuotientGroup.eq.1 h
  have h4 : d.out⁻¹ * d'.out ∈ J := by
    convert h3 using 1
    group
  rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
  exact QuotientGroup.eq.2 h4

private theorem cos_rng (hF : Fac J B L) (hx : Dom J B L x) (hy : Dom J B L y) (g : G ⧸ J) :
    (∃ c ∈ Cs J x, ∃ d ∈ Cs J y, g = QuotientGroup.mk (c.out * d.out)) ↔ g ∈ Cs J (x * y) := by
  constructor
  · rintro ⟨c, ⟨k, hk, rfl⟩, d, ⟨l, hl, rfl⟩, rfl⟩
    obtain ⟨j, hj, ej⟩ := out_mk J (k * x)
    obtain ⟨i, hi, ei⟩ := out_mk J (l * y)
    obtain ⟨a, ha, e, he, hs⟩ := swap hF hx hy (J.mul_mem hj hl)
    refine ⟨k * a, J.mul_mem hk ha, ?_⟩
    rw [ej, ei, QuotientGroup.eq]
    have hmul : k * x * j * (l * y * i) = k * a * (x * y) * (e * i) := by
      calc k * x * j * (l * y * i) = k * (x * (j * l) * y) * i := by group
        _ = k * a * (x * y) * (e * i) := by rw [hs]; group
    rw [hmul]
    have := J.inv_mem (J.mul_mem he hi)
    convert this using 1
    group
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj, ej⟩ := out_mk J (k * x)
    refine ⟨_, ⟨k, hk, rfl⟩, _, ⟨j⁻¹, J.inv_mem hj, rfl⟩, ?_⟩
    obtain ⟨i, hi, ei⟩ := out_mk J (j⁻¹ * y)
    rw [ej, ei, QuotientGroup.eq]
    convert hi using 1
    group

end Abstract

section Conc

open Parabolic Cartan Iwasawa GLnLocal ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

private theorem conj_mem (c : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, i ≠ j → g i j ≠ 0 → c j ≤ c i) :
    Cartan.diagPow F n c * g * (Cartan.diagPow F n c)⁻¹ ∈ iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  have hle : ∀ i j, i ≠ j → g i j ≠ 0 →
      valuation F ((uniformizer F : F) ^ (c i - c j) * g i j) ≤ valuation F (g i j) := by
    intro i j e z
    have := valuation_zpow_mul_le_pow_mul (F := F) (x := g i j) (e := 0) (z := c i - c j)
      (by have := h i j e z; push_cast; omega)
    simpa using this
  rw [mem_iwahori_iff F n]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [diagPow_conj_apply]
    by_cases e : i = j
    · subst e
      simp [h3]
    by_cases z : g i j = 0
    · simp [z]
    · exact (hle i j e z).trans (h1 i j)
  · rw [diagPow_conj_apply]
    by_cases z : g i j = 0
    · simp [z]
    · exact (hle i j hij.ne' z).trans_lt (h2 i j hij)
  · rw [diagPow_conj_apply]
    simp [h3]

private abbrev Lw (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) : Set (GL (Fin n) F) :=
  ((iwahori F n ⊓ oppositeUnipotentRadical F n (id : Fin n → Fin n) : Subgroup _) : Set _)

private theorem iw_fac :
    Fac (iwahori F n) (blockUpper F n (id : Fin n → Fin n)) (Lw F n) := by
  intro k hk
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := iwahori_iwahoriFactorization' (F := F) (n := n)
    (β := (id : Fin n → Fin n)) monotone_id k hk
  obtain ⟨hxI, hxN⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hyI, hyM⟩ := Subgroup.mem_inf.1 hy
  exact ⟨x * y, Subgroup.mul_mem _ hxI hyI,
    Subgroup.mul_mem _ (unipotentRadical_le_blockUpper hxN) (levi_le_blockUpper hyM), z, hz, rfl⟩

private theorem iw_dom {ν : Fin n → ℤ} (hν : Antitone ν) :
    Dom (iwahori F n) (blockUpper F n (id : Fin n → Fin n)) (Lw F n) (Cartan.diagPow F n ν) := by
  refine ⟨levi_le_blockUpper (diagPow_mem_levi ν), fun b hb hbB => ?_, fun z hz => ?_⟩
  · refine conj_mem ν hb fun i j e nz => hν ?_
    by_contra hlt
    exact nz ((mem_blockUpper F n).1 hbB (not_le.1 hlt))
  · obtain ⟨hzI, hzN⟩ := Subgroup.mem_inf.1 hz
    have := conj_mem (-ν) hzI fun i j e nz => ?_
    · rwa [diagPow_neg, inv_inv] at this
    · have hji : j ≤ i := by
        by_contra hlt
        exact nz ((mem_oppositeUnipotentRadical.1 hzN).1 i j (not_le.1 hlt))
      simpa using hν hji

end Conc

section Op

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
  (w : Pl K)

private theorem hop_mul (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (hO : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (hC : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (x y : GL (Fin n) (w.adicCompletion K))
    (hinj : ∀ c c' d d' : GL (Fin n) (w.adicCompletion K) ⧸ J, c ∈ Cs J x → c' ∈ Cs J x → d ∈ Cs J y →
      d' ∈ Cs J y → (QuotientGroup.mk (c.out * d.out) : GL (Fin n) (w.adicCompletion K) ⧸ J) =
        QuotientGroup.mk (c'.out * d'.out) → c = c' ∧ d = d')
    (hrng : ∀ g : GL (Fin n) (w.adicCompletion K) ⧸ J,
      (∃ c ∈ Cs J x, ∃ d ∈ Cs J y, g = QuotientGroup.mk (c.out * d.out)) ↔ g ∈ Cs J (x * y)) :
    Hop μ w J x ∘L Hop μ w J y = Hop μ w J (x * y) := by
  classical
  obtain ⟨fx, -, -, sx, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hO hC
  obtain ⟨fy, my, py, sy, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J y hO hC
  obtain ⟨-, -, pxy, sxy, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J (x * y) hO hC
  obtain ⟨-, -, a1, -, -, hmul, -, -, -⟩ :=
    UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  letI : Fintype (Cs J x) := fx.fintype
  letI : Fintype (Cs J y) := fy.fintype
  have rmul : ∀ g h, rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := fun g h => by
    simp only [rhoL, map_mul, hmul]
  have single : ∀ (z : GL (Fin n) (w.adicCompletion K)) (T : LL μ →L[ℂ] LL μ),
      (∀ (ι : Type) [Fintype ι] (f : ι → GL (Fin n) (w.adicCompletion K)),
        Function.Injective (fun i => (QuotientGroup.mk (f i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) →
        Set.range (fun i => (QuotientGroup.mk (f i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) = Cs J z →
        ∀ v ∈ fixL μ w J, T v = ∑ i, rhoL μ w (f i) v) →
      ∀ [Fintype (Cs J z)], ∀ v ∈ fixL μ w J, T v = ∑ d : Cs J z, rhoL μ w d.1.out v := by
    intro z T hT _ v hv
    refine hT (Cs J z) (fun d => d.1.out) (fun a b e => Subtype.ext ?_) ?_ v hv
    · simpa using e
    · ext g
      simp only [QuotientGroup.out_eq', Set.mem_range, Subtype.exists, exists_prop, exists_eq_right]
  refine ContinuousLinearMap.ext fun v => ?_
  have hu : prj (fixL μ w J) v ∈ fixL μ w J := a1 v
  have e1 : Hop μ w J y v = ∑ d : Cs J y, rhoL μ w d.1.out (prj (fixL μ w J) v) := by
    have := congrArg (fun T : LL μ →L[ℂ] LL μ => T v) py
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]
    exact single y _ sy _ hu
  have e2 : Hop μ w J x (Hop μ w J y v) = ∑ c : Cs J x, rhoL μ w c.1.out (Hop μ w J y v) :=
    single x _ sx _ (my v)
  have e3 : Hop μ w J (x * y) v = ∑ i : Cs J x × Cs J y,
      rhoL μ w (i.1.1.out * i.2.1.out) (prj (fixL μ w J) v) := by
    have := congrArg (fun T : LL μ →L[ℂ] LL μ => T v) pxy
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]
    refine sxy (Cs J x × Cs J y) (fun i => i.1.1.out * i.2.1.out) ?_ ?_ _ hu
    · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ e
      obtain ⟨rfl, rfl⟩ := hinj c c' d d' hc hc' hd hd' e
      rfl
    · ext g
      rw [← show _ ↔ g ∈ Cs J (x * y) from hrng g]
      constructor
      · rintro ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, rfl⟩
        exact ⟨c, hc, d, hd, rfl⟩
      · rintro ⟨c, hc, d, hd, rfl⟩
        exact ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, rfl⟩
  rw [ContinuousLinearMap.comp_apply, e2, e1, e3, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [rmul, ContinuousLinearMap.comp_apply]

private theorem uiw_mul (a b : Fin n → ℤ) (ha : Antitone a) (hb : Antitone b) :
    Uiw μ w a ∘L Uiw μ w b = Uiw μ w (a + b) := by
  unfold Uiw
  rw [GroundTheory.Automorphic.Parabolic.diagPow_add]
  exact hop_mul μ w _ (GLnLocal.isOpen_iwahori _ n) (GLnLocal.isCompact_iwahori _ n) _ _
    (fun _ _ _ _ h1 h2 h3 h4 e => cos_inj iw_fac (iw_dom ha) (iw_dom hb) h1 h2 h3 h4 e)
    (cos_rng iw_fac (iw_dom ha) (iw_dom hb))

end Op

theorem UpperTheory.ConvolutionTheory.Tf.uiwPow :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (ν ν' : Fin n → ℤ), Antitone ν → Antitone ν' →
      Uiw μ w ν ∘L Uiw μ w ν' = Uiw μ w (ν + ν') ∧ (∀ j : ℕ, 0 < j → Uiw μ w ν ^ j = Uiw μ w (j • ν)) ∧
      IsOpen (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ∧ IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ∧
      ∃ C : ℝ, ∀ j : ℕ, ‖Uiw μ w ν ^ j‖ ≤ C ^ j := by
  intro K _ _ n μ _ w ν ν' hν hν'
  have hanti : ∀ j : ℕ, Antitone (j • ν) := by
    intro j
    induction j with
    | zero =>
      rw [zero_nsmul]
      exact fun _ _ _ => le_rfl
    | succ j ih =>
      rw [succ_nsmul]
      exact ih.add hν
  refine ⟨uiw_mul μ w ν ν' hν hν', fun j hj => ?_, GLnLocal.isOpen_iwahori _ n,
    GLnLocal.isCompact_iwahori _ n, ‖Uiw μ w ν‖, fun j => ?_⟩
  · induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      rw [pow_succ, ih, succ_nsmul]
      exact uiw_mul μ w _ _ (hanti j) hν
  · cases j with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ j => exact norm_pow_le' _ (Nat.succ_pos j)
