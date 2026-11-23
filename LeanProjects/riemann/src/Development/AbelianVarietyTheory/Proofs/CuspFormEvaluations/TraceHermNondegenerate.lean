import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingHermSelf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocalizedModuleSubtype

open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule

namespace GlobalTheory

namespace ShortVectors

section Rational

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem exists_euclidean {M : ℕ} [FiniteDimensional ℚ V] (hM : finrank ℚ V = M)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) :
    ∃ φ : V →ₗ[ℚ] EuclideanSpace ℝ (Fin M), ∀ x y, inner ℝ (φ x) (φ y) = (B x y : ℝ) := by
  classical
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hs)
  let e : Fin M ≃ Fin (finrank ℚ V) := finCongr hM.symm
  let c : Fin M → ℝ := fun i => Real.sqrt (B (v (e i)) (v (e i)))
  let F : V → Fin M → ℝ := fun x i => c i * (v.repr x (e i) : ℝ)
  let φ : V →ₗ[ℚ] EuclideanSpace ℝ (Fin M) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin M) ℝ).symm (F x)
      map_add' := fun x y => by
        ext i
        simp [F, mul_add]
      map_smul' := fun q x => by
        ext i
        simp [F, Rat.smul_def, mul_left_comm] }
  refine ⟨φ, fun x y => ?_⟩
  have hB : B x y = ∑ j, v.repr x j * v.repr y j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · ring
    · intro k _ hk
      have h0 : B (v k) (v j) = 0 := hv hk
      simp [h0]
    · simp
  have hinner : inner ℝ (φ x) (φ y) = ∑ i, c i ^ 2 * ((v.repr x (e i) : ℝ) * (v.repr y (e i) : ℝ)) := by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [F]
    ring
  rw [hinner, hB, Rat.cast_sum]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  simp only [c, Rat.cast_mul]
  rw [Real.sq_sqrt (Rat.cast_nonneg.mpr (hp _))]
  ring

theorem transference_rat {M : ℕ} (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) (hn : B.Nondegenerate)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ (B u u : ℝ)) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, (B (v i) (v i) : ℝ) ≤ ((M : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  have : FiniteDimensional ℚ V := b.finiteDimensional_of_finite
  have hM : finrank ℚ V = M := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  obtain ⟨φ, hφ⟩ := exists_euclidean hM B hs hp
  let bd := B.dualBasis hn b
  have hd1 : ∀ i j, B (bd i) (b j) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hn b i j
  have hd2 : ∀ i j, inner ℝ (φ (bd i)) (φ (b j)) = if j = i then 1 else 0 := by
    intro i j
    rw [hφ, hd1]
    split_ifs <;> simp
  have hd3 : ∀ i j, inner ℝ (φ (b j)) (φ (bd i)) = if j = i then 1 else 0 := by
    intro i j
    rw [real_inner_comm]
    exact hd2 i j
  have hli : LinearIndependent ℝ (fun i => φ (bd i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun z => inner ℝ z (φ (b i))) hg
    simp only [sum_inner, real_inner_smul_left, hd2, inner_zero_left, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  let b' : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)
  have hb' : ∀ i, b' i = φ (bd i) := fun i => by simp [b']
  have hint : ∀ u ∈ Submodule.span ℤ (Set.range bd), ∀ j, ∃ k : ℤ, B u (b j) = k := by
    intro u hu j
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨if j = i then 1 else 0, by rw [hd1]; split_ifs <;> simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k1, h1⟩ := hx
      obtain ⟨k2, h2⟩ := hy
      exact ⟨k1 + k2, by rw [map_add, LinearMap.add_apply, h1, h2]; push_cast; ring⟩
    | smul a x _ hx =>
      obtain ⟨k, h⟩ := hx
      exact ⟨a * k, by rw [map_zsmul, LinearMap.smul_apply, h, zsmul_eq_mul]; push_cast; ring⟩
  have hmin' : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have hr : Set.range b' = φ.toAddMonoidHom.toIntLinearMap '' Set.range bd := by
      rw [← Set.range_comp]
      ext z
      simp [hb']
    rw [hr, ← Submodule.map_span] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hx0
    have h1 := hmin u hu0 (hint u hu)
    have h2 : (B u u : ℝ) = ‖φ u‖ ^ 2 := by rw [← hφ, real_inner_self_eq_norm_sq]
    rw [h2] at h1
    have h3 : 0 ≤ ‖φ u‖ := norm_nonneg _
    change lam ≤ ‖φ u‖
    nlinarith
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual b' lam hlam hmin'
  choose m hm using hyint
  have hyv : ∀ i, φ (∑ j, (m i j : ℚ) • b j) = y i := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis b' fun k => ?_
    rw [hm, hb', map_sum, sum_inner]
    simp only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ, real_inner_smul_left, hd3, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Rat.cast_intCast]
  refine ⟨fun i => ∑ j, (m i j : ℚ) • b j, fun i => ?_, ?_, fun i => ?_⟩
  · refine Submodule.sum_mem _ fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg φ hg
    rw [map_sum, map_zero] at h
    simp only [map_smul, hyv, ← Rat.cast_smul_eq_qsmul ℝ] at h
    have := (Fintype.linearIndependent_iff.mp hyli) (fun i => (g i : ℝ)) h i
    exact_mod_cast this
  · rw [← hφ, hyv, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hynorm i) 2

end Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def traceHerm (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (herm 1 x y))
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1; simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])

theorem traceHerm_apply {n : ℕ} (x y : Fin n → E) :
    traceHerm n x y = Algebra.trace ℚ E (herm 1 x y) := rfl

theorem traceHerm_self {n : ℕ} (x : Fin n → E) :
    (traceHerm n x x : ℝ) = ∑ σ : E →+* ℂ, ∑ k, ‖σ (x k)‖ ^ 2 := by
  rw [traceHerm_apply]
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := herm 1 x x)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ (herm 1 x x) = ∑ σ : E →+* ℂ, σ (herm 1 x x) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun σ => rfl).symm
  rw [h2] at h1
  simp only [TraceDualMin.embedding_herm_self] at h1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, Complex.ofReal_sum]

theorem traceHerm_isSymm (n : ℕ) : (traceHerm (E := E) n).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [traceHerm_apply, traceHerm_apply, DualFamily.herm_one_symm x y, TraceDualMin.trace_cc]

theorem traceHerm_nonneg {n : ℕ} (x : Fin n → E) : 0 ≤ traceHerm n x x := by
  have h : (0 : ℝ) ≤ (traceHerm n x x : ℝ) := by
    rw [traceHerm_self]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact_mod_cast h

theorem two_mul_le_traceHerm {n : ℕ} (x : Fin n → E) (τ : E →+* ℂ) :
    2 * ∑ k, ‖τ (x k)‖ ^ 2 ≤ (traceHerm n x x : ℝ) := by
  classical
  rw [traceHerm_self]
  let f : (E →+* ℂ) → ℝ := fun σ => ∑ k, ‖σ (x k)‖ ^ 2
  have hne : NumberField.ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have hr : NumberField.ComplexEmbedding.IsReal τ := NumberField.ComplexEmbedding.isReal_iff.mpr h
    exact NumberField.InfinitePlace.not_isReal_of_mk_isComplex
      (NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)) hr
  have hf : f (NumberField.ComplexEmbedding.conjugate τ) = f τ := by
    simp [f, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hnn : ∀ σ ∈ (Finset.univ : Finset (E →+* ℂ)), σ ∉ ({τ, NumberField.ComplexEmbedding.conjugate τ} : Finset _) →
      0 ≤ f σ := fun σ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc 2 * ∑ k, ‖τ (x k)‖ ^ 2 = f τ + f (NumberField.ComplexEmbedding.conjugate τ) := by
        rw [hf]; ring
    _ = ∑ σ ∈ ({τ, NumberField.ComplexEmbedding.conjugate τ} : Finset _), f σ := by
        rw [Finset.sum_pair hne.symm]
    _ ≤ ∑ σ, f σ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) hnn

theorem traceHerm_nondegenerate (n : ℕ) : (traceHerm (E := E) n).Nondegenerate := by
  have hl : ∀ x : Fin n → E, (∀ y, traceHerm n x y = 0) → x = 0 := by
    intro x hx
    have h0 := traceHerm_self x
    rw [hx x, Rat.cast_zero] at h0
    obtain ⟨σ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    funext k
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg ‖σ (x k)‖)).mp h0.symm σ (Finset.mem_univ _)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖σ (x k)‖)).mp hs k
      (Finset.mem_univ _)
    have h1 : σ (x k) = 0 := by simpa using hk
    simpa using h1
  exact ⟨hl, fun y hy => hl y fun x => by rw [(traceHerm_isSymm n).eq]; exact hy x⟩

omit [IsCMField E] in
theorem span_rat_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : span E (Λ : Set (Fin n → E)) = ⊤) : span ℚ (Λ : Set (Fin n → E)) = ⊤ := by
  have key : ∀ (a : E) (v : Fin n → E), v ∈ Λ → a • v ∈ span ℚ (Λ : Set (Fin n → E)) := by
    intro a v hv
    obtain ⟨m, s, hm, hs⟩ :=
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)).exists_nsmul_eq
        (𝓞 E)
    have hinv : ((m : ℚ)⁻¹) • (m • a) = a := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul]
    have ha : a = ((m : ℚ)⁻¹) • (algebraMap (𝓞 E) E s) := by
      rw [← hs, hinv]
    have hsv : (algebraMap (𝓞 E) E s) • v = s • v := algebraMap_smul E s v
    rw [ha, smul_assoc, hsv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Λ.smul_mem s hv))
  have closed : ∀ (a : E) (x : Fin n → E), x ∈ span ℚ (Λ : Set (Fin n → E)) →
      a • x ∈ span ℚ (Λ : Set (Fin n → E)) := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact key a v hv
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact add_mem hx hy
    | smul q x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ q hx
  rw [eq_top_iff]
  rintro w -
  have hw : w ∈ span E (Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span hv
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact closed a x hx

theorem finrank_eq : finrank ℚ E = 2 * fdeg E := by
  rw [fdeg, NumberField.IsTotallyComplex.finrank]
  omega

theorem exists_basis {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (h : span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : Basis (Fin (2 * fdeg E * n)) ℚ (Fin n → E),
      ∀ x, x ∈ span ℤ (Set.range b) ↔ x ∈ Λ := by
  classical
  have hq := span_rat_eq_top Λ h
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  let bz := Module.finBasis ℤ Λ
  let u : Fin (finrank ℤ Λ) → Fin n → E := fun i => (bz i : Fin n → E)
  have hspanZ : (Submodule.span ℤ (Set.range u) : Set (Fin n → E)) = Λ := by
    have h1 : Submodule.span ℤ (Set.range u) =
        (⊤ : Submodule ℤ Λ).map (Λ.subtype.restrictScalars ℤ) := by
      rw [← bz.span_eq, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, Submodule.map_top]
    ext x
    simp
  have hliZ : LinearIndependent ℤ u :=
    bz.linearIndependent.map' (Λ.subtype.restrictScalars ℤ)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ u := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspQ : ⊤ ≤ Submodule.span ℚ (Set.range u) := by
    rw [← hq, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range u) := by
      rw [← SetLike.mem_coe, hspanZ]
      exact hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hx'
  let bq : Basis (Fin (finrank ℤ Λ)) ℚ (Fin n → E) := Basis.mk hliQ hspQ
  have hcard : finrank ℤ Λ = 2 * fdeg E * n := by
    have h1 := Module.finrank_eq_card_basis bq
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp [finrank_eq]
    ring
  refine ⟨bq.reindex (finCongr hcard), fun x => ?_⟩
  rw [Basis.range_reindex, Basis.coe_mk, ← SetLike.mem_coe, hspanZ, SetLike.mem_coe]

end ShortVectors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open ShortVectors in

theorem exists_short_vectors {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) :
    ∃ v : Fin (2 * fdeg E * n) → Fin n → E, (∀ i, v i ∈ Λ) ∧ LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v) = ⊤ ∧
      ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 := by
  classical
  have hspan := DualFamily.span_eq_top Λ hfg hdual
  obtain ⟨b, hb⟩ := exists_basis Λ hfg hspan
  have hfin : finrank ℚ E = 2 * fdeg E := finrank_eq
  have hf : 0 < fdeg E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hrd : 0 < rdE E := by
    unfold rdE dE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))) _
  have hF0 : (0 : ℝ) < fdeg E := by exact_mod_cast hf
  set lam : ℝ := Real.sqrt (2 * fdeg E) / rdE E with hlam_def
  have hlam : 0 < lam := div_pos (Real.sqrt_pos.mpr (by positivity)) hrd
  have hl2 : lam ^ 2 = 2 * fdeg E / rdE E ^ 2 := by
    rw [hlam_def, div_pow, Real.sq_sqrt (by positivity)]
  have hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, traceHerm n u (b j) = k) →
      lam ^ 2 ≤ (traceHerm n u u : ℝ) := by
    intro u hu hj
    have htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k := by
      intro y hy
      have hy' := (hb y).mpr hy
      clear hy
      simp only [← traceHerm_apply]
      induction hy' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact hj j
      | zero => exact ⟨0, by simp⟩
      | add x z _ _ hx hz =>
        obtain ⟨k1, h1⟩ := hx
        obtain ⟨k2, h2⟩ := hz
        exact ⟨k1 + k2, by rw [map_add, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨k, h⟩ := hx
        exact ⟨a * k, by rw [map_zsmul, h, zsmul_eq_mul]; push_cast; ring⟩
    have h1 := trace_dual_min Λ hint hdual u hu htr
    rw [traceHerm_self, hl2]
    exact h1
  obtain ⟨v, hvΛ, hvli, hvB⟩ := transference_rat b (traceHerm n) (traceHerm_isSymm n)
    traceHerm_nonneg (traceHerm_nondegenerate n) lam hlam hmin
  refine ⟨v, fun i => (hb _).mp (hvΛ i), hvli, ?_, fun i τ => ?_⟩
  · exact hvli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  · have h2 := two_mul_le_traceHerm (v i) τ
    have h3 := hvB i
    have hF3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hF0.le,
        ← Real.rpow_natCast (fdeg E : ℝ) 3]
      norm_num
    have key : (((2 * fdeg E * n : ℕ) : ℝ) ^ 2 / lam) ^ 2 =
        2 * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 := by
      rw [div_pow, hl2, mul_pow, mul_pow, mul_pow, hF3]
      push_cast
      field_simp
    linarith

end GlobalTheory
