import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices

namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

noncomputable section

section Slot

variable {ι : Type} [Fintype ι]

def intersection_update_fsHerm_neg_one (i0 k0 : Fin 2) : (ι → ℝ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℝ) where
  toFun p := fun τ i k => if i = i0 ∧ k = k0 then p τ else 0
  map_add' p q := by funext τ i k; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' s p := by
    funext τ i k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

lemma position_apply (i0 k0 : Fin 2) (p : ι → ℝ) (τ : ι) (i k : Fin 2) :
    intersection_update_fsHerm_neg_one i0 k0 p τ i k = if i = i0 ∧ k = k0 then p τ else 0 := rfl

lemma sum_position (y : ι → Fin 2 → Fin 2 → ℝ) :
    y = ∑ i0, ∑ k0, intersection_update_fsHerm_neg_one i0 k0 (fun τ => y τ i0 k0) := by
  funext τ i k
  simp only [Finset.sum_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;> simp [position_apply]

lemma norm_th_lt {y : ι → Fin 2 → Fin 2 → ℝ} (hy : ‖y‖ < 1) (τ : ι) (i k : Fin 2) :
    ‖th y τ i k‖ < 2 := by
  have h1 : ∀ a b : Fin 2, |y τ a b| < 1 := fun a b => by
    have h := (norm_le_pi_norm (y τ a) b).trans ((norm_le_pi_norm (y τ) a).trans (norm_le_pi_norm y τ))
    rw [Real.norm_eq_abs] at h
    linarith
  have hadd : ∀ a b : ℝ, |a| < 1 → |b| < 1 → ‖(a : ℂ) + I * b‖ < 2 := fun a b ha hb => by
    have e1 : ‖(a : ℂ)‖ = |a| := by simp
    have e2 : ‖I * (b : ℂ)‖ = |b| := by simp
    have := norm_add_le (a : ℂ) (I * b)
    linarith
  have hsub : ∀ a b : ℝ, |a| < 1 → |b| < 1 → ‖(a : ℂ) - I * b‖ < 2 := fun a b ha hb => by
    have e1 : ‖(a : ℂ)‖ = |a| := by simp
    have e2 : ‖I * (b : ℂ)‖ = |b| := by simp
    have := norm_sub_le (a : ℂ) (I * b)
    linarith
  simp only [th]
  split_ifs
  · have e1 : ‖(y τ i k : ℂ)‖ = |y τ i k| := by simp
    have := h1 i k
    linarith
  · exact hadd _ _ (h1 i k) (h1 k i)
  · exact hsub _ _ (h1 k i) (h1 i k)

end Slot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

def cE : E := ((g * dEnat E : ℕ) : E) / 2

def cr : ℝ := ((g * dEnat E : ℕ) : ℝ) / 2

lemma emb_cE (τ : E →+* ℂ) : τ (cE (E := E) g) = (cr (E := E) g : ℂ) := by
  simp only [cE, cr, map_div₀, map_natCast, map_ofNat]
  try push_cast
  try ring

lemma cr_pos (hg : 0 < g) : 0 < cr (E := E) g := by
  have hd : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have h : (0:ℝ) < ((g * dEnat E : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hg hd
  show (0:ℝ) < ((g * dEnat E : ℕ) : ℝ) / 2
  linarith

lemma cr_ge (hg : 0 < g) : (1 : ℝ) / 2 ≤ cr (E := E) g := by
  have hd : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have h0 := Nat.mul_pos hg hd
  have h : (1:ℝ) ≤ ((g * dEnat E : ℕ) : ℝ) := by exact_mod_cast h0
  show (1:ℝ) / 2 ≤ ((g * dEnat E : ℕ) : ℝ) / 2
  linarith

lemma cc_cE : cc (cE (E := E) g) = cE g := by
  simp only [cc, cE, map_div₀, map_natCast, map_ofNat]

lemma embH_herm {β : Matrix (Fin 2) (Fin 2) E} (hβ : ∀ i k, cc (β i k) = β k i) :
    IsHermFam (X.embH β) := by
  intro τ i k
  show τ.1 (β k i) = conj (τ.1 (β i k))
  rw [← hβ i k]
  exact NumberField.IsCMField.complexEmbedding_complexConj E τ.1 (β i k)

lemma herm_of_LZ {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  exact embH_herm X hβ

lemma mem_LZ_of (Γ : Matrix (Fin 2) (Fin 2) E) (hh : ∀ i k, cc (Γ i k) = Γ k i)
    (hi : ∀ i k, IsIntegral ℤ (Γ i k)) : X.embH (fun i k => cE g * Γ i k) ∈ X.LZ g := by
  refine ⟨fun i k => cE g * Γ i k, fun i k => ?_, fun i k => ⟨Γ i k, hi i k, rfl⟩, rfl⟩
  show cc (cE g * Γ i k) = cE g * Γ k i
  rw [show cc (cE g * Γ i k) = cc (cE g) * cc (Γ i k) from map_mul _ _ _, cc_cE, hh]

def LZsub : AddSubgroup (X.Ψ → Fin 2 → Fin 2 → ℂ) where
  carrier := X.LZ g
  add_mem' := by
    rintro _ _ ⟨β, hβ, hγ, rfl⟩ ⟨β', hβ', hγ', rfl⟩
    refine ⟨β + β', fun i k => ?_, fun i k => ?_, ?_⟩
    · show cc (β i k + β' i k) = β k i + β' k i
      rw [show cc (β i k + β' i k) = cc (β i k) + cc (β' i k) from map_add _ _ _, hβ, hβ']
    · obtain ⟨γ, hγi, e⟩ := hγ i k
      obtain ⟨γ', hγi', e'⟩ := hγ' i k
      exact ⟨γ + γ', hγi.add hγi', by simp only [Matrix.add_apply, e, e']; ring⟩
    · funext τ i k; simp [Data.embH]
  zero_mem' := ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩,
    by funext τ i k; simp [Data.embH]⟩
  neg_mem' := by
    rintro _ ⟨β, hβ, hγ, rfl⟩
    refine ⟨-β, fun i k => ?_, fun i k => ?_, ?_⟩
    · show cc (-β i k) = -β k i
      rw [show cc (-β i k) = -cc (β i k) from map_neg _ _, hβ]
    · obtain ⟨γ, hγi, e⟩ := hγ i k
      exact ⟨-γ, hγi.neg, by simp only [Matrix.neg_apply, e]; ring⟩
    · funext τ i k; simp [Data.embH]

lemma LZ_sum {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, ω j ∈ X.LZ g)
    (n : Fin N → ℤ) : ∑ j, (n j : ℂ) • ω j ∈ X.LZ g := by
  have key : ∀ j, (n j : ℂ) • ω j = n j • ω j := fun j => by
    first
    | exact Int.cast_smul_eq_zsmul ℂ (n j) (ω j)
    | exact Int.cast_smul_eq_zsmul (n j) (ω j)
    | simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  exact (LZsub X g).sum_mem fun j _ => (LZsub X g).zsmul_mem (hω j) (n j)

def Lc : Submodule ℤ (X.Ψ → Fin 2 → Fin 2 → ℝ) :=
  ((LZsub X g).map (kapL : (X.Ψ → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] _).toAddMonoidHom).toIntSubmodule

lemma mem_Lc {y : X.Ψ → Fin 2 → Fin 2 → ℝ} : y ∈ Lc X g ↔ ∃ b ∈ X.LZ g, kap b = y := by
  first
  | exact Iff.rfl
  | constructor
    · intro h
      obtain ⟨b, hb, e⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_toIntSubmodule.mp h)
      exact ⟨b, hb, e⟩
    · rintro ⟨b, hb, e⟩
      exact AddSubgroup.mem_toIntSubmodule.mpr (AddSubgroup.mem_map.mpr ⟨b, hb, e⟩)

lemma finite_small (hg : 0 < g) : {y | y ∈ Lc X g ∧ ‖y‖ < 1}.Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ 4
  have hpi : (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 4}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS
  refine (hpi.image fun γ => kap (X.embH fun i k => cE g * γ i k)).subset ?_
  rintro y ⟨hy, hn⟩
  obtain ⟨b, ⟨β, hβ, hγ, rfl⟩, rfl⟩ := (mem_Lc X g).mp hy
  choose γ hγi hγe using hγ
  have hcr := cr_ge (E := E) g hg
  have hcr0 := cr_pos (E := E) g hg
  have hb : IsHermFam (X.embH β) := embH_herm X hβ
  have hk : ∀ (τ : X.Ψ) (i k : Fin 2), |kap (X.embH β) τ i k| < 1 := fun τ i k => by
    have h := (norm_le_pi_norm (kap (X.embH β) τ i) k).trans
      ((norm_le_pi_norm (kap (X.embH β) τ) i).trans (norm_le_pi_norm (kap (X.embH β)) τ))
    rw [Real.norm_eq_abs] at h
    linarith
  have hre : ∀ (τ : X.Ψ) (i k : Fin 2), |(τ.1 (β i k)).re| < 1 ∧ |(τ.1 (β i k)).im| < 1 := by
    intro τ
    have h00 : |(τ.1 (β 0 0)).re| < 1 := by
      first | exact hk τ 0 0 | simpa [kap, Data.embH] using hk τ 0 0
    have h01 : |(τ.1 (β 0 1)).re| < 1 := by
      first | exact hk τ 0 1 | simpa [kap, Data.embH] using hk τ 0 1
    have h10 : |(τ.1 (β 0 1)).im| < 1 := by
      first | exact hk τ 1 0 | simpa [kap, Data.embH] using hk τ 1 0
    have h11 : |(τ.1 (β 1 1)).re| < 1 := by
      first | exact hk τ 1 1 | simpa [kap, Data.embH] using hk τ 1 1
    have e0 : τ.1 (β 0 0) = conj (τ.1 (β 0 0)) := hb τ 0 0
    have e1 : τ.1 (β 1 1) = conj (τ.1 (β 1 1)) := hb τ 1 1
    have e2 : τ.1 (β 1 0) = conj (τ.1 (β 0 1)) := hb τ 0 1
    have i0 : |(τ.1 (β 0 0)).im| < 1 := by
      have h := congrArg Complex.im e0
      rw [Complex.conj_im] at h
      have h' : (τ.1 (β 0 0)).im = 0 := by linarith
      rw [h']
      norm_num
    have i1 : |(τ.1 (β 1 1)).im| < 1 := by
      have h := congrArg Complex.im e1
      rw [Complex.conj_im] at h
      have h' : (τ.1 (β 1 1)).im = 0 := by linarith
      rw [h']
      norm_num
    have r2 : |(τ.1 (β 1 0)).re| < 1 := by rw [e2, Complex.conj_re]; exact h01
    have m2 : |(τ.1 (β 1 0)).im| < 1 := by rw [e2, Complex.conj_im, abs_neg]; exact h10
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · exact ⟨h00, i0⟩
    · exact ⟨h01, h10⟩
    · exact ⟨r2, m2⟩
    · exact ⟨h11, i1⟩
  have hΨ : ∀ (τ : X.Ψ) (i k : Fin 2), ‖τ.1 (γ i k)‖ ≤ 4 := by
    intro τ i k
    have h2 : ‖τ.1 (β i k)‖ < 2 := by
      have hn1 := Complex.norm_le_abs_re_add_abs_im (τ.1 (β i k))
      have hr := hre τ i k
      linarith [hr.1, hr.2]
    have e : τ.1 (β i k) = (cr (E := E) g : ℂ) * τ.1 (γ i k) := by
      rw [hγe i k, map_mul]
      congr 1
      exact emb_cE g τ.1
    have en : ‖τ.1 (β i k)‖ = cr (E := E) g * ‖τ.1 (γ i k)‖ := by
      rw [e, norm_mul]
      congr 1
      simp [abs_of_pos hcr0]
    rw [en] at h2
    nlinarith [norm_nonneg (τ.1 (γ i k))]
  refine ⟨γ, ?_, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies, forall_const, Set.mem_setOf_eq]
    intro i k
    refine ⟨hγi i k, fun φ => ?_⟩
    by_cases hφ : φ ∈ X.Ψ
    · exact hΨ ⟨φ, hφ⟩ i k
    · have hc : ComplexEmbedding.conjugate φ ∈ X.Ψ := by
        by_contra h
        exact hφ ((X.cmType φ).mpr h)
      have := hΨ ⟨_, hc⟩ i k
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  · have hfun : (fun i k => cE (E := E) g * γ i k) = β := by
      funext i k
      exact (hγe i k).symm
    exact congrArg (fun β' => kap (X.embH β')) hfun

instance Lc_discrete [Fact (0 < g)] : DiscreteTopology (Lc X g) := by
  have hg : 0 < g := Fact.out
  rw [discreteTopology_iff_isOpen_singleton_zero]
  set T := {y : X.Ψ → Fin 2 → Fin 2 → ℝ | y ∈ Lc X g ∧ ‖y‖ < 1} \ {0}
  have hT : IsClosed T := ((finite_small X g hg).subset Set.sdiff_subset).isClosed
  have h0 : (0 : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ Tᶜ := by simp [T]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT.isOpen_compl 0 h0
  rw [Metric.isOpen_iff]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  refine ⟨min ε 1, lt_min hε one_pos, fun q hq => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hq
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  have hq' : ‖(q : X.Ψ → Fin 2 → Fin 2 → ℝ)‖ < min ε 1 := by simpa using hq
  by_contra hne
  have hmem : (q : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ T :=
    ⟨⟨q.2, lt_of_lt_of_le hq' (min_le_right _ _)⟩, hne⟩
  have : (q : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ Metric.ball (0 : X.Ψ → Fin 2 → Fin 2 → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq' (min_le_left _ _)
  exact hball this hmem

lemma span_fixed_integral_real_parts : Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
    p = fun τ => (τ.1 a).re} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hf : ∀ p : X.Ψ → ℝ, f p = ∑ τ, p τ * f (fun j => if τ = j then 1 else 0) := by
    intro p
    rw [LinearMap.pi_apply_eq_sum_univ f p]
    simp only [smul_eq_mul]
  obtain ⟨lam, hlam⟩ : ∃ lam : X.Ψ → ℝ, ∀ p : X.Ψ → ℝ, f p = ∑ τ, p τ * lam τ := ⟨_, hf⟩
  have hinv : ∀ y : E, cc (cc y) = y := by
    intro y
    first
    | exact NumberField.IsCMField.complexConj_apply_apply E y
    | exact NumberField.IsCMField.complexConj_apply_apply y
    | simp [cc]
  have hvan : ∀ x : 𝓞 E, ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ = 0 := by
    intro x
    have hx : IsIntegral ℤ (x : E) := by
      first
      | exact x.isIntegral_coe
      | exact NumberField.RingOfIntegers.isIntegral_coe x
      | exact x.2
    have hcx : IsIntegral ℤ (cc (x : E)) := by
      first
      | exact hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
      | exact hx.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)
    have hr : cc ((x : E) + cc (x : E)) = (x : E) + cc (x : E) := by
      rw [show cc ((x : E) + cc (x : E)) = cc (x : E) + cc (cc (x : E)) from map_add _ _ _, hinv,
        add_comm]
    have hmem : (fun τ : X.Ψ => (τ.1 ((x : E) + cc (x : E))).re) ∈ Submodule.span ℝ
        {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧ p = fun τ => (τ.1 a).re} :=
      Submodule.subset_span ⟨_, hr, hx.add hcx, rfl⟩
    have h := hfS hmem
    rw [LinearMap.mem_ker, hlam] at h
    have e : ∀ τ : X.Ψ, (τ.1 ((x : E) + cc (x : E))).re = 2 * (τ.1 (x : E)).re := by
      intro τ
      rw [map_add, show τ.1 (cc (x : E)) = conj (τ.1 (x : E)) from
        NumberField.IsCMField.complexEmbedding_complexConj E τ.1 (x : E), Complex.add_re, Complex.conj_re]
      ring
    simp only [e] at h
    have h2 : ∑ τ : X.Ψ, 2 * (τ.1 (x : E)).re * lam τ = 2 * ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring
    linarith
  have hmh : ∀ φ ψ : 𝓞 E →+* ℂ, φ.toMonoidHom = ψ.toMonoidHom → φ = ψ := fun φ ψ h =>
    RingHom.ext fun x => DFunLike.congr_fun h x
  have hext : ∀ φ ψ : E →+* ℂ, φ.comp (algebraMap (𝓞 E) E) = ψ.comp (algebraMap (𝓞 E) E) → φ = ψ :=
    fun φ ψ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  have hcc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
    intro φ
    first
    | exact ComplexEmbedding.conjugate_conjugate φ
    | exact star_star φ
    | (ext y; simp [ComplexEmbedding.conjugate_coe_eq])
  have hFinj : Function.Injective
      (Sum.elim (fun τ : X.Ψ => τ.1) (fun τ : X.Ψ => ComplexEmbedding.conjugate τ.1)) := by
    rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h' : τ.1 = ComplexEmbedding.conjugate τ'.1 := h
      have h1 : ComplexEmbedding.conjugate τ'.1 ∈ X.Ψ := by
        rw [← h']
        exact τ.2
      exact ((X.cmType τ'.1).mp τ'.2) h1
    · exfalso
      have h' : ComplexEmbedding.conjugate τ.1 = τ'.1 := h
      have h1 : ComplexEmbedding.conjugate τ.1 ∈ X.Ψ := by
        rw [h']
        exact τ'.2
      exact ((X.cmType τ.1).mp τ.2) h1
    · have h' : ComplexEmbedding.conjugate τ.1 = ComplexEmbedding.conjugate τ'.1 := h
      have h1 : τ.1 = τ'.1 := by
        have h2 := congrArg ComplexEmbedding.conjugate h'
        rwa [hcc, hcc] at h2
      exact congrArg Sum.inr (Subtype.ext h1)
  have hGinj : Function.Injective (fun t : X.Ψ ⊕ X.Ψ =>
      ((Sum.elim (fun τ : X.Ψ => τ.1) (fun τ : X.Ψ => ComplexEmbedding.conjugate τ.1) t).comp
        (algebraMap (𝓞 E) E)).toMonoidHom) := by
    intro t t' h
    exact hFinj (hext _ _ (hmh _ _ h))
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hGinj
  rw [Fintype.linearIndependent_iff] at hli
  have hzero := hli (Sum.elim (fun τ => (lam τ : ℂ)) (fun τ => (lam τ : ℂ))) (by
    funext x
    have key : ∑ τ : X.Ψ, (lam τ : ℂ) * (τ.1 (x : E) + conj (τ.1 (x : E))) = 0 := by
      have h := hvan x
      simp only [Complex.add_conj]
      have h3 : ∑ τ : X.Ψ, (lam τ : ℂ) * ((2 * (τ.1 (x : E)).re : ℝ) : ℂ) =
          ((2 * ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ : ℝ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        ring
      rw [h3, h, mul_zero, Complex.ofReal_zero]
    rw [Finset.sum_apply, Fintype.sum_sum_type]
    show ∑ τ : X.Ψ, (lam τ : ℂ) * τ.1 (x : E) +
      ∑ τ : X.Ψ, (lam τ : ℂ) * (ComplexEmbedding.conjugate τ.1) (x : E) = 0
    simp only [ComplexEmbedding.conjugate_coe_eq, ← Finset.sum_add_distrib, ← mul_add]
    exact key)
  have hl : ∀ τ, lam τ = 0 := fun τ => by
    have h := hzero (Sum.inl τ)
    simpa using h
  exact hf0 (LinearMap.ext fun p => by rw [hlam]; simp [hl])

lemma span_gen (T : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → Fin 2 → Fin 2 → ℝ))
    (hT : ∀ a : E, cc a = a → IsIntegral ℤ a →
      T (fun τ => (τ.1 a).re) ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)))
    (p : X.Ψ → ℝ) : T p ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) := by
  have hp : p ∈ Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => (τ.1 a).re} := by
    rw [span_fixed_integral_real_parts X]
    exact Submodule.mem_top
  have hle : Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => (τ.1 a).re} ≤
      (Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ))).comap T := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, hi, rfl⟩
    exact hT a ha hi
  exact hle hp

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
