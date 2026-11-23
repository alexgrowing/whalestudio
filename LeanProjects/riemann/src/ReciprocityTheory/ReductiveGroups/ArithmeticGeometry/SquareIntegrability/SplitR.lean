import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section rk

variable {dim : (E →+* ℂ) → ℕ}

theorem rk_act_apply (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) : act α v i = i.1 (α : E) * v i := rfl

theorem rk_act_sum {J : Type} [Fintype J] (c : J → ℤ) (ω : J → 𝓞 E) (v : Vsp dim) :
    act (∑ j, c j • ω j) v = ∑ j, c j • act (ω j) v := by
  ext i
  simp [rk_act_apply, Finset.sum_mul, mul_assoc]

theorem rk_act_natCast (n : ℕ) (v : Vsp dim) : act (n : 𝓞 E) v = (n : ℤ) • v := by
  ext i
  simp [rk_act_apply]

theorem rk_act_zsmul (α : 𝓞 E) (n : ℤ) (v : Vsp dim) : act α (n • v) = n • act α v := by
  ext i
  simp [rk_act_apply] <;> ring

theorem rk_act_zero (α : 𝓞 E) : act α (0 : Vsp dim) = 0 := by
  ext i
  simp [rk_act_apply]

def rkFam {ρ : ℕ} (e : Fin ρ → Vsp dim) (p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin ρ) :
    Vsp dim :=
  act (RingOfIntegers.basis E p.1) (e p.2)

theorem rkFam_span_stable {ρ : ℕ} (e : Fin ρ → Vsp dim) (γ : 𝓞 E) (y : Vsp dim)
    (hy : y ∈ Submodule.span ℤ (Set.range (rkFam e))) :
    act γ y ∈ Submodule.span ℤ (Set.range (rkFam e)) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    have hmul : act γ (rkFam e p) = act (γ * RingOfIntegers.basis E p.1) (e p.2) := by
      ext i
      simp [rkFam, rk_act_apply, mul_assoc]
    rw [hmul, ← (RingOfIntegers.basis E).sum_repr (γ * RingOfIntegers.basis E p.1), rk_act_sum]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l, p.2), rfl⟩)
  | zero =>
    rw [rk_act_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have hxy : act γ (x + y) = act γ x + act γ y := by
      ext i
      simp [rk_act_apply, mul_add]
    rw [hxy]
    exact Submodule.add_mem _ hx hy
  | smul n x _ hx =>
    rw [rk_act_zsmul]
    exact Submodule.smul_mem _ n hx

def rkP (τ : E →+* ℂ) : Vsp dim →ₗ[ℂ] (Fin (dim τ) → ℂ) where
  toFun v a := v ⟨τ, a⟩
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp

open Classical in

def rkQ (τ : E →+* ℂ) : (Fin (dim τ) → ℂ) →ₗ[ℂ] Vsp dim where
  toFun y := ∑ a, y a • EuclideanSpace.single (⟨τ, a⟩ : Idx dim) (1 : ℂ)
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.smul_sum, smul_smul]

open Classical in
theorem rkQP_apply (τ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    rkQ τ (rkP τ v) i = if i.1 = τ then v i else 0 := by
  obtain ⟨σ, b⟩ := i
  by_cases h : σ = τ
  · subst h
    simp [rkQ, rkP, EuclideanSpace.single_apply, Sigma.mk.inj_iff]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      rw [Pi.single_apply, if_neg]
      · simp
      · intro h
        apply hx
        exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · intro h
      exact absurd (Finset.mem_univ b) h
  · simp [rkQ, rkP, EuclideanSpace.single_apply, Sigma.mk.inj_iff, h]

end rk

theorem rk_li_real (X : PT E) {ι : Type} [Fintype ι] (u : ι → Vsp X.dim) (hu : ∀ i, u i ∈ X.L)
    (hli : LinearIndependent ℤ u) : LinearIndependent ℝ u := by
  classical
  have hc : ∀ i k, ∃ n : ℤ, (n : ℝ) = X.b.repr (u i) k := fun i k => by
    obtain ⟨n, hn⟩ := (X.b.mem_span_iff_repr_mem ℤ (u i)).1 (hu i) k
    exact ⟨n, by simpa using hn⟩
  choose v hv using hc
  have hu' : ∀ i, X.b.equivFun.symm (fun k => algebraMap ℤ ℝ (v i k)) = u i := fun i =>
    X.b.equivFun.symm_apply_eq.2 (funext fun k => by simp [hv])
  have h1 : LinearIndependent ℤ v := by
    have heq : u = (X.b.equivFun.symm.toLinearMap.restrictScalars ℤ).comp
        ((Algebra.linearMap ℤ ℝ).compLeft _) ∘ v := by
      funext i; rw [← hu' i]; rfl
    rw [heq] at hli
    exact hli.of_comp
  have h2 : LinearIndependent ℝ (fun i => algebraMap ℤ ℝ ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' X.b.equivFun.symm.toLinearMap (LinearEquiv.ker _)
  have heq2 : u = X.b.equivFun.symm.toLinearMap ∘ (fun i => algebraMap ℤ ℝ ∘ v i) := by
    funext i; exact (hu' i).symm
  rw [heq2]
  exact h3

theorem rank_iso [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) :
    ∃ ρ, (∀ τ, ρ ≤ X.dim τ) ∧ Module.finrank ℝ (IR I) = 2 * PT.f E * ρ := by
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  have hJ : Fintype.card J = Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hdeg : Module.finrank ℚ E = 2 * PT.f E := by
    have := IsTotallyComplex.finrank (K := E)
    unfold PT.f; omega
  have hJpos : 0 < Fintype.card J := by rw [hJ]; exact Module.finrank_pos
  have hfam_mem : ∀ {ρ : ℕ} (e : Fin ρ → Vsp X.dim), (∀ k, e k ∈ I) → ∀ p, rkFam e p ∈ I :=
    fun e he p => hst _ _ (he p.2)
  let P : ℕ → Prop := fun ρ =>
    ∃ e : Fin ρ → Vsp X.dim, (∀ k, e k ∈ I) ∧ LinearIndependent ℤ (rkFam e)
  have hbound : ∀ ρ, P ρ → Fintype.card J * ρ ≤ Module.finrank ℝ (Vsp X.dim) := by
    rintro ρ ⟨e, he, hli⟩
    have h := (rk_li_real X (rkFam e) (fun p => hle (hfam_mem e he p)) hli).fintype_card_le_finrank
    simpa [Fintype.card_prod] using h
  have hP0 : P 0 := ⟨Fin.elim0, fun k => k.elim0, linearIndependent_empty_type⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Nat.findGreatest P (Module.finrank ℝ (Vsp X.dim)) := ⟨_, rfl⟩
  have hPρ : P ρ := hρ ▸ Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hnot : ¬ P (ρ + 1) := by
    by_cases h : ρ + 1 ≤ Module.finrank ℝ (Vsp X.dim)
    · rw [hρ] at h ⊢
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h
    · intro hP
      have h1 := hbound _ hP
      have h2 : ρ + 1 ≤ Fintype.card J * (ρ + 1) := Nat.le_mul_of_pos_left _ hJpos
      omega
  obtain ⟨e, he, hli⟩ := hPρ

  have key : ∀ x ∈ I, x ∈ Submodule.span ℝ (Set.range (rkFam e)) := by
    intro x hx
    let e' : Fin (ρ + 1) → Vsp X.dim := Fin.cons x e
    have he' : ∀ k, e' k ∈ I := by
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa [e'] using hx
      · simpa [e'] using he k
    have hdep : ¬ LinearIndependent ℤ (rkFam e') := fun h => hnot ⟨e', he', h⟩
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i0, hi0⟩ := hdep
    have hsplit : ∑ p, g p • rkFam e' p = ∑ j, g (j, 0) • act (RingOfIntegers.basis E j) x +
        ∑ p : J × Fin ρ, g (p.1, p.2.succ) • rkFam e p := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Fin.sum_univ_succ]
      rw [Finset.sum_add_distrib]
      simp only [rkFam, e', Fin.cons_zero, Fin.cons_succ]
      rfl
    rw [hsplit] at hg
    by_cases hβ : ∀ j, g (j, 0) = 0
    · have h0 : ∑ p : J × Fin ρ, g (p.1, p.2.succ) • rkFam e p = 0 := by
        simpa [hβ] using hg
      have h1 := Fintype.linearIndependent_iff.1 hli _ h0
      obtain ⟨j, k⟩ := i0
      exfalso
      apply hi0
      induction k using Fin.cases with
      | zero => exact hβ j
      | succ k => exact h1 (j, k)
    · simp only [not_forall] at hβ
      obtain ⟨j0, hj0⟩ := hβ
      obtain ⟨β, hβdef⟩ : ∃ β : 𝓞 E, β = ∑ j, g (j, 0) • RingOfIntegers.basis E j := ⟨_, rfl⟩
      have hβ0 : β ≠ 0 := fun h => hj0 (Fintype.linearIndependent_iff.1
        (RingOfIntegers.basis E).linearIndependent _ (hβdef ▸ h) j0)
      have hact : act β x = -∑ p : J × Fin ρ, g (p.1, p.2.succ) • rkFam e p := by
        rw [hβdef, rk_act_sum]; exact eq_neg_of_add_eq_zero_left hg
      have hβS : act β x ∈ Submodule.span ℤ (Set.range (rkFam e)) := by
        rw [hact]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun p _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
      obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {β}))
      have hN : Ideal.absNorm (Ideal.span {β}) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
      have hNx : ((Ideal.absNorm (Ideal.span {β}) : ℤ) • x) ∈
          Submodule.span ℤ (Set.range (rkFam e)) := by
        have := rkFam_span_stable e γ _ hβS
        rwa [← act_mul', hγ, rk_act_natCast] at this
      have h2 : (((Ideal.absNorm (Ideal.span {β}) : ℤ) : ℝ) • x) ∈
          Submodule.span ℝ (Set.range (rkFam e)) := by
        rw [Int.cast_smul_eq_zsmul]
        exact Submodule.span_le_restrictScalars ℤ ℝ _ hNx
      have h3 := (Submodule.span ℝ (Set.range (rkFam e))).smul_mem
        (((Ideal.absNorm (Ideal.span {β}) : ℤ) : ℝ))⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul] at h3
  have hIR : IR I = Submodule.span ℝ (Set.range (rkFam e)) := by
    apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => key x hx
    · exact Submodule.span_le.2
        (by rintro _ ⟨p, rfl⟩; exact Submodule.subset_span (hfam_mem e he p))
  have hR := rk_li_real X (rkFam e) (fun p => hle (hfam_mem e he p)) hli
  have hcard : Fintype.card (J × Fin ρ) = 2 * PT.f E * ρ := by
    rw [Fintype.card_prod, Fintype.card_fin, hJ, hdeg]

  have hC : LinearIndependent ℂ (rkFam e) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hmem : ∀ q, rkFam e q ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) :=
      fun q => Submodule.subset_span (hfam_mem e he q)
    obtain ⟨A, hAdef⟩ : ∃ A : Vsp X.dim, A = ∑ q, (g q).re • rkFam e q := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : Vsp X.dim, B = ∑ q, (g q).im • rkFam e q := ⟨_, rfl⟩
    have hA : A ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) :=
      hAdef ▸ Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hmem q)
    have hB : B ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) :=
      hBdef ▸ Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hmem q)
    have hAB : A + Complex.I • B = 0 := by
      rw [hAdef, hBdef, ← hg, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      rw [mul_comm]
      exact Complex.re_add_im _
    have hA' : A = -(Complex.I • B) := eq_neg_of_add_eq_zero_left hAB
    have him := Hf_im_span_iso (I : Set (Vsp X.dim)) (fun v hv w hw => hiso v hv w hw) B hB A hA
    rw [Hf_im_eq, hA', smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg,
      real_inner_self_eq_norm_sq] at him
    have hB0 : B = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 him)
    have hA0 : A = 0 := by rw [hA', hB0, smul_zero, neg_zero]
    have hre := Fintype.linearIndependent_iff.1 hR _ (hAdef ▸ hA0) p
    have him' := Fintype.linearIndependent_iff.1 hR _ (hBdef ▸ hB0) p
    exact Complex.ext hre him'

  let W : (E →+* ℂ) × Fin ρ → Vsp X.dim := fun q => rkQ q.1 (rkP q.1 (e q.2))
  have hfamW : ∀ p : J × Fin ρ,
      rkFam e p = ∑ σ : E →+* ℂ, σ (RingOfIntegers.basis E p.1 : E) • W (σ, p.2) := by
    intro p
    ext i
    simp [W, rkFam, rk_act_apply, rkQP_apply, mul_ite, Finset.sum_ite_eq]
  have hspan : Submodule.span ℂ (Set.range (rkFam e)) ≤ Submodule.span ℂ (Set.range W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    rw [hfamW p]
    exact Submodule.sum_mem _ fun σ _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(σ, p.2), rfl⟩)
  have hEmb : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := NumberField.Embeddings.card E ℂ
  have hW : LinearIndependent ℂ W := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    apply le_antisymm
    · calc Fintype.card ((E →+* ℂ) × Fin ρ) = Fintype.card (J × Fin ρ) := by
            simp only [Fintype.card_prod, hEmb, hJ]
        _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (rkFam e))) :=
            (finrank_span_eq_card hC).symm
        _ ≤ (Set.range W).finrank ℂ := Submodule.finrank_mono hspan
    · exact finrank_range_le_card W
  refine ⟨ρ, fun τ => ?_, by rw [hIR, finrank_span_eq_card hR, hcard]⟩
  have hWτ : LinearIndependent ℂ (fun k => W (τ, k)) :=
    hW.comp _ (fun a b h => by simpa using h)
  have hPτ : LinearIndependent ℂ (fun k => rkP τ (e k)) := by
    have h1 : (fun k => W (τ, k)) = rkQ τ ∘ fun k => rkP τ (e k) := rfl
    rw [h1] at hWτ
    exact hWτ.of_comp
  simpa using hPτ.fintype_card_le_finrank

end

end ReciprocityTheory.ChartRestriction.G.I2
