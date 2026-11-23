import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate

open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace SelfDualClasses

open ShortVectors

noncomputable def hermRat (n : ℕ) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] E :=
  LinearMap.mk₂ ℚ (fun x y => herm 1 x y)
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])

theorem hermRat_apply {n : ℕ} (x y : Fin n → E) : hermRat n x y = herm 1 x y := rfl

theorem exists_isometry {n : ℕ} {ι : Type} (b b' : Basis ι ℚ (Fin n → E))
    (h : ∀ i j, herm 1 (b' i) (b' j) = herm 1 (b i) (b j)) :
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧
      ∀ i, γ (b i) = b' i := by
  let g : (Fin n → E) ≃ₗ[ℚ] (Fin n → E) := b.equiv b' (Equiv.refl ι)
  have hg : ∀ x y, herm 1 (g x) (g y) = herm 1 x y := by
    have : (hermRat n).compl₁₂ g.toLinearMap g.toLinearMap = hermRat (E := E) n :=
      LinearMap.ext_basis b b fun i j => by simp [g, hermRat_apply, h]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  have hs : ∀ (c : E) x, g (c • x) = c • g x := by
    intro c x
    rw [← sub_eq_zero]
    refine (traceHerm_nondegenerate n).1 _ fun z => ?_
    obtain ⟨y, rfl⟩ := g.surjective z
    rw [map_sub, LinearMap.sub_apply, traceHerm_apply, traceHerm_apply, hg,
      TraceDualMin.herm_smul_left, TraceDualMin.herm_smul_left, hg, sub_self]
  exact ⟨{ g.toAddEquiv with map_smul' := hs }, hg, fun i => by simp [g]⟩

theorem finite_integral_of_basis {n : ℕ} {ι : Type} [Fintype ι] (b : Basis ι ℚ (Fin n → E)) :
    {Λ : Submodule (𝓞 E) (Fin n → E) | (∀ i, b i ∈ Λ) ∧
      ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)}.Finite := by
  classical
  let L₀ : Submodule ℤ (Fin n → E) := span ℤ (Set.range b)
  let L₁ : Submodule ℤ (Fin n → E) := (traceHerm n).dualSubmodule L₀
  have hfg : L₁.FG := by
    simp only [L₁, L₀]
    rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ (traceHerm_nondegenerate n)]
    exact fg_span (Set.finite_range _)
  have : Module.Finite ℤ L₁ := Module.Finite.iff_fg.mpr hfg
  have : Finite (L₁ ⧸ L₀.submoduleOf L₁) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : (x : Fin n → E) ∈ span ℚ (Set.range b) := b.mem_span _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ _ _ hx
    refine ⟨t, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ht
  have h0 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) → ∀ x ∈ L₀, x ∈ Λ := by
    intro Λ hΛ
    have : L₀ ≤ Λ.restrictScalars ℤ := span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact this
  have h1 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → ∀ x ∈ Λ, x ∈ L₁ := by
    intro Λ hΛ hint x hx y hy
    have := Algebra.isIntegral_trace (L := ℚ) (hint x hx y (h0 Λ hΛ y hy))
    rw [Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp this
  let F : Submodule (𝓞 E) (Fin n → E) → Set (L₁ ⧸ L₀.submoduleOf L₁) :=
    fun Λ => {q | ∃ x : L₁, (x : Fin n → E) ∈ Λ ∧ Submodule.Quotient.mk x = q}
  have key : ∀ Λ Λ' : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ i, b i ∈ Λ') → F Λ = F Λ' → Λ ≤ Λ' := by
    intro Λ Λ' hΛ hint hΛ' hF x hx
    have : Submodule.Quotient.mk ⟨x, h1 Λ hΛ hint x hx⟩ ∈ F Λ := ⟨_, hx, rfl⟩
    rw [hF] at this
    obtain ⟨y, hy, hq⟩ := this
    rw [Submodule.Quotient.eq] at hq
    have h2 : (y : Fin n → E) - x ∈ Λ' := h0 Λ' hΛ' _ hq
    simpa using Λ'.sub_mem hy h2
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro Λ ⟨hΛ, hi⟩ Λ' ⟨hΛ', hi'⟩ hF
  exact le_antisymm (key _ _ hΛ hi hΛ' hF) (key _ _ hΛ' hi' hΛ hF.symm)

theorem norm_herm_le {n : ℕ} (τ : E →+* ℂ) (x y : Fin n → E) (C : ℝ)
    (hx : ∑ k, ‖τ (x k)‖ ^ 2 ≤ C) (hy : ∑ k, ‖τ (y k)‖ ^ 2 ≤ C) : ‖τ (herm 1 x y)‖ ≤ C := by
  have h : ‖τ (herm 1 x y)‖ ≤ ∑ k, (‖τ (x k)‖ ^ 2 + ‖τ (y k)‖ ^ 2) / 2 := by
    rw [DualFamily.herm_one_eq, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have : ‖τ (cc (y k))‖ = ‖τ (y k)‖ := by
      simp [cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, norm_mul, this]
    nlinarith [sq_nonneg (‖τ (x k)‖ - ‖τ (y k)‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith

theorem finite_linearMap {R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T] [Module.Finite R M] [Finite T] : Finite (M →ₗ[R] T) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
  refine Finite.of_injective
    (fun (g : M →ₗ[R] T) (i : Fin m) => g (f (Pi.basisFun R (Fin m) i))) fun g g' h => ?_
  rw [← LinearMap.cancel_right hf]
  exact (Pi.basisFun R (Fin m)).ext fun i => congrFun h i

end SelfDualClasses

open SelfDualClasses in

theorem finite_classes_selfDual_of_selfDual (n : ℕ) :
    ∃ S : Finset (Submodule (𝓞 E) (Fin n → E)),
    (∀ Λ ∈ S, Λ.FG ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∃ Λ₀ ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∀ x, x ∈ Λ₀ ↔ γ x ∈ Λ := by
  classical
  set C : ℝ := (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 with hC
  let ι := Fin (2 * fdeg E * n)
  let A : Set E := {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C}
  have hA : A.Finite := Embeddings.finite_of_norm_le E ℂ C
  let gram : Basis ι ℚ (Fin n → E) → ι → ι → E := fun b i j => herm 1 (b i) (b j)
  let B : Set (Basis ι ℚ (Fin n → E)) := {b | ∀ i j, gram b i j ∈ A}
  have hG : (gram '' B).Finite := by
    refine (Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => hA).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hb
  obtain ⟨B₀, -, hB₀fin, hB₀⟩ := Set.exists_subset_image_finite_and.mp
    (⟨gram '' B, subset_rfl, hG, rfl⟩ : ∃ t ⊆ gram '' B, t.Finite ∧ t = gram '' B)
  have hS : {Λ : Submodule (𝓞 E) (Fin n → E) | (∃ b ∈ B₀, ∀ i, b i ∈ Λ) ∧ Λ.FG ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ}.Finite := by
    refine (hB₀fin.biUnion fun b _ => finite_integral_of_basis b).subset ?_
    rintro Λ ⟨⟨b, hb, hbΛ⟩, -, hi, -⟩
    exact Set.mem_biUnion hb ⟨hbΛ, hi⟩
  refine ⟨hS.toFinset, fun Λ hΛ => (hS.mem_toFinset.mp hΛ).2, fun Λ hfg hint hdual => ?_⟩
  obtain ⟨v, hv, hli, hsp, hle⟩ := exists_short_vectors Λ hfg hint hdual
  let b : Basis ι ℚ (Fin n → E) := Basis.mk hli hsp.ge
  have hb : ∀ i, b i = v i := fun i => Basis.mk_apply _ _ i
  have hbB : gram b ∈ gram '' B₀ := by
    rw [hB₀]
    refine ⟨b, fun i j => ?_, rfl⟩
    simp only [gram, hb]
    exact ⟨hint _ (hv i) _ (hv j), fun φ => norm_herm_le φ _ _ C (hle i φ) (hle j φ)⟩
  obtain ⟨b₀, hb₀, hgram⟩ := hbB
  obtain ⟨γ, hγ, hγb⟩ := exists_isometry b₀ b fun i j => (congrFun₂ hgram i j).symm
  let γ' : (Fin n → E) ≃ₗ[𝓞 E] (Fin n → E) := γ.restrictScalars (𝓞 E)
  refine ⟨Λ.comap γ'.toLinearMap, hS.mem_toFinset.mpr ⟨⟨b₀, hb₀, fun i => ?_⟩, ?_, ?_, ?_⟩,
    γ, hγ, fun x => Iff.rfl⟩
  · change γ (b₀ i) ∈ Λ
    rw [hγb, hb]
    exact hv i
  · rw [Submodule.comap_equiv_eq_map_symm]
    exact hfg.map _
  · intro x hx y hy
    rw [← hγ]
    exact hint _ hx _ hy
  · intro x hx
    refine hdual (γ x) fun y hy => ?_
    obtain ⟨z, rfl⟩ := γ.surjective y
    rw [hγ]
    exact hx z hy

theorem finite_classes_selfDual_pairs (n : ℕ) (T : Type) [AddCommGroup T] [Module (𝓞 E) T]
    [Finite T] :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ f : Λ →ₗ[𝓞 E] T,
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  classical
  obtain ⟨S, hS, hcl⟩ := finite_classes_selfDual_of_selfDual (E := E) n
  have hfin : {P : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T | P.1 ∈ S}.Finite := by
    refine (S.finite_toSet.biUnion (t := fun Λ => Set.range
      fun f : Λ →ₗ[𝓞 E] T => (⟨Λ, f⟩ : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T))
      fun Λ hΛ => ?_).subset ?_
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr (hS Λ hΛ).1
      have : Finite (Λ →ₗ[𝓞 E] T) := SelfDualClasses.finite_linearMap
      exact Set.finite_range _
    · rintro ⟨Λ, f⟩ h
      exact Set.mem_biUnion h ⟨f, rfl⟩
  refine ⟨hfin.toFinset, fun P hP => hS _ (hfin.mem_toFinset.mp hP), fun Λ h1 h2 h3 f => ?_⟩
  obtain ⟨Λ₀, hΛ₀, γ, hγ, h⟩ := hcl Λ h1 h2 h3
  exact ⟨⟨Λ₀, f ∘ₗ (γ.restrictScalars (𝓞 E)).toLinearMap.restrict fun x hx => (h x).mp hx⟩,
    hfin.mem_toFinset.mpr hΛ₀, γ, hγ, h, fun x => rfl⟩

theorem finite_classes_selfDual_level (n N : ℕ) (hN : N ≠ 0) :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E),
      Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∀ f : Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}),
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  exact finite_classes_selfDual_pairs n _

end GlobalTheory
