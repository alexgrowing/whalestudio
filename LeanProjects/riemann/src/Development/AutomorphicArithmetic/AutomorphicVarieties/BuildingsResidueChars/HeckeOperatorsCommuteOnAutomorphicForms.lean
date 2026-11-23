import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem finite_translation_mul (g h : GL (Fin a) (Af F)) (φ : TR.Sm F a) :
    TR.finRep F a (g * h) φ = TR.finRep F a g (TR.finRep F a h φ) := by
  rw [map_mul]; rfl

private theorem center_algebra_translation_comm (g : GL (Fin a) (Af F)) {z : Module.End ℂ (TR.Sm F a)} (hz : z ∈ TR.Zalg F a) :
    TR.finRep F a g * z = z * TR.finRep F a g := by
  have key : TR.Zalg F a ≤ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    have hE : ∀ i j, TR.Eop v i j ∈ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
      intro i j
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (TR.lie_rt_fin _ g).symm
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (key hz) _ rfl

private theorem compact_finite_translation_comm (g : GL (Fin a) (Af F)) (k : TR.Kinf F a) (φ : TR.Sm F a) :
    TR.cptRep F a k (TR.finRep F a g φ) = TR.finRep F a g (TR.cptRep F a k φ) := by
  refine Subtype.ext (funext fun x => ?_)
  change φ.1 (x * TR.infGL F a (Unitary.toUnits k) * finGL F a g) =
    φ.1 (x * finGL F a g * TR.infGL F a (Unitary.toUnits k))
  rw [mul_assoc, mul_assoc, TR.infGL_comm]

private theorem automorphic_form_translate (φ : TR.Sm F a) (g : GL (Fin a) (Af F)) (h : TR.IsAutForm φ) :
    TR.IsAutForm (TR.finRep F a g φ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 (ratGL F a γ * x * finGL F a g) = φ.1 (x * finGL F a g)
    rw [mul_assoc, h.left]
  · have e : {k | TR.finRep F a k (TR.finRep F a g φ) = TR.finRep F a g φ} =
        (fun k => g⁻¹ * k * g) ⁻¹' {k | TR.finRep F a k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hk
        rw [finite_translation_mul, finite_translation_mul, hk, ← finite_translation_mul, inv_mul_cancel, map_one]
        rfl
      · intro hk
        have := congrArg (TR.finRep F a g) hk
        rwa [← finite_translation_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, finite_translation_mul] at this
    rw [e]
    exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ)).map (TR.finRep F a g)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (compact_finite_translation_comm g k φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (TR.finRep F a g))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, LinearMap.congr_fun (center_algebra_translation_comm g hz) φ⟩
  · obtain ⟨C, N, hC⟩ := h.growth (x * finGL F a g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (x * TR.infGL F a y * finGL F a g)‖ ≤ _
    rw [mul_assoc, TR.infGL_comm, ← mul_assoc]
    exact hC y

private theorem automorphic_form_linear_combination (φ ψ : TR.Sm F a) (c : ℂ) (h : TR.IsAutForm φ) (h' : TR.IsAutForm ψ) :
    TR.IsAutForm (φ + c • ψ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 _ + c * ψ.1 _ = φ.1 _ + c * ψ.1 _
    rw [h.left, h'.left]
  · rw [isOpen_iff_mem_nhds]
    intro k₀ hk₀
    have hO : IsOpen ((fun k => k₀⁻¹ * k) ⁻¹' ({k | TR.finRep F a k φ = φ} ∩ {k | TR.finRep F a k ψ = ψ})) :=
      (h.level.inter h'.level).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
    · simp
    · rintro k ⟨h1, h2⟩
      have h1' : TR.finRep F a (k₀⁻¹ * k) φ = φ := h1
      have h2' : TR.finRep F a (k₀⁻¹ * k) ψ = ψ := h2
      have h3 : TR.finRep F a (k₀⁻¹ * k) (φ + c • ψ) = φ + c • ψ := by rw [map_add, map_smul, h1', h2']
      have h4 : TR.finRep F a k₀ (φ + c • ψ) = φ + c • ψ := hk₀
      change TR.finRep F a k (φ + c • ψ) = φ + c • ψ
      rw [← mul_inv_cancel_left k₀ k, finite_translation_mul, h3, h4]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ) ⊔
        Submodule.span ℂ (Set.range fun k => TR.cptRep F a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z ψ) '' TR.Zalg F a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
  · obtain ⟨C, N, hC⟩ := h.growth x
    obtain ⟨D, M, hD⟩ := h'.growth x
    refine ⟨|C| + ‖c‖ * |D|, N + M, fun y => ?_⟩
    have h1 : 1 ≤ TR.height y := by
      unfold TR.height
      have := norm_nonneg (TR.toL y.val)
      have := norm_nonneg (TR.toL (y⁻¹).val)
      linarith
    have bound : ∀ (B : ℝ) (n : ℕ), n ≤ N + M → B * TR.height y ^ n ≤ |B| * TR.height y ^ (N + M) := fun B n hn =>
      mul_le_mul (le_abs_self B) (pow_le_pow_right₀ h1 hn) (pow_nonneg (zero_le_one.trans h1) n) (abs_nonneg B)
    have b1 := (hC y).trans (bound C N (Nat.le_add_right _ _))
    have b2 := (hD y).trans (bound D M (Nat.le_add_left _ _))
    change ‖φ.1 _ + c * ψ.1 _‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul, mul_assoc]
    exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 (norm_nonneg c))

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_operators_commute_on_automorphic_forms :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), TR.IsAutForm (0 : TR.Sm F a) ∧ (∀ (φ : TR.Sm F a) (g : GL (Fin a) (Af F)), TR.IsAutForm φ → TR.IsAutForm (TR.finRep F a g φ)) ∧ ∀ (φ ψ : TR.Sm F a) (z : ℂ), TR.IsAutForm φ → TR.IsAutForm ψ → TR.IsAutForm (φ + z • ψ) := by
  intro F _ _ _ a
  exact ⟨TR.isAutForm_const (Submodule.zero_mem _), automorphic_form_translate, automorphic_form_linear_combination⟩
