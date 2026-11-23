import Formalism.LocalToGlobal.GlobalTheory.GL4.Statement

noncomputable section

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

theorem isIntegral_of_trace_pow_mul (E : Type) [Field E] [NumberField E] (x : E)
    (h : ∀ (n : ℕ) (b : 𝓞 E), Algebra.trace ℚ E (x ^ n * (b : E)) ∈ (algebraMap ℤ ℚ).range) :
    IsIntegral ℤ x := by
  classical
  let B := Algebra.traceForm ℚ E
  let b0 := NumberField.integralBasis E
  let Dl : Submodule ℤ E := B.dualSubmodule (Submodule.span ℤ (Set.range b0))
  have hDl : Dl = Submodule.span ℤ (Set.range (B.dualBasis (traceForm_nondegenerate ℚ E) b0)) :=
    LinearMap.BilinForm.dualSubmodule_span_of_basis B _ b0
  have hDfg : Dl.FG := by
    rw [hDl]; exact Submodule.fg_span (Set.finite_range _)
  let N : Submodule ℤ E := Submodule.span ℤ (Set.range (fun p : ℕ × 𝓞 E => x ^ p.1 * (p.2 : E)))
  have hND : N ≤ Dl := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨n, b⟩, rfl⟩
    intro y hy
    rw [NumberField.mem_span_integralBasis] at hy
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨z, hz⟩ := h n (b * c)
    refine Submodule.mem_one.2 ⟨z, ?_⟩
    rw [hz]
    show _ = Algebra.trace ℚ E (x ^ n * (b : E) * (c : E))
    push_cast [mul_assoc]
    rfl
  have hNfg : N.FG := by
    have hn : IsNoetherian ℤ Dl := isNoetherian_of_fg_of_noetherian Dl hDfg
    exact isNoetherian_submodule.1 hn N hND
  have hN0 : N ≠ ⊥ := by
    intro h0
    have : x ^ 0 * ((1 : 𝓞 E) : E) ∈ N := Submodule.subset_span ⟨(0, 1), rfl⟩
    rw [h0] at this
    simp at this
  refine isIntegral_of_smul_mem_submodule (A := E) N hN0 hNfg x fun n hn => ?_
  refine Submodule.span_induction (p := fun n _ => x • n ∈ N) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨⟨k, b⟩, rfl⟩
    refine Submodule.subset_span ⟨(k + 1, b), ?_⟩
    show x ^ (k + 1) * (b : E) = x * (x ^ k * (b : E))
    ring
  · simp
  · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
  · intro r a _ ha; rw [smul_comm]; exact N.smul_mem r ha

theorem mem_int_of_adele (F : Type) [Field F] [NumberField F] (y : F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) y ∈ intAd F) : y ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro v
  have := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  exact this

section Tens

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem mul_mem_pureClosure {R : Type} [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R)
    {m m' : E ⊗[F] R}
    (hm : m ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r})
    (hm' : m' ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r}) :
    m * m' ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r} := by
  induction hm using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, r, hr, rfl⟩ := hx
    induction hm' using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', r', hr', rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a * a', S₁.mul_mem ha ha', r * r', S₂.mul_mem hr hr',
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y y' _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem tensInt_le_pureClosure {R : Type} [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R)
    {z : E ⊗[F] R} (hz : z ∈ tensInt (F := F) R S₁ S₂) :
    z ∈ AddSubgroup.closure {z | ∃ a ∈ S₁, ∃ r ∈ S₂, z = a ⊗ₜ[F] r} := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨r, rfl⟩
    · exact AddSubgroup.subset_closure ⟨a, a.2, 1, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, S₁.one_mem, r, r.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, S₁.one_mem, 1, S₂.one_mem, rfl⟩
  | add x y _ _ h1 h2 => exact add_mem h1 h2
  | neg x _ h1 => exact neg_mem h1
  | mul x y _ _ h1 h2 => exact mul_mem_pureClosure S₁ S₂ h1 h2

end Tens

def trT (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  TensorProduct.lift ((LinearMap.mul F R).comp ((Algebra.linearMap F R).comp (Algebra.trace F E)))

theorem trT_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (a : E) (r : R) :
    trT F E R (a ⊗ₜ r) = algebraMap F R (Algebra.trace F E a) * r := by
  simp [trT]

theorem mem_intOE_of_inclE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsScalarTower ℚ F E] (x : E)
    (hx : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    x ∈ (algebraMap (𝓞 E) E).range := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

  have htrO : ∀ a : E, a ∈ intOE E → Algebra.trace F E a ∈ (algebraMap (𝓞 F) F).range := by
    rintro a ⟨a, rfl⟩
    have : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 this
    exact ⟨y, hy⟩

  have htr : ∀ z ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F),
      trT F E (FiniteAdeleRing (𝓞 F) F) z ∈ intAd F := by
    intro z hz
    have := tensInt_le_pureClosure _ _ hz
    clear hz
    induction this using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, r, hr, rfl⟩ := hy
      rw [trT_tmul]
      refine (intAd F).mul_mem ?_ hr
      obtain ⟨o, ho⟩ := htrO a ha
      rw [← ho]
      intro v
      show ((o : F) : v.adicCompletion F) ∈ _
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact HeightOneSpectrum.valuation_le_one v o
    | zero => rw [map_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [map_neg]; exact neg_mem h1
  have hint : IsIntegral ℤ x := by
    apply isIntegral_of_trace_pow_mul E x
    intro n b
    have hw : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x ^ n * (b : E)) ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
      rw [map_mul, map_pow]
      refine Subring.mul_mem _ (Subring.pow_mem _ hx n) (Subring.subset_closure (Or.inl ⟨⟨(b : E), b, rfl⟩, rfl⟩))
    have h1 := htr _ hw
    have e1 : trT F E (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x ^ n * (b : E))) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (Algebra.trace F E (x ^ n * (b : E))) := by
      show trT F E _ ((x ^ n * (b : E)) ⊗ₜ 1) = _
      rw [trT_tmul, mul_one]
    rw [e1] at h1
    obtain ⟨o, ho⟩ := mem_int_of_adele F _ h1
    rw [← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← ho]
    have : IsIntegral ℤ (Algebra.trace ℚ F (o : F)) := Algebra.isIntegral_trace o.2
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 this
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
