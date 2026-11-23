import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace PositivityTheory.Affgl.TopEig
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Jc (c : (E →+* ℂ) → ℂ → ℂ) : Set (Module.End ℂ (Sm E a)) :=
  {z | ∃ τ u, z = cap τ u - c τ u • (1 : Module.End ℂ (Sm E a))}

theorem cap_mem (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩

theorem abs_cofin {A : Type} [Ring A] [Algebra ℂ A] (G J : Set A)
    (h : ∀ g ∈ G, ∃ r : ℂ, g - r • (1 : A) ∈ J) :
    ∀ z ∈ Algebra.adjoin ℂ G, z ∈ Submodule.span ℂ {(1 : A)} ⊔
      Submodule.span ℂ {y | ∃ x ∈ Algebra.adjoin ℂ G, ∃ j ∈ J, y = x * j} := by
  generalize hS : Submodule.span ℂ {y | ∃ x ∈ Algebra.adjoin ℂ G, ∃ j ∈ J, y = x * j} = S
  have hmul : ∀ x ∈ Algebra.adjoin ℂ G, ∀ s ∈ S, x * s ∈ S := by
    subst hS
    intro x hx s hs
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', j, hj, rfl⟩ := hy
      exact Submodule.subset_span ⟨x * x', mul_mem hx hx', j, hj, (mul_assoc _ _ _).symm⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := h x hx
    have e : x = r • (1 : A) + 1 * (x - r • 1) := by rw [one_mul]; abel
    rw [e]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      (hS ▸ Submodule.subset_span ⟨1, one_mem _, _, hr, rfl⟩)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y hx0 _ hx hy =>
    obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mul_add, mul_smul_comm, mul_one]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (hmul x hx0 s hs))

theorem cofin_Jc (c : (E →+* ℂ) → ℂ → ℂ) : Cofin (Jc (a := a) c) := by
  refine ⟨?_, Submodule.span ℂ {1}, FiniteDimensional.span_singleton ℂ _, ?_⟩
  · rintro _ ⟨τ, u, rfl⟩
    exact (Zalg E a).sub_mem (cap_mem τ u) ((Zalg E a).smul_mem (Zalg E a).one_mem _)
  · refine abs_cofin {z | ∃ τ u, z = cap (a := a) τ u} (Jc c) ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨c τ u, τ, u, rfl⟩

theorem forms_subset (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (c : (E →+* ℂ) → ℂ → ℂ) :
    GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ genSpace L ρ (Jc c) := by
  rintro φ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rintro _ ⟨τ, u, rfl⟩
  rw [LinearMap.sub_apply, h4, LinearMap.smul_apply, Module.End.one_apply, sub_self]

theorem top : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GenFin E a) → GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  intro h E _ _ _ a L hL W _ _ _ ρ hρ c
  have := h E a L hL W ρ hρ (Jc c) (cofin_Jc c)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono (forms_subset L ρ c))

end PositivityTheory.Affgl.TopEig
