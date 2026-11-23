import Mathlib

open scoped InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Type*}

theorem orth_stable (ρ : Γ → H →ₗ[ℂ] H) (hρ : ∀ g, ∃ g', ∀ x y, ⟪x, ρ g y⟫_ℂ = ⟪ρ g' x, y⟫_ℂ)
    {S : Submodule ℂ H} (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : ∀ g, ∀ x ∈ Sᗮ, ρ g x ∈ Sᗮ := by
  intro g x hx
  obtain ⟨g', h⟩ := hρ g
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [h]
  exact hx _ (hS g' u hu)

theorem mem_of_mem_closure_of_finite (ρ : Γ → H →ₗ[ℂ] H) (hρ : ∀ g, ∃ g', ∀ x y, ⟪x, ρ g y⟫_ℂ = ⟪ρ g' x, y⟫_ℂ)
    (W F E₀ : Submodule ℂ H) [FiniteDimensional ℂ E₀] (hF : ∀ g, ∀ x ∈ F, ρ g x ∈ F)
    (hW : ∀ w ∈ W, ∃ S ≤ W, FiniteDimensional ℂ S ∧ w ∈ S ∧ ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hE : ∀ S ≤ W, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S ⊓ Fᗮ = ⊥ → S ≤ E₀)
    {v : H} (hvF : v ∈ F) (hv : v ∈ W.topologicalClosure) : v ∈ W := by
  set E : Submodule ℂ H := sSup {S | S ≤ W ∧ S ≤ E₀ ∧ ∀ g, ∀ x ∈ S, ρ g x ∈ S} with hEdef
  have hEW : E ≤ W := sSup_le fun S hS => hS.1
  have hE0 : E ≤ E₀ := sSup_le fun S hS => hS.2.1
  have hEfd : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hE0
  have hEs : ∀ g, ∀ x ∈ E, ρ g x ∈ E := fun g => by
    have : E ≤ E.comap (ρ g) := sSup_le fun S hS x hx => (le_sSup hS : S ≤ E) (hS.2.2 g x hx)
    exact this
  set v' := v - E.starProjection v with hv'
  have hv'E : v' ∈ Eᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have key : ∀ w ∈ W, ⟪w, v'⟫_ℂ = 0 := by
    intro w hw
    obtain ⟨S, hSW, hSfd, hwS, hS⟩ := hW w hw
    set S₂ : Submodule ℂ H := (S ⊔ E) ⊓ Eᗮ with hS₂
    have hS₂fd : FiniteDimensional ℂ S₂ := Submodule.finiteDimensional_of_le inf_le_left
    have hSE : ∀ g, ∀ x ∈ S ⊔ E, ρ g x ∈ S ⊔ E := fun g => by
      have : S ⊔ E ≤ (S ⊔ E).comap (ρ g) :=
        sup_le (fun x hx => Submodule.mem_sup_left (hS g x hx)) (fun x hx => Submodule.mem_sup_right (hEs g x hx))
      exact this
    have hS₂s : ∀ g, ∀ x ∈ S₂, ρ g x ∈ S₂ := fun g x hx => ⟨hSE g x hx.1, orth_stable ρ hρ hEs g x hx.2⟩
    set A : Submodule ℂ H := S₂ ⊓ Fᗮ with hA
    have hAfd : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le inf_le_left
    have hAs : ∀ g, ∀ x ∈ A, ρ g x ∈ A := fun g x hx => ⟨hS₂s g x hx.1, orth_stable ρ hρ hF g x hx.2⟩
    set B : Submodule ℂ H := S₂ ⊓ Aᗮ with hB
    have hBs : ∀ g, ∀ x ∈ B, ρ g x ∈ B := fun g x hx => ⟨hS₂s g x hx.1, orth_stable ρ hρ hAs g x hx.2⟩
    have hBW : B ≤ W := inf_le_left.trans (inf_le_left.trans (sup_le hSW hEW))
    have hBE : B ≤ E := by
      refine le_sSup ⟨hBW, hE B hBW hBs ?_, hBs⟩
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ A := ⟨hx.1.1, hx.2⟩
      exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 hx.1.2)
    have hS₂F : ∀ x ∈ S₂, x ∈ Fᗮ := by
      intro x hx
      have hPA : A.starProjection x ∈ A := Submodule.starProjection_apply_mem A x
      have h1 : x - A.starProjection x ∈ B :=
        ⟨S₂.sub_mem hx hPA.1, Submodule.sub_starProjection_mem_orthogonal x⟩
      have h2 : x - A.starProjection x = 0 :=
        inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal (hBE h1) h1.1.2)
      rw [sub_eq_zero.1 h2]
      exact hPA.2
    have hPE : E.starProjection w ∈ E := Submodule.starProjection_apply_mem E w
    have h3 : w - E.starProjection w ∈ S₂ :=
      ⟨Submodule.sub_mem _ (Submodule.mem_sup_left hwS) (Submodule.mem_sup_right hPE),
        Submodule.sub_starProjection_mem_orthogonal w⟩
    have h4 : ⟪w - E.starProjection w, v'⟫_ℂ = 0 := by
      rw [hv', inner_sub_right, Submodule.inner_left_of_mem_orthogonal hvF (hS₂F _ h3),
        Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem E v) h3.2, sub_zero]
    have h5 : ⟪E.starProjection w, v'⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hPE hv'E
    rw [inner_sub_left, h5, sub_zero] at h4
    exact h4
  have hPv : E.starProjection v ∈ W := hEW (Submodule.starProjection_apply_mem E v)
  have hcl : v' ∈ W.topologicalClosure := Submodule.sub_mem _ hv (W.le_topologicalClosure hPv)
  have h0 : ⟪v', v'⟫_ℂ = 0 := by
    have hc : IsClosed {x : H | ⟪x, v'⟫_ℂ = 0} := isClosed_eq (by fun_prop) continuous_const
    exact closure_minimal (s := (W : Set H)) key hc hcl
  have : v = E.starProjection v := sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  rw [this]
  exact hPv

theorem exists_monic_aeval_mem {V : Type*} [AddCommGroup V] [Module ℂ V] (C : Module.End ℂ V) (N : Submodule ℂ V)
    [FiniteDimensional ℂ (V ⧸ N)] (hN : ∀ x ∈ N, C x ∈ N) :
    ∃ q : Polynomial ℂ, q.Monic ∧ 0 < q.natDegree ∧ ∀ x, Polynomial.aeval C q x ∈ N := by
  set D : Module.End ℂ (V ⧸ N) := N.mapQ N C hN with hD
  have hint : ∀ (p : Polynomial ℂ) x, N.mkQ (Polynomial.aeval C p x) = Polynomial.aeval D p (N.mkQ x) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro x; simp
    | add p q hp hq => intro x; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a h =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval D), Polynomial.aeval_X, Polynomial.aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, h]
      rfl
  refine ⟨Polynomial.X * D.charpoly, Polynomial.monic_X.mul D.charpoly_monic, ?_, fun x => ?_⟩
  · rw [Polynomial.monic_X.natDegree_mul D.charpoly_monic, Polynomial.natDegree_X]
    omega
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hint, map_mul, LinearMap.aeval_self_charpoly, mul_zero]
    rfl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
