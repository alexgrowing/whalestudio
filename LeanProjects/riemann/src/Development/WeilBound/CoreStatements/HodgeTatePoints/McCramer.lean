import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem cramer_sub : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (c₀ : Fin r → κ), b.det (z ∘ c₀) ≠ 0 → (∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A) → LinearIndependent Ω (z ∘ c₀) ∧ Submodule.span A (Set.range z) = Submodule.span A (Set.range (z ∘ c₀)) := by
  intro Ω _ E _ _ A r b κ z c₀ h0 h
  classical
  obtain ⟨li, sp⟩ := (Module.Basis.is_basis_iff_det b).2 (isUnit_iff_ne_zero.2 h0)
  refine ⟨li, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨k, rfl⟩
    let B := Module.Basis.mk li sp.ge
    have hc : ∀ l, B.repr (z k) l ∈ A := by
      intro l
      have e := LinearMap.congr_fun (b.det_smul_mk_coord_eq_det_update li sp.ge l) (z k)
      have e2 : b.det (z ∘ c₀) * B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) := by
        rw [Function.comp_update]
        exact e
      have e3 : B.repr (z k) l = b.det (z ∘ Function.update c₀ l k) / b.det (z ∘ c₀) := by
        rw [← e2, mul_div_cancel_left₀ _ h0]
      rw [e3]
      exact h _
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨_, hc l⟩, ?_⟩
    have := B.sum_repr (z k)
    simp only [B, Module.Basis.mk_apply] at this
    exact this
  · rintro _ ⟨i, rfl⟩
    exact ⟨c₀ i, rfl⟩

section
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (A : Subring Ω) {r : ℕ}

theorem repr_mem {ι : Type} (B : Module.Basis ι Ω E) {v : E} (hv : v ∈ Submodule.span A (Set.range B)) (j : ι) :
    B.repr v j ∈ A := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [B.repr_self, Finsupp.single_apply]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  | zero => simp
  | add x y _ _ hx hy => simpa using A.add_mem hx hy
  | smul a x _ hx =>
    have : B.repr (a • x) j = (a : Ω) * B.repr x j := by
      show B.repr ((a : Ω) • x) j = _
      simp
    rw [this]
    exact A.mul_mem a.2 hx

theorem det_mem (B : Module.Basis (Fin r) Ω E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range B)) : B.det v ∈ A := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine A.sum_mem fun s _ => A.mul_mem (intCast_mem _ _) (A.prod_mem fun i _ => ?_)
  exact repr_mem A B (hv _) _

theorem det_mem_span (B : Module.Basis (Fin r) Ω E) {κ : Type} (z : κ → E) (v : Fin r → E)
    (hv : ∀ i, v i ∈ Submodule.span A (Set.range z)) :
    B.det v ∈ Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) := by
  classical
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv i)
  have e : v = fun i => ∑ k ∈ (c i).support, ((c i k : A) : Ω) • z k := funext fun i => (hc i).symm
  have e2 := B.det.toMultilinearMap.map_sum_finset (fun i k => ((c i k : A) : Ω) • z k) fun i => (c i).support
  rw [e]
  refine (show B.det _ = _ from e2) ▸ Submodule.sum_mem _ fun s _ => ?_
  rw [MultilinearMap.map_smul_univ]
  have : (∏ i, ((c i (s i) : A) : Ω)) = ((∏ i, c i (s i) : A) : Ω) := by simp
  rw [this]
  exact Submodule.smul_mem _ (∏ i, c i (s i)) (Submodule.subset_span ⟨s, rfl⟩)

end

theorem frame_plucker : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (A : Subring Ω) [IsLocalRing A] (r : ℕ) (b : Module.Basis (Fin r) Ω E) (κ : Type) (z : κ → E) (f : Fin r → E), LinearIndependent Ω f → Submodule.span A (Set.range z) = Submodule.span A (Set.range f) → ∃ c₀ : Fin r → κ, b.det (z ∘ c₀) ≠ 0 ∧ ∀ c : Fin r → κ, b.det (z ∘ c) / b.det (z ∘ c₀) ∈ A := by
  intro Ω _ E _ _ A _ r b κ z f li h
  classical
  haveI := Module.Finite.of_basis b
  have sp : Submodule.span Ω (Set.range f) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_eq_card_basis b])
  let B := Module.Basis.mk li sp.ge
  have hB : (B : Fin r → E) = f := Module.Basis.coe_mk _ _
  have hd : b.det f ≠ 0 := ((Module.Basis.is_basis_iff_det b).1 ⟨li, sp⟩).ne_zero
  have hbB : ∀ v, b.det v = b.det f * B.det v := fun v => by
    conv_lhs => rw [b.det.eq_smul_basis_det B, hB]
    rfl
  have hA : ∀ c : Fin r → κ, B.det (z ∘ c) ∈ A := fun c =>
    det_mem A B _ fun i => by rw [hB, ← h]; exact Submodule.subset_span ⟨c i, rfl⟩
  have h1 := det_mem_span A B z f fun i => by rw [h]; exact Submodule.subset_span ⟨i, rfl⟩
  rw [← hB, B.det_self] at h1
  have : ∃ c₀, IsUnit (⟨_, hA c₀⟩ : A) := by
    by_contra hn
    push Not at hn
    have : Submodule.span A (Set.range fun c : Fin r → κ => B.det (z ∘ c)) ≤
        Submodule.map (Algebra.linearMap A Ω) (IsLocalRing.maximalIdeal A) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, rfl⟩
      exact ⟨⟨_, hA c⟩, hn c, rfl⟩
    obtain ⟨y, hy, e⟩ := this h1
    have : y = 1 := Subtype.ext e
    exact hy (this ▸ isUnit_one)
  obtain ⟨c₀, hu⟩ := this
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : B.det (z ∘ c₀) * (w : Ω) = 1 := congrArg Subtype.val hw
  refine ⟨c₀, by rw [hbB]; exact mul_ne_zero hd (left_ne_zero_of_mul_eq_one hw'), fun c => ?_⟩
  rw [hbB, hbB (z ∘ c₀), mul_div_mul_left _ _ hd, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hw']
  exact A.mul_mem (hA c) w.2

end PositivityTheory.HtPt.Mc
