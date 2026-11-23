import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat

open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

theorem star_compat {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {F : Type} [AddCommGroup F] [Module K F]
    {FC : Type} [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] (jR : F →ₛₗ[σ] FC) (h : F →ₗ⋆[K] F →ₗ[K] K)
    (hiso : ∀ x y, ⟪jR x, jR y⟫_ℂ = σ (h x y)) (x : F) (hx : jR x ≠ 0) (a : K) :
    σ (star a) = starRingEnd ℂ (σ a) := by
  have h1 := hiso (a • x) x
  have h2 := hiso x x
  rw [LinearMap.map_smulₛₗ, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul,
    ← h2] at h1
  have hne : ⟪jR x, jR x⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  have h3 := mul_right_cancel₀ hne h1
  rw [h3]
  rfl

theorem range_adjoint_rat {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {F : Type} [AddCommGroup F] [Module K F]
    {FC : Type} [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (jR : F →ₛₗ[σ] FC) (h : F →ₗ⋆[K] F →ₗ[K] K) {ι : Type} (bb : Basis ι K F)
    (hli : LinearIndependent ℂ fun k => jR (bb k)) (hsp : Submodule.span ℂ (Set.range fun k => jR (bb k)) = ⊤)
    (hiso : ∀ x y, ⟪jR x, jR y⟫_ℂ = σ (h x y)) (Θ : FC →ₗ[ℂ] E) {N : ℕ} (ψ : Fin N → Module.Dual ℂ E)
    (hψ : ∀ e, (∀ i, ψ i e = 0) → e = 0) (hr : ∀ i x, ψ i (Θ (jR x)) ∈ Set.range σ) :
    Submodule.span ℂ (jR '' ((LinearMap.range (LinearMap.adjoint Θ)).comap jR : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ) := by
  classical
  have : Finite ι := hli.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx

  set e : Fin N → E := fun i => (InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap (ψ i)) with he
  have hei : ∀ i u, ⟪e i, u⟫_ℂ = ψ i u := by
    intro i u
    simp [he, InnerProductSpace.toDual_symm_apply]
  have hspan : Submodule.span ℂ (Set.range e) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro u hu
    apply hψ
    intro i
    rw [← hei]
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal' _ _).mp hu _ (Submodule.subset_span ⟨i, rfl⟩))

  have hrat : ∀ i, LinearMap.adjoint Θ (e i) ∈
      Submodule.span ℂ (jR '' ((LinearMap.range (LinearMap.adjoint Θ)).comap jR : Set F)) := by
    intro i
    set f : (ι → ℂ) →ₗ[ℂ] FC := Fintype.linearCombination ℂ fun k => jR (bb k) with hf
    have hfinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [hf, Fintype.linearCombination_apply] at hx
      funext k
      exact Fintype.linearIndependent_iff.mp hli x hx k
    have hfr : LinearMap.range f = ⊤ := by rw [hf, Fintype.range_linearCombination, hsp]
    obtain ⟨c, hc⟩ : LinearMap.adjoint Θ (e i) ∈ LinearMap.range f := by rw [hfr]; trivial
    set φ : ι → Module.Dual ℂ FC := fun l => innerₛₗ ℂ (jR (bb l)) with hφ
    have hφinj : ∀ u, (∀ l, φ l u = 0) → u = 0 := by
      intro u hu
      have : u ∈ (Submodule.span ℂ (Set.range fun k => jR (bb k)))ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro v hv
        refine inner_eq_zero_symm.mp (Submodule.span_induction (p := fun v _ => ⟪v, u⟫_ℂ = 0) ?_ ?_ ?_ ?_ hv)
        · rintro _ ⟨l, rfl⟩; exact hu l
        · simp
        · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
        · intro a x _ hx; rw [inner_smul_left, hx, mul_zero]
      rw [hsp, Submodule.top_orthogonal_eq_bot] at this
      exact this
    have hfe : ∀ k, f (Pi.single k 1) = jR (bb k) := by
      intro k; simp [hf, Fintype.linearCombination_apply_single]
    have hcoord := coord_rat σ φ hφinj f hfinj
      (fun l k => by rw [hfe]; exact ⟨h (bb l) (bb k), (hiso _ _).symm⟩) c
      (fun l => by
        rw [hc]
        change ⟪jR (bb l), LinearMap.adjoint Θ (e i)⟫_ℂ ∈ Set.range σ
        rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, hei]
        obtain ⟨a, ha⟩ := hr i (bb l)
        exact ⟨star a, by rw [← ha, star_compat σ jR h hiso (bb l) (hli.ne_zero l)]⟩)
    choose a ha using hcoord
    have hr' : jR (∑ k, a k • bb k) = LinearMap.adjoint Θ (e i) := by
      rw [← hc, hf, Fintype.linearCombination_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, ha]
    rw [← hr']
    exact Submodule.subset_span ⟨_, ⟨e i, hr'.symm⟩, rfl⟩
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span ℂ (Set.range e) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun v _ => LinearMap.adjoint Θ v ∈
      Submodule.span ℂ (jR '' ((LinearMap.range (LinearMap.adjoint Θ)).comap jR : Set F))) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨i, rfl⟩; exact hrat i
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem ratZOfTests : RatZOfTests := by
  intro K _ _ _ Bs A X cv hKR hKL hJR hJL hRT hLT
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · obtain ⟨N, ψ, hψ, hr⟩ := hRT
    exact range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  · obtain ⟨N, ψ, hψ, hr⟩ := hLT j
    exact range_adjoint_rat Bs.v0.embedding (X.jL j t) (cv.hL j t) (bL j t) (hKL j t).1 (hKL j t).2 (hJL j t)
      (X.θ' j t) ψ hψ (fun i x => hr t i x)

end Formalism.IndefR.Rat
