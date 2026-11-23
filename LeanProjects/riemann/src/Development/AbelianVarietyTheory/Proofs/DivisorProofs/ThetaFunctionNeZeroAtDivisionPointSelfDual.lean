import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZeroStatement

open Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem eq_zero_of_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {z : Fin g → ℂ}
    (hz : ∀ m ∈ S, (z ⬝ᵥ Hm.mulVec (star m)).im = 0) : z = 0 := by
  have h : ∀ m, (z ⬝ᵥ Hm.mulVec (star m)).im = 0 := by
    intro m
    have hm : m ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hz m hm
    | zero => simp
    | add a b _ _ ha hb => rw [star_add, mulVec_add, dotProduct_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [star_smul, mulVec_smul, dotProduct_smul, smul_im, ha, smul_zero]
  by_contra hne
  have h1 := hpos z hne
  have h2 := h (I • z)
  rw [star_smul, mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem exists_ne_zero_of_principal {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hχ : ∀ l, ‖χ l‖ = 1)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) (n : ℕ) (hn : 2 ≤ n) (f : (Fin g → ℂ) → ℂ)
    (hdf : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ (l : Λ) z, f (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f z) :
    ∃ l ∈ Λ, f ((n : ℂ)⁻¹ • l) ≠ 0 := by
  obtain ⟨φ, τ, Q, b, hτ, hτp, hΛ, hQ, -, hb, h1, h2⟩ :=
    GlobalTheory.SiegelNormalForm.exists_normal_form g Λ hd hs Hm χ Ef hH hpos hχ hE hbij
  have hφ : Differentiable ℂ (fun z => φ z) :=
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
  have key := GlobalTheory.T.exists_theta_division_point_ne_zero g n τ (fun j => b j ^ n) (fun z => f (φ z) * cexp (-(n * Q z))) hτ hτp hn
    (fun j => pow_ne_zero _ (hb j)) ((hdf.comp hφ).mul ((hQ.const_mul (n : ℂ)).neg.cexp)) ?_ ?_ ?_
  · obtain ⟨m, k, h⟩ := key
    refine ⟨φ _, (hΛ _).2 ⟨m, k, rfl⟩, ?_⟩
    rw [← map_smul]
    exact left_ne_zero_of_mul h
  · intro h
    apply h0
    ext w
    have h := congrFun h (φ.symm w)
    simp only [Pi.zero_apply, LinearEquiv.apply_symm_apply] at h ⊢
    exact (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
  · intro i z
    have hm : φ (Pi.single i 1) ∈ Λ := by
      refine (hΛ _).2 ⟨Pi.single i 1, 0, ?_⟩
      ext a
      by_cases h : a = i
      · subst h; simp [Matrix.mulVec, dotProduct]
      · simp [h, Matrix.mulVec, dotProduct]
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h1 i ⟨_, hm⟩ z rfl] at e
    simp only [map_add]
    rw [e, ← Complex.exp_nat_mul, mul_right_comm, ← Complex.exp_add, mul_comm]
    congr 2
    ring
  · intro j z
    have hm : φ (τ.mulVec (Pi.single j 1)) ∈ Λ := by
      refine (hΛ _).2 ⟨0, Pi.single j 1, ?_⟩
      have : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
        ext a
        by_cases h : a = j
        · subst h; simp
        · simp [h]
      rw [this]
      ext a
      simp
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h2 j ⟨_, hm⟩ z rfl] at e
    simp only [map_add]
    rw [e, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have : cexp (n * (Q (z + τ.mulVec (Pi.single j 1)) - Q z)) *
        cexp (-(n * Q (z + τ.mulVec (Pi.single j 1)))) = cexp (-(n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this, show (n : ℂ) * (-(2 * Real.pi * I) * z j) = -(2 * Real.pi * I) * n * z j by ring]
    ring

theorem exists_ne_zero_of_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  intro V _ _ _ g B p hp L hfg hL hsp Hm hH hpos hB c hc N hN f hdf h0 hf
  set Λ : Submodule ℤ (Fin g → ℂ) := L.map p with hΛ
  have hsp' : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := hsp
  choose q hq hpq using fun l : Λ => l.2
  have hint : ∀ l m : Λ, ∃ k : ℤ,
      (k : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := fun l m => by
    obtain ⟨k, hk⟩ := (hL _).1 (hq l) _ (hq m)
    exact ⟨k, by rw [← hpq l, ← hpq m, hB, hk, Rat.cast_intCast]⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, add_dotProduct, add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, smul_dotProduct]; simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, mulVec_add, dotProduct_add,
        add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, mulVec_smul,
        dotProduct_smul]; simp))
  have hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := hk
  have hker : ∀ l : Λ, Ef l = 0 → l = 0 := fun l hl =>
    Subtype.ext (eq_zero_of_im_eq_zero hpos hsp' fun m hm => by
      rw [← hE l ⟨m, hm⟩, hl]; simp)
  have hdisc : DiscreteTopology Λ := by
    haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 (hfg.map p)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := Λ)
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have e : ({0} : Set Λ) = ⋂ m ∈ s, {l : Λ |
        |((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im| < 1} := by
      ext l
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h m _ => by simp [h], fun h => hker l (LinearMap.ext_on hs fun m hm => ?_)⟩
      have h1 := h m hm
      rw [← hE, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
      exact Int.abs_lt_one_iff.1 h1
    rw [e]
    refine isOpen_biInter_finset fun m _ => isOpen_lt ?_ continuous_const
    refine (Complex.continuous_im.comp ?_).abs
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => hp ?_
    rw [map_zero]
    refine eq_zero_of_im_eq_zero hpos hsp ?_
    rintro _ ⟨v, -, rfl⟩
    rw [hB, hu]; simp
  have hBsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℚ) (V := V)).symm).1 hBinj
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 hker, fun φ => ?_⟩
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible ℚ).extension_property L.subtype
      L.subtype_injective ((Algebra.linearMap ℤ ℚ) ∘ₗ φ ∘ₗ p.submoduleMap L)
    obtain ⟨x, hx⟩ := hBsurj ψ.toAddMonoidHom.toRatLinearMap
    have h1 : ∀ (y) (hy : y ∈ L), B x y = (φ ⟨p y, Submodule.mem_map_of_mem hy⟩ : ℤ) :=
      fun y hy => by
        rw [hx]
        exact LinearMap.congr_fun hψ ⟨y, hy⟩
    refine ⟨⟨p x, Submodule.mem_map_of_mem ((hL x).2 fun y hy => ⟨_, h1 y hy⟩)⟩,
      LinearMap.ext ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    refine Int.cast_injective (α := ℝ) ?_
    rw [hE, hB, h1 y hy, Rat.cast_intCast]
  have hN0 : N ≠ 0 := by omega
  choose χ hχ using fun l : Λ => IsAlgClosed.exists_pow_nat_eq (c (q l)) (Nat.pos_of_ne_zero hN0)
  have hχ1 : ∀ l, ‖χ l‖ = 1 := fun l =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 (by rw [← norm_pow, hχ, hc])
  obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := exists_ne_zero_of_principal Λ hdisc hsp' Hm χ Ef hH hpos hχ1 hE
    hbij N hN f hdf h0 (fun l z => by
      rw [mul_pow, hχ, ← Complex.exp_nat_mul, ← hpq l]
      exact hf _ (hq l) z)
  exact ⟨v, hv, h⟩

end GlobalTheory.ThetaDivisionPoints
