import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

open Polynomial Module.End

theorem part_projector_mem_adjoin :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
      [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
      [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) →
      (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) →
      (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) →
      ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) →
      ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S,
        (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧
          ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ S hS hsplit hint L _ _ _ 𝔪
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨F, hF, -⟩ := NCov.exists_finset_pts hinj hS hsplit hint
  by_cases hA : ∃ ψ0 : Algebra.adjoin O S →ₐ[O] O, NCov.cls ψ0 = 𝔪
  swap
  · push_neg at hA
    refine ⟨0, Subalgebra.zero_mem _, fun x hx => ?_, fun x _ => rfl⟩
    have : NCov.part (Algebra.adjoin O S) 𝔪 = ⊥ := by
      unfold NCov.part
      exact iSup₂_eq_bot.2 fun ψ h => absurd h (hA ψ)
    rw [this, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨ψ0, rfl⟩ := hA
  have hmax := NCov.cls_isMaximal ψ0
  have hs : ∀ φ : Algebra.adjoin O S →ₐ[O] O, ∃ s : Algebra.adjoin O S,
      (NCov.cls φ ≠ NCov.cls ψ0 → s ∈ NCov.cls φ) ∧ s ∉ NCov.cls ψ0 := by
    intro φ
    by_cases h : NCov.cls φ = NCov.cls ψ0
    · exact ⟨1, fun h' => absurd h h', fun h1 => hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)⟩
    · have : ¬ NCov.cls φ ≤ NCov.cls ψ0 := fun hle =>
        h ((NCov.cls_isMaximal φ).eq_of_le hmax.ne_top hle)
      obtain ⟨s, hs1, hs2⟩ := SetLike.not_le_iff_exists.1 this
      exact ⟨s, fun _ => hs1, hs2⟩
  choose s hsin hsout using hs
  set FA := F.filter (fun ψ => NCov.cls ψ = NCov.cls ψ0)
  set FB := F.filter (fun ψ => NCov.cls ψ ≠ NCov.cls ψ0)
  letI : CommRing (Algebra.adjoin O S) := Algebra.adjoinCommRingOfComm O fun a ha b hb => (hS a ha b hb).eq
  obtain ⟨f, hfdef⟩ : ∃ f : Algebra.adjoin O S, f = ∏ φ ∈ FB, s φ := ⟨_, rfl⟩
  have hres : ∀ ψ : Algebra.adjoin O S →ₐ[O] O, ∀ u, u ∈ NCov.cls ψ ↔ IsLocalRing.residue O (ψ u) = 0 :=
    fun ψ u => Iff.rfl
  have hfA : ∀ ψ, NCov.cls ψ = NCov.cls ψ0 → IsLocalRing.residue O (ψ f) ≠ 0 := by
    intro ψ hψ
    rw [hfdef, map_prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun φ _ => ?_
    have := hsout φ
    rw [← hψ, hres] at this
    exact this
  have hfB : ∀ φ ∈ FB, IsLocalRing.residue O (φ f) = 0 := by
    intro φ hφ
    rw [hfdef, map_prod, map_prod]
    exact Finset.prod_eq_zero hφ ((hres φ _).1 (hsin φ (Finset.mem_filter.1 hφ).2))
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ =>
    (f : End K V).maxGenEigenspaceIndex (NCov.pt ψ f)
  let g : O[X] := ∏ ψ ∈ FA, (X - C (ψ f)) ^ d ψ
  let h : O[X] := ∏ φ ∈ FB, (X - C (φ f)) ^ d φ
  have hcop : IsCoprime g h := by
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => IsCoprime.pow ?_
    refine isCoprime_X_sub_C_of_isUnit_sub ?_
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_sub, hfB φ hφ, sub_zero]
    exact hfA ψ (Finset.mem_filter.1 hψ).2
  obtain ⟨p, q, hpq⟩ := hcop
  have hkill : ∀ (G : Finset (Algebra.adjoin O S →ₐ[O] O)) (ψ) (_ : ψ ∈ G) (x : V),
      x ∈ NCov.W _ (NCov.pt ψ) → aeval (f : End K V) (∏ φ ∈ G, (X - C (φ f)) ^ d φ) x = 0 := by
    intro G ψ hψ x hx
    rw [show (∏ φ ∈ G, (X - C (φ f)) ^ d φ) =
        (∏ φ ∈ G.erase ψ, (X - C (φ f)) ^ d φ) * (X - C (ψ f)) ^ d ψ from
      (Finset.prod_erase_mul _ _ hψ).symm]
    rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
    rw [NCov.pow_sub_apply_eq_zero ψ f hx, map_zero]
  have hval : ((aeval f (q * h) : Algebra.adjoin O S) : End K V) = aeval (f : End K V) (q * h) := by
    have e := aeval_algHom_apply (Algebra.adjoin O S).val f (q * h)
    simpa using e.symm
  refine ⟨_, (aeval f (q * h)).2, ?_, ?_⟩
  · intro x hx
    rw [hval]
    have hle : NCov.part (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h) - 1) := by
      unfold NCov.part
      refine iSup₂_le fun ψ hψ => ?_
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hW : NCov.W _ (NCov.pt ψ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hψA : ψ ∈ FA := Finset.mem_filter.2 ⟨hF ψ hW, hψ⟩
      have e1 := congrArg (fun P => aeval (f : End K V) P y) hpq
      simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
        Module.End.one_apply] at e1
      rw [hkill FA ψ hψA y hy, map_zero, zero_add] at e1
      simpa [map_mul, Module.End.mul_apply] using e1
    have := hle hx
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  · intro x hx
    rw [hval]
    have hle : NCov.off (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h)) := by
      unfold NCov.off
      refine iSup₂_le fun φ hφ => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      by_cases hW : NCov.W _ (NCov.pt φ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hφB : φ ∈ FB := Finset.mem_filter.2 ⟨hF φ hW, hφ⟩
      rw [map_mul, Module.End.mul_apply, hkill FB φ hφB y hy, map_zero]
    exact hle hx

end GlobalTheory
