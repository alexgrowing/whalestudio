import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem exists_character_of_smul_ne_zero :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W]
      [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 →
      ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  intro R _ _ _ W _ _ _ _ t ht
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R W t)
  have hmemJ : ∀ x : R, x ∈ J ↔ x • t = 0 := fun x => by
    simp [J, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ J := h ▸ Submodule.mem_top
    exact ht (by simpa using (hmemJ 1).1 h1)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℂ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)
  haveI : Module.Finite ℂ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ m)
  have bij : Function.Bijective (algebraMap ℂ (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m)) bij
  refine ⟨(e.symm : (R ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m), fun r c h => ?_⟩
  have hmem : r - algebraMap ℂ R c ∈ J := by
    rw [hmemJ, sub_smul, algebraMap_smul, h, sub_self]
  have hq : Ideal.Quotient.mkₐ ℂ m r = algebraMap ℂ (R ⧸ m) c := by
    have h0 : Ideal.Quotient.mk m (r - algebraMap ℂ R c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hJm hmem)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have he : e c = algebraMap ℂ (R ⧸ m) c := rfl
  show e.symm (Ideal.Quotient.mkₐ ℂ m r) = c
  rw [hq, ← he, AlgEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.RgCOBlock
