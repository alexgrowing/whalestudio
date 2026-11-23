import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open Limits

namespace GlobalTheory.SameLine

theorem injective_of_mem_range {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B' : Module.Basis (Fin 1) R M) (B : Module.Basis (Fin 1) R N)
    (f : M →ₗ[R] N) {t : M} (ht : f t = B 0) : Function.Injective f := by
  have hsum (P : Type) [AddCommGroup P] [Module R P] (C : Module.Basis (Fin 1) R P) (m : P) :
      m = C.repr m 0 • C 0 := by
    conv_lhs => rw [← C.sum_repr m]
    simp
  set c := B.repr (f (B' 0)) 0
  have hf (m : M) : B.repr (f m) 0 = B'.repr m 0 * c := by
    conv_lhs => rw [hsum M B' m]
    simp [c]
  have hac : B'.repr t 0 * c = 1 := by
    rw [← hf, ht]; simp
  refine (injective_iff_map_eq_zero f).2 fun m hm => ?_
  have h0 : B'.repr m 0 * c = 0 := by rw [← hf, hm]; simp
  have : B'.repr m 0 = 0 := by
    calc B'.repr m 0 = B'.repr m 0 * (B'.repr t 0 * c) := by rw [hac, mul_one]
      _ = B'.repr t 0 * (B'.repr m 0 * c) := by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hsum M B' m, this, zero_smul]

theorem isIso_of_epi {X : Scheme.{0}} {Q' Q : X.Modules} (π : Q' ⟶ Q) [Epi π]
    (hQ' : IsVB Q' 1) (hQ : IsVB Q 1) : IsIso π := by
  have : Mono π := by
    refine GlobalTheory.QCoh.mono_of_locally_app_injective π fun W x hx => ?_
    obtain ⟨U₁, e', -, hx₁, h₁, he'⟩ := hQ'.exists_affine hx
    obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
    obtain ⟨U₃, h₃, hx₃, t, ht⟩ := exists_app_eq_of_epi π (e 0) hx₂
    refine ⟨U₃, hx₃, h₃.trans (h₂.trans h₁), ?_⟩
    have := injective_of_mem_range (he'.basis (h₃.trans h₂)) (he.basis h₃)
      (GlobalTheory.QCoh.appLinear π U₃) (t := t) (by
        rw [GlobalTheory.QCoh.appLinear_apply, ht, IsFrame.basis_apply])
    exact this
  exact isIso_of_mono_of_epi π

end GlobalTheory.SameLine

theorem GlobalTheory.SameLine.eq_line : ∀ (X : Scheme.{0}) (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0), (ShortComplex.mk l m w).ShortExact → (ShortComplex.mk l' m' w').ShortExact → IsVB Q 1 → IsVB Q' 1 → l' ≫ m = 0 → ∃ e : L' ≅ L, e.hom ≫ l = l' := by
  intro X V L Q L' Q' l m w l' m' w' hS hS' hQ hQ' h
  have hmono : Mono l := hS.mono_f
  have hmono' : Mono l' := hS'.mono_f
  have hepi : Epi m := hS.epi_g
  obtain ⟨π, hπ⟩ := CokernelCofork.IsColimit.desc' hS'.gIsCokernel m h
  change Q' ⟶ Q at π
  change m' ≫ π = m at hπ
  have : Epi π := epi_of_epi_fac hπ
  have : IsIso π := GlobalTheory.SameLine.isIso_of_epi π hQ' hQ
  have h₂ : l ≫ m' = 0 := by
    rw [← cancel_mono π, Category.assoc]
    rw [hπ, w, zero_comp]
  obtain ⟨f, hf⟩ := KernelFork.IsLimit.lift' hS.fIsKernel l' h
  obtain ⟨g, hg⟩ := KernelFork.IsLimit.lift' hS'.fIsKernel l h₂
  change L' ⟶ L at f
  change L ⟶ L' at g
  change f ≫ l = l' at hf
  change g ≫ l' = l at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_mono l', Category.assoc, hg, hf, Category.id_comp]
  · rw [← cancel_mono l, Category.assoc, hf, hg, Category.id_comp]
