import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
open TopologicalSpace

namespace GlobalTheory.VB

theorem injective_of_basis_mem_range {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type} [Fintype ι] (B' : Module.Basis ι R M)
    (B : Module.Basis ι R N) (f : M →ₗ[R] N) (hB : ∀ i, B i ∈ LinearMap.range f) :
    Function.Injective f := by
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← B.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hB i
  have : Module.Finite R M := Module.Finite.of_basis B'
  let g : N ≃ₗ[R] M := B.equiv B' (Equiv.refl ι)
  have hinj : Function.Injective (g.toLinearMap ∘ₗ f) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (g.surjective.comp hsurj)
  exact fun a b hab => hinj (by simp [hab])

variable {X : Scheme.{0}} {F G : X.Modules} {V : X.Opens}

theorem exists_app_eq_of_epi_fintype {ι : Type} [Fintype ι] (φ : F ⟶ G) [Epi φ]
    (s : ι → Γ(G, V)) {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (h : W ≤ V), x ∈ W ∧
      ∃ t : ι → Γ(F, W), ∀ i, φ.app W (t i) = Twist.resM G h (s i) := by
  choose W hW hxW t ht using fun i => exists_app_eq_of_epi φ (s i) hx
  let W' : X.Opens := V ⊓ Finset.univ.inf W
  have hxW' : x ∈ W' := ⟨hx, by rw [Opens.coe_finset_inf]; simpa using hxW⟩
  have hle (i : ι) : W' ≤ W i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  refine ⟨W', inf_le_left, hxW', fun i => Twist.resM F (hle i) (t i), fun i => ?_⟩
  rw [Twist.app_resM, ht, Twist.resM_resM]

theorem isIso_of_epi_of_isVB : ∀ {X : Scheme.{0}} {E E' : X.Modules} (π : E ⟶ E') [Epi π] (r : ℕ),
    GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → IsIso π := by
  intro X E E' π _ r hE hE'
  have : Mono π := by
    refine GlobalTheory.QCoh.mono_of_locally_app_injective π fun W x hx => ?_
    obtain ⟨U₁, e', -, hx₁, h₁, he'⟩ := hE.exists_affine hx
    obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hE'.exists_affine hx₁
    obtain ⟨U₃, h₃, hx₃, t, ht⟩ := exists_app_eq_of_epi_fintype π e hx₂
    refine ⟨U₃, hx₃, h₃.trans (h₂.trans h₁), ?_⟩
    exact injective_of_basis_mem_range (he'.basis (h₃.trans h₂)) (he.basis h₃)
      (GlobalTheory.QCoh.appLinear π U₃) fun i => ⟨t i, by
        rw [GlobalTheory.QCoh.appLinear_apply, ht, IsFrame.basis_apply]⟩
  exact isIso_of_mono_of_epi π

end GlobalTheory.VB
