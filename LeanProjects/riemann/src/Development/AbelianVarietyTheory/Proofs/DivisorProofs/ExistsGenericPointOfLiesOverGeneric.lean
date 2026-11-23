import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum

theorem eq_gp_of_lies_over_bot {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} [IsReduced S] (π : S ⟶ Sp R)
    (gp : Sp (FractionRing R) ⟶ S) (hgp : gp ≫ π = jK R) (hd : IsDominant gp)
    {B : CommRingCat} (e₀ : Spec B ⟶ S) [he₀ : IsOpenImmersion e₀] (P : Spec B)
    (hP : π (e₀ P) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) (k : Sp (FractionRing R)) : e₀ P = gp k := by
  have hsub : Set.range gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  set g' := IsOpenImmersion.lift e₀ gp hsub with hg'
  have hfac : g' ≫ e₀ = gp := IsOpenImmersion.lift_fac _ _ _
  set g := Spec.preimage g' with hg
  set ρ := Spec.preimage (e₀ ≫ π) with hρ
  have hgg : Spec.map g = g' := Spec.map_preimage _
  have hρρ : Spec.map ρ = e₀ ≫ π := Spec.map_preimage _
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgg, hρρ, ← Category.assoc, hfac, hgp]
  have hcomp' : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => by
    have := congrArg (fun f => f.hom r) hcomp
    simpa using this
  have hden : DenseRange g' := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ g') = gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hred : _root_.IsReduced B := by
    have : IsReduced (Spec B) := isReduced_of_isOpenImmersion e₀
    exact (affine_isReduced_iff B).1 this
  have hinj : Function.Injective g.hom := by
    have h1 : DenseRange (PrimeSpectrum.comap g.hom) := by rw [← hgg] at hden; exact hden
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 h1
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have hPρ : Ideal.comap ρ.hom P.asIdeal = ⊥ := by
    have h2 : (Spec.map ρ) P = π (e₀ P) := by rw [hρρ]; rfl
    rw [hP] at h2
    exact congrArg PrimeSpectrum.asIdeal h2
  have hPb : P.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom x)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * x - ρ.hom a = 0 := by
      apply hinj
      rw [map_sub, map_mul, hcomp', hcomp', ← hxs, map_zero, mul_div_cancel₀ _ hs0, sub_self]
    have ha : a ∈ Ideal.comap ρ.hom P.asIdeal := by
      rw [Ideal.mem_comap, ← sub_eq_zero.1 h0]
      exact P.asIdeal.mul_mem_left _ hx
    rw [hPρ, Ideal.mem_bot] at ha
    have hx0 : g.hom x = 0 := by rw [← hxs, ha, map_zero, zero_div]
    rw [Ideal.mem_bot]
    exact hinj (by rw [hx0, map_zero])
  rw [← hfac]
  show e₀ P = e₀ (g' k)
  congr 1
  rw [← hgg]
  apply PrimeSpectrum.ext
  show P.asIdeal = Ideal.comap g.hom k.asIdeal
  have hk : k.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ k.isPrime
  rw [hPb, hk, Ideal.comap_bot_of_injective _ hinj]

theorem modif_pt_over_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  intro R _ _ M' W _ _ φ ξ hφ hξ
  have : IsReduced M'.S := by have := M'.integral; infer_instance
  let w : Sp W := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)
  let k : Sp (FractionRing R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  refine ⟨w, k, ?_⟩
  let j := M'.S.affineCover.idx (ξ w)
  have hoi : IsOpenImmersion (M'.S.affineCover.f j) := M'.S.affineCover.map_prop j
  obtain ⟨P, hP⟩ := M'.S.affineCover.covers (ξ w)
  rw [← hP]
  refine eq_gp_of_lies_over_bot (he₀ := hoi) M'.π M'.gp M'.gp_π M'.dominant (M'.S.affineCover.f j) P ?_ k
  refine (congrArg M'.π hP).trans ?_
  have h1 : M'.π (ξ w) = (spMap φ) w := by rw [← hξ]; rfl
  rw [h1]
  apply PrimeSpectrum.ext
  show Ideal.comap φ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hφ

end GlobalTheory.Mum
