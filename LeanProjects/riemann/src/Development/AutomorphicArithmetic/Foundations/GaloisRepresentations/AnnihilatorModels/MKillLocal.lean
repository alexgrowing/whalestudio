import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem away_local {B : Type} [CommRing B] (f : B) (p : PrimeSpectrum B)
    (hp : p ∈ PrimeSpectrum.basicOpen f) (hs : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p}) :
    IsLocalRing (Localization.Away f) := by
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hinj := PrimeSpectrum.localization_comap_injective (Localization.Away f) (Submonoid.powers f)
  have key : ∀ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q = p := by
    intro q
    have hq : PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) := by
      rw [← hrange]
      exact ⟨q, rfl⟩
    exact hs hq
  obtain ⟨q, -⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [hrange]
    exact hp
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => ?_⟩
  have h := hinj ((key ⟨N, hN.isPrime⟩).trans (key ⟨M, hM.isPrime⟩).symm)
  exact congrArg PrimeSpectrum.asIdeal h

private theorem exists_eps (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B] [Module.Finite κ B]
    (f : B) (m : Ideal B) [hm : m.IsMaximal] (hf : f ∉ m) :
    Nonempty (Localization.Away f →ₐ[κ] κ) := by
  haveI : Module.Finite κ (B ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic κ (B ⧸ m) := Algebra.IsAlgebraic.of_finite κ (B ⧸ m)
  let φ : B ⧸ m →ₐ[κ] κ := IsAlgClosed.lift
  let ψ : B →ₐ[κ] κ := φ.comp (Ideal.Quotient.mkₐ κ m)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := ψ) ?_⟩
  rintro ⟨y, n, rfl⟩
  simp only [map_pow]
  refine IsUnit.pow _ (isUnit_iff_ne_zero.mpr ?_)
  intro h
  apply hf
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply φ.toRingHom.injective
  rw [map_zero]
  exact h

private theorem local_kill (κ : Type) [Field κ] (A A' : Over (Sp κ)) [GrpObj A] [GrpObj A'] (χ : A ⟶ A') [IsMonHom χ]
    (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) (hsub : IsSub A P)
    (h1 : ∀ g : 𝟙_ (Over (Sp κ)) ⟶ A, P _ g → g ≫ χ = 1)
    (Λ : Type) [CommRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ)
    (h2 : ∀ g : algPt κ Λ ⟶ A, P _ g → Inf ε g → g ≫ χ = 1)
    (g : algPt κ Λ ⟶ A) (hP : ∀ (T : Over (Sp κ)) (y : T ⟶ algPt κ Λ), P T (y ≫ g)) : g ≫ χ = 1 := by
  let s : 𝟙_ (Over (Sp κ)) ⟶ algPt κ Λ := Over.homMk (spMap ε.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    ext x
    simp)
  let π : algPt κ Λ ⟶ 𝟙_ (Over (Sp κ)) := toUnit _
  have hsπ : s ≫ π = 𝟙 _ := toUnit_unique _ _
  let g0 : algPt κ Λ ⟶ A := π ≫ s ≫ g
  have hg : P _ g := by simpa using hP _ (𝟙 _)
  have hg0 : P _ g0 := by simpa [g0] using hP _ (π ≫ s)
  have hsg : P _ (s ≫ g) := hP _ s
  have hh : P _ (g * g0⁻¹) := ((hsub _).2 _ _ hg hg0)
  have hs1 : s ≫ (g * g0⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    simp only [g0, ← Category.assoc, hsπ, Category.id_comp, mul_inv_cancel]
  have hinf : Inf ε (g * g0⁻¹) := by
    have := congrArg Over.Hom.left hs1
    simpa [Inf, s] using this
  have e1 : (g * g0⁻¹) ≫ χ = 1 := h2 _ hh hinf
  have e2 : g0 ≫ χ = 1 := by
    simp only [g0, Category.assoc, h1 _ hsg, MonObj.comp_one]
  have : g = (g * g0⁻¹) * g0 := by rw [inv_mul_cancel_right]
  rw [this, MonObj.mul_comp, e1, e2]
  exact _root_.mul_one _

theorem killLocal_of : KillLocal := by
  intro κ _ _ A A' _ _ χ hχ P d hrep hsub h1 h2 T g hg
  obtain ⟨B, _, _, hfin, hfree, -, i, hmono, hi⟩ := hrep
  obtain ⟨y, rfl⟩ := (hi T g).2 hg
  suffices hmain : i ≫ χ = 1 by rw [Category.assoc, hmain, comp_one]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  have hpt : ∀ p : PrimeSpectrum B, ∃ f : B, p ∈ PrimeSpectrum.basicOpen f ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ {p} := by
    intro p
    obtain ⟨_, ⟨f, rfl⟩, hp, hs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_singleton p) (isOpen_discrete _)
    exact ⟨f, hp, hs⟩
  choose s hs hs' using hpt
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hs ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hspan).openCover _ _ fun p => ?_
  change spMap (algebraMap B (Localization.Away (s p))) ≫ _ = spMap (algebraMap B (Localization.Away (s p))) ≫ _
  haveI := away_local (s p) p (hs p) (hs' p)
  haveI hmax : p.asIdeal.IsMaximal := p.2.isMaximal'
  obtain ⟨ε⟩ := exists_eps κ B (s p) p.asIdeal (hs p)
  let j : algPt κ (Localization.Away (s p)) ⟶ algPt κ B := Over.homMk (spMap (algebraMap B (Localization.Away (s p)))) (by
    change spMap (algebraMap B (Localization.Away (s p))) ≫ spMap (algebraMap κ B) = spMap (algebraMap κ (Localization.Away (s p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  have hk : (j ≫ i) ≫ χ = 1 := local_kill κ A A' χ P hsub h1 _ ε (fun g hg hI => h2 _ ε g hg hI) (j ≫ i)
    (fun T y => (hi T _).1 ⟨y ≫ j, by simp⟩)
  have hk' : j ≫ i ≫ χ = j ≫ 1 := by rw [comp_one, ← Category.assoc, hk]
  exact congrArg (fun t => t.left) hk'

end UpperTheory.Gal.crystallineComparison.Mod
