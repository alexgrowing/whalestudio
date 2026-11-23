import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DegComp

theorem det_ne_zero_of_injective {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hπ : HoloMap B A π)
    (hinj : Function.Injective π) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : π ((B.chart j).symm y) ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hπ.1)
  have hI : Set.InjOn (A.chart k ∘ π ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) := by
    intro a ha b hb hab
    exact (B.chart j).symm.injOn ha.1 hb.1 (hinj ((A.chart k).injOn ha.2 hb.2 hab))
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn e _ (A.chart k ∘ π ∘ (B.chart j).symm) hU
    (fun w hw => (hπ.2 j k w hw).differentiableAt.differentiableWithinAt) hI y ⟨hy, hk⟩
  intro h0
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero h0
  have hker : LinearMap.ker (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  rw [hker] at hlt
  exact lt_irrefl _ hlt

theorem isDegreeOff_one_of_bijective {e : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X}
    (hπ : HoloMap B A π) (hbij : Function.Bijective π) : IsDegreeOff A B π 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · simpa using isAnalyticSubset_empty B
  · simp
  · intro x _
    obtain ⟨y, rfl⟩ := hbij.2 x
    have hfib : π ⁻¹' {π y} = {y} := by
      ext z
      simp [hbij.1.eq_iff]
    rw [hfib, Set.ncard_singleton]
  · intro j k y hy _ hk
    exact det_ne_zero_of_injective hπ hbij.1 j k hy hk

theorem holoMap_comp_isDegreeOff : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  intro e d X Y Z _ _ _ _ _ _ A B C π h br hπ hbij hh hd
  obtain ⟨g, hgl, hgr, hg⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one A B π hπ
    (isDegreeOff_one_of_bijective hπ hbij)
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, ?_⟩
  obtain ⟨han, hint, hpan, hpint, hfib, hdet⟩ := hd
  have hpre : (π ∘ h) ⁻¹' (π '' br) = h ⁻¹' br := by
    ext z
    simp [hbij.1.mem_set_image]
  have himg : π '' br = g ⁻¹' br := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hgl] using hy
    · intro hx
      exact ⟨g x, hx, hgr x⟩
  let E : Y ≃ₜ X :=
    { toFun := π, invFun := g, left_inv := hgl, right_inv := hgr,
      continuous_toFun := hπ.1, continuous_invFun := hg.1 }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    intro x
    obtain ⟨W, hW, hxW, r, f, hf, hS⟩ := han (g x)
    refine ⟨g ⁻¹' W, hW.preimage hg.1, hxW, r, fun i => f i ∘ g,
      fun i => GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_comp hg (hf i), ?_⟩
    ext y
    simpa using Set.ext_iff.1 hS (g y)
  · change interior (E '' br) = ∅
    rw [← E.image_interior, hint, Set.image_empty]
  · rw [hpre]
    exact hpan
  · rw [hpre]
    exact hpint
  · intro x hx
    have hgx : g x ∉ br := fun hb => hx ⟨g x, hb, hgr x⟩
    have hset : (π ∘ h) ⁻¹' {x} = h ⁻¹' {g x} := by
      ext z
      constructor
      · intro hz
        have hz' : π (h z) = x := hz
        change h z = g x
        rw [← hz', hgl]
      · intro hz
        have hz' : h z = g x := hz
        change π (h z) = x
        rw [hz', hgr]
    rw [hset]
    exact hfib _ hgx
  · intro j k y hy hnot hk
    have hnot' : (C.chart j).symm y ∉ h ⁻¹' br := by rwa [hpre] at hnot
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp]
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact det_ne_zero_of_injective hπ hbij.1 l k hQt hk'
    · rw [hQdef]
      exact hdet j l y hy hnot' hl

end GlobalTheory.CompanionTheory.Ar.DegComp
