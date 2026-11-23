import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ClopenPush

theorem isSection_pot_sec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) [CompactSpace (CxPts (genStr Z) σ)] (hu : IsOpenEmbedding (up j hj σ)) (hc : IsClosed (Set.range (up j hj σ))), ClopenPush.LiftsFns j hj σ → ∀ {B : LB Y} (ψ : Weight q (σ.comp β) B) (s : B.Sec), IsSection (manifold Z σ).finAtlas (ClopenPush.pot (up j hj σ) hu hc ψ.locPot) (ClopenPush.sec (up j hj σ) (ψ.locSec (secVal q (σ.comp β) s))) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z _ Y q j hj σ _ hu hc hL B ψ s
  refine ⟨fun x => ?_, fun x x' z hz => ?_⟩
  · rw [AnRead.finAtlas_holoOn_iff _ (LocPot.isOpen_U _ x)]
    by_cases hx : x ∈ Set.range (up j hj σ)
    · obtain ⟨y₀, rfl⟩ := hx
      rw [pot_U_up]
      have h := fun y : ψ.locPot.U y₀ => hL _ (s.f (pick ψ.isLB y₀)) y.1 y.2
      choose W G hW hG using h
      refine AnRead.holoOn_of_cover (T := fun y => ptsIn (genStr Z) σ (W y))
        (fun _ => isOpen_ptsIn _) ?_ fun y => ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, hW _⟩
      · refine (((manifold Z σ).holoOn_ev _ (G y)).mono Set.inter_subset_right).congr ?_
        rintro _ ⟨⟨y', -, rfl⟩, h'⟩
        rw [sec_up _ hu.injective, (hG y y' h').2]
        rfl
    · exact AnRead.HoloOn.congr (f := fun _ => 0) (fun _ => differentiableOn_const (0 : ℂ))
        fun z _ => sec_of_not _ hx z
  · by_cases hx : x ∈ Set.range (up j hj σ)
    · have hz' := pot_U_subset hu hc _ hx hz.1
      by_cases hx' : x' ∈ Set.range (up j hj σ)
      · obtain ⟨y, rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hx'
        obtain ⟨w, rfl⟩ := hz'
        rw [pot_U_up, pot_U_up, Set.mem_inter_iff, hu.injective.mem_set_image,
          hu.injective.mem_set_image] at hz
        rw [sec_up _ hu.injective, sec_up _ hu.injective, pot_φ_up, pot_φ_up]
        exact (ψ.norm_mul_exp_eq_sqrt (secVal_mem s) hz.1).trans
          (ψ.norm_mul_exp_eq_sqrt (secVal_mem s) hz.2).symm
      · have h2 := hz.2
        rw [pot_U_of_not hu hc _ hx'] at h2
        exact absurd hz' h2
    · by_cases hx' : x' ∈ Set.range (up j hj σ)
      · have h1 := hz.1
        rw [pot_U_of_not hu hc _ hx] at h1
        exact absurd (pot_U_subset hu hc _ hx' hz.2) h1
      · rw [sec_of_not _ hx, sec_of_not _ hx', norm_zero, zero_mul, zero_mul]

end GlobalTheory.ClopenPush
