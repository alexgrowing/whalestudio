import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
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
open GlobalTheory.IrrAn
open scoped GlobalTheory.AffinePoints

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace GlobalTheory.IrrSmooth

theorem exists_prime_cut {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {T : Set Y}
    (hT : IsClosed T) (hirr : IsIrreducible T) (hne : (T ∩ (V : Set Y)).Nonempty) :
    ∃ ξ : PrimeSpectrum Γ(Y, V), hV.fromSpec ξ ∈ T ∧
      ∀ x : V, (x : Y) ∈ T ↔ ξ.asIdeal ≤ (hV.primeIdealOf x).asIdeal := by
  set Z : Set (PrimeSpectrum Γ(Y, V)) := hV.fromSpec ⁻¹' T
  have hZc : IsClosed Z := hT.preimage hV.fromSpec.continuous
  have hZi : IsIrreducible Z := by
    obtain ⟨y, hyT, hyV⟩ := hne
    rw [← hV.range_fromSpec] at hyV
    obtain ⟨z, rfl⟩ := hyV
    exact ⟨⟨z, hyT⟩, hirr.2.preimage hV.fromSpec.isOpenEmbedding⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZi hZc
  refine ⟨ξ, ?_, fun x => ?_⟩
  · have : ξ ∈ Z := by rw [← hξ.def]; exact subset_closure rfl
    exact this
  have h1 : (x : Y) ∈ T ↔ hV.primeIdealOf x ∈ Z := by
    show _ ↔ hV.fromSpec (hV.primeIdealOf x) ∈ T
    rw [hV.fromSpec_primeIdealOf]
  rw [h1, ← hξ.def, ← PrimeSpectrum.le_iff_mem_closure]
  rfl

theorem isLocalization_away_quotient {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    [IsLocalization.Away t S] (Q : Ideal R) [Q.IsPrime] (ht : t ∉ Q) :
    IsLocalization.Away (Ideal.Quotient.mk Q t) (S ⧸ Q.map (algebraMap R S)) := by
  have hdisj : Disjoint (Submonoid.powers t : Set R) (Q : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact ht (‹Q.IsPrime›.mem_of_pow_mem n hn)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact ((IsLocalization.Away.algebraMap_isUnit t).map (Ideal.Quotient.mk _)).pow n
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers t) w
    refine ⟨⟨Ideal.Quotient.mk Q a, ⟨_, n, rfl⟩⟩, ?_⟩
    simp only [map_pow, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [← map_pow, ← map_mul, ← map_pow, h]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨1, ?_⟩
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq] at hxy
    rw [← map_sub] at hxy
    have : a - b ∈ Q := by
      rw [← IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers t) S ‹_› hdisj]
      exact hxy
    simp [Ideal.Quotient.eq.2 this]

open Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_affine_smooth_prime : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})), IsClosed T → IsIrreducible T → ∃ (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens) (hW : IsAffineOpen W), (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))).Nonempty ∧ ∃ P : Ideal Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W), P.IsPrime ∧ (∀ x : W, (x : (Limits.pullback p (spMap σ) : Scheme.{0})) ∈ T ↔ P ≤ (hW.primeIdealOf x).asIdeal) ∧ letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra; Algebra.FiniteType ℂ (Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) ∧ ∃ d' : ℕ, GlobalTheory.AffinePoints.HasAlgebraicCharts ℂ (Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) d' := by
  intro k _ X p _ σ T hT hirr
  set Y : Scheme.{0} := pullback p (spMap σ)
  set q : Y ⟶ Sp ℂ := pullback.snd p (spMap σ)
  have hft : ∀ U : Y.Opens, IsAffineOpen U → (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q U).FiniteType := fun U hU =>
    (HasRingHomProperty.appLE @LocallyOfFiniteType q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  obtain ⟨y, hy⟩ := hirr.nonempty
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  replace hV : IsAffineOpen V := hV
  obtain ⟨ξ, hξT, hQT⟩ := exists_prime_cut hV hT hirr ⟨y, hy, hyV⟩
  set Q := ξ.asIdeal
  letI : Algebra ℂ Γ(Y, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hft V hV
  haveI : Algebra.FiniteType ℂ (Γ(Y, V) ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q) Ideal.Quotient.mk_surjective
  obtain ⟨d, hd, -⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq ℂ (Γ(Y, V) ⧸ Q)
  obtain ⟨s, hs0, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension (K := ℂ) hd
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
  have ht : t ∉ Q := fun h => hs0 (Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hW : IsAffineOpen (Y.basicOpen t) := hV.basicOpen t
  have hWV : Y.basicOpen t ≤ V := Y.basicOpen_le t
  have hloc := hV.isLocalization_basicOpen t
  set W := Y.basicOpen t
  have hres : algebraMap Γ(Y, V) Γ(Y, W) = (Y.presheaf.map (homOfLE hWV).op).hom := rfl
  set P := Q.map (algebraMap Γ(Y, V) Γ(Y, W))
  have hdisj : Disjoint (Submonoid.powers t : Set Γ(Y, V)) (Q : Set Γ(Y, V)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact ht (ξ.2.mem_of_pow_mem n hn)
  haveI hP : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) _ Q ξ.2 hdisj
  refine ⟨W, hW, ⟨hV.fromSpec ξ, hξT, ?_⟩, P, hP, fun x => ?_, ?_⟩
  · have : ξ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen t := by
      rw [hV.fromSpec_preimage_basicOpen]; exact ht
    exact this
  · have hxV : (x : Y) ∈ V := hWV x.2
    have hc := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 Y) V hV W hW hWV x.2
    rw [hQT ⟨x, hxV⟩, Ideal.map_le_iff_le_comap]
    have hc' := congrArg PrimeSpectrum.asIdeal hc
    simp only [PrimeSpectrum.comap_asIdeal] at hc'
    convert Iff.rfl using 2
    rw [hres]
    convert hc' using 3
    all_goals first | rfl | simp [Scheme.Hom.appLE]
  · letI : Algebra ℂ Γ(Y, W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q W).toAlgebra
    haveI : Algebra.FiniteType ℂ Γ(Y, W) := hft W hW
    refine ⟨Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) Ideal.Quotient.mk_surjective,
      d, ?_⟩
    haveI := isLocalization_away_quotient (S := Γ(Y, W)) t Q ht
    haveI : IsScalarTower ℂ (Γ(Y, V) ⧸ Q) (Γ(Y, W) ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply ℂ Γ(Y, W) (Γ(Y, W) ⧸ P),
        IsScalarTower.algebraMap_apply ℂ Γ(Y, V) (Γ(Y, V) ⧸ Q), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_quotient_map_quotient]
      congr 1
      simp only [RingHom.algebraMap_toAlgebra, hres, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, RingHom.comp_apply]
      change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ q.appLE ⊤ V _ ≫
        Y.presheaf.map (homOfLE hWV).op).hom c
      have e1 : q.appLE ⊤ V (by simp) ≫ Y.presheaf.map (homOfLE hWV).op = q.appLE ⊤ W (by simp) :=
        Scheme.Hom.appLE_map ..
      rw [e1]
      rfl
    let e := (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk Q t))
      (Localization.Away (Ideal.Quotient.mk Q t)) (Γ(Y, W) ⧸ P)).restrictScalars ℂ
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := d) (e := e)
    exact GlobalTheory.AffinePoints.hasAlgebraicCharts_of_isStandardSmooth

end GlobalTheory.IrrSmooth
