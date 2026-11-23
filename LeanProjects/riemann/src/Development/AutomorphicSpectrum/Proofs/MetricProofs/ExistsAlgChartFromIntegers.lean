import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIffStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown

theorem etale_res_int {X : Scheme.{0}} (t : X ⟶ Sp ℤ) {U : X.Opens} (hU : IsAffineOpen U) (n : Γ(X, U))
    {D : ℕ} (x : Fin D → Γ(X, U)) (h : (MvPolynomial.eval₂Hom (algX t U) x).Etale) :
    (MvPolynomial.eval₂Hom (Int.castRingHom Γ(X, X.basicOpen n))
      fun a => resG X (X.basicOpen_le n) (x a)).Etale := by
  have hloc := hU.isLocalization_basicOpen n
  have hres : (resG X (X.basicOpen_le n)).Etale :=
    RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway n)
  have hcomp := RingHom.Etale.stableUnderComposition _ _ h hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  rwa [show (resG X (X.basicOpen_le n)).comp (algX t U) = Int.castRingHom _ from RingHom.ext_int _ _] at hcomp

theorem isUnit_natCast_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (N : ℕ) :
    IsUnit (N : Γ(X, X.basicOpen (N : Γ(X, U)))) := by
  have hloc := hU.isLocalization_basicOpen (N : Γ(X, U))
  have := IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen (N : Γ(X, U)))) (N : Γ(X, U))
  simpa using this

theorem mem_ptsIn_basicOpen_natCast {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {U : X.Opens} {N : ℕ} (hN : N ≠ 0) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    y ∈ ptsIn p σ (X.basicOpen (N : Γ(X, U))) := by
  refine (mem_ptsIn_basicOpen hy _).2 ?_
  have h := ev_algX hy (N : k)
  rw [map_natCast, map_natCast] at h
  rw [h]
  exact_mod_cast hN

end GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown

open GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown in

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  intro k _ _ _ _ X p t τ σ D c' hne
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  have hle := X.basicOpen_le (N : Γ(X, c'.U))
  have hetZ := etale_res_int t c'.affine (N : Γ(X, c'.U)) c'.x c'.etale
  have hetk := (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hN (algX p (X.basicOpen (N : Γ(X, c'.U))))
    (isUnit_natCast_basicOpen c'.affine N) D _).2 hetZ
  let s := IsOpenEmbedding.toOpenPartialHomeomorph (sheet t τ : CxPts p σ → CxPts t τ) hemb
  have hs : (s : CxPts p σ → CxPts t τ) = sheet t τ := IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb
  have hss : s.source = Set.univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb
  have hst : s.target = Set.range (sheet t τ : CxPts p σ → CxPts t τ) :=
    IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb
  have hsrc : (s.trans c'.e).source = sheet t τ ⁻¹' c'.e.source := by
    rw [OpenPartialHomeomorph.trans_source, hss, Set.univ_inter, hs]
  have happ : ∀ y, (s.trans c'.e) y = c'.e (sheet t τ y) := fun y => by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hs]
  have hsym : ∀ v ∈ (s.trans c'.e).target, sheet t τ ((s.trans c'.e).symm v) = c'.e.symm v := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_target] at hv
    have h2 : c'.e.symm v ∈ s.target := hv.2
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, ← hs]
    exact s.right_inv h2
  refine ⟨{ e := s.trans c'.e
            U := X.basicOpen (N : Γ(X, c'.U))
            affine := c'.affine.basicOpen _
            x := fun a => resG X hle (c'.x a)
            etale := hetk
            source_subset := ?_
            apply_eq := ?_
            holo := ?_ }, hsrc, fun y _ => (happ y).symm⟩
  · intro y hy
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    exact mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
  · intro y hy a
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    have hB := mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
    rw [happ, c'.apply_eq _ hy a, ev_res hle hB]
    rfl
  · intro W f
    refine ((c'.holo W f).mono ?_).congr ?_
    · rintro v ⟨hv, hw⟩
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.trans_target] at hv
        exact hv.1
      · show c'.e.symm v ∈ ptsIn t τ W
        rw [← hsym v hv]
        exact hw
    · rintro v ⟨hv, -⟩
      show ev p σ W f _ = ev t τ W f (c'.e.symm v)
      rw [← hsym v hv]
      rfl
