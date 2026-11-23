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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem valR_restrict_eq_valR {A : Type} [CommRing A] {X : Scheme.{0}} (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ X)
    {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj V)
    (f : X.presheaf.obj (Opposite.op U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y V ((X.presheaf.map (homOfLE hVU).op).hom f) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y U f := by
  have hU : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj U := h.trans (fun z hz => hVU hz)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  rw [dif_pos h, dif_pos hU]
  congr 1
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE]

private theorem isUnit_natCast_sp_complex_sections (N : ℕ) (hN : N ≠ 0) (W : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) :
    IsUnit (N : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.obj (Opposite.op W)) := by
  have h1 : IsUnit (N : ℂ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hN)
  have h2 := h1.map
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
  simpa only [map_natCast] using h2

private theorem etale_eval2Hom_basicOpen {k : Type} [CommRing k] {X : Scheme.{0}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (N : ℕ)
    (hNet : (Int.castRingHom (Localization.Away (N : k))).Etale)
    (φ : k →+* X.presheaf.obj (Opposite.op U)) {D : ℕ} (x : Fin D → X.presheaf.obj (Opposite.op U))
    (hx : (MvPolynomial.eval₂Hom φ x).Etale) :
    (MvPolynomial.eval₂Hom
      (Int.castRingHom (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))))
      (fun a => algebraMap (X.presheaf.obj (Opposite.op U))
        (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))) (x a))).Etale := by
  haveI := hU.isLocalization_basicOpen (N : X.presheaf.obj (Opposite.op U))
  have hres : (algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (N : X.presheaf.obj (Opposite.op U)))
  have hcomp : ((algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).comp
        (MvPolynomial.eval₂Hom φ x)).Etale :=
    RingHom.Etale.stableUnderComposition (MvPolynomial.eval₂Hom φ x) (algebraMap _ _) hx hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  have hunit : IsUnit
      ((N : X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))) := by
    simpa only [map_natCast] using
      IsLocalization.Away.algebraMap_isUnit
        (S := X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))
        (N : X.presheaf.obj (Opposite.op U))
  exact (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hNet _ hunit D _).mp hcomp

theorem algChart_toZ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) :
    ∃ c' : AlgChart t τ D, c'.e.source = sheet t τ '' c.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  classical
  obtain ⟨N, hN0, hNet⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  haveI : Nonempty (GlobalTheory.CxPts p σ) := ⟨c.e.symm (0 : EuclideanSpace ℂ (Fin D))⟩
  obtain ⟨E, hE, hEs, hEt⟩ : ∃ E : OpenPartialHomeomorph (GlobalTheory.CxPts p σ) (GlobalTheory.CxPts t τ),
      ⇑E = sheet t τ ∧ E.source = Set.univ ∧ E.target = Set.range (sheet t τ) :=
    ⟨_, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb⟩
  have hleft : ∀ y : GlobalTheory.CxPts p σ, E.symm (sheet t τ y) = y := by
    intro y
    have h := E.left_inv (x := y) (by rw [hEs]; trivial)
    rwa [hE] at h
  have hsrc : (E.symm.trans c.e).source = sheet t τ '' c.e.source := by
    ext z
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, hEt]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, by simpa [Set.mem_preimage, hleft] using hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by simpa [Set.mem_preimage, hleft] using hy⟩
  have hin : ∀ y ∈ c.e.source, ⊤ ≤ (TopologicalSpace.Opens.map (y.1).base).obj
      (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) := by
    intro y hy
    rw [AlgebraicGeometry.Scheme.preimage_basicOpen, AlgebraicGeometry.Scheme.basicOpen_of_isUnit]
    · exact c.source_subset hy
    · rw [map_natCast]
      exact isUnit_natCast_sp_complex_sections N hN0 _
  have het := etale_eval2Hom_basicOpen c.affine N hNet (algX p c.U) c.x c.etale
  refine ⟨⟨E.symm.trans c.e, X.basicOpen (N : X.presheaf.obj (Opposite.op c.U)),
      c.affine.basicOpen _, fun a => algebraMap (X.presheaf.obj (Opposite.op c.U)) _ (c.x a),
      ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · have hZ : algX t (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) =
        Int.castRingHom _ := RingHom.ext_int _ _
    rw [hZ]
    exact het
  · intro z hz
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hin y hy
  · intro z hz a
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft, c.apply_eq y hy a]
    exact (valR_restrict_eq_valR y.1 (X.basicOpen_le _) (hin y hy) (c.x a)).symm
  · intro W f
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm,
      OpenPartialHomeomorph.symm_symm, hE, OpenPartialHomeomorph.symm_target, hEs]
    refine ((c.holo W f).mono ?_).congr ?_
    · rintro v ⟨⟨hv1, -⟩, hv2⟩
      exact ⟨hv1, hv2⟩
    · intro v _
      rfl
  · intro y hy
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft]

end GlobalTheory.CompanionTheory.Ar.BaseZ
