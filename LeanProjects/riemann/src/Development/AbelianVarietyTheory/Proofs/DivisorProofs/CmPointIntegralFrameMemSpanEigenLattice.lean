import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedSpanEigenVectorMemEigenSublatticeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointCoordinatesMemSpanEigenLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisCompletionInSpanLieLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisFibreOverCompletionFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrameStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hchg hint i
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field E H K B t₀ m2 F T iK t' n'
  obtain ⟨vV, hvV, hvVM⟩ := GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice E H K B F 𝔓 T iK hiK ρV hρV G n
  choose M w hMw hMn hMspan using hvVM
  obtain ⟨ub, hubT, -, -, hubu⟩ := hint
  obtain ⟨u', hu'1, hu'2⟩ := hubu ρ i
  obtain ⟨av, w₁, hw₁, hw₁c⟩ := GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis E H K B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV
    (fun k => ⟨w k, hMw k, hMn k⟩) (ub ρ i) u' (hubT ρ i) hu'2
  have hbase : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← hw₁]; exact Over.w w₁
  obtain ⟨w₂, hw₂, hw₂c⟩ := GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ u hu T iK yT hyT t' n' m1' h1 v' hv'
    hv'φ C a y' hchg i u' hbase hu'1
  obtain rfl : w₁ = w₂ := Over.OverMorphism.ext (hw₁.trans hw₂.symm)
  have htan : IsTangent w₁ :=
    (GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).2.1 _ _ hw₁c
  have heq := (hv'.2 w₁ htan).unique hw₁c hw₂c
  have hWlie : (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V
      ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
    rw [← heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hMspan k)
  obtain ⟨r', -, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K B.pol F (𝓞 E) B.t.act
  have hueig : ∀ j a, r' a (u j) = ((tt a : 𝓞 K) : K) • u j := by
    intro j a
    have := ((hr' tt (u j)).2).1 (GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu j) a
    rw [this, ← algebraMap_smul K (tt a) (u j)]
  have hx := GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice K F.P₀.g F.lieLat (𝓞 E) (fun a => LinearMap.toMatrix' (r' a))
    (fun a => ((tt a : 𝓞 K) : K)) 𝔓 T iK hiK (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K B.pol F).1 _ hWlie (fun a => by
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, smul_comm]
      congr 1
      funext k
      rw [show (fun k => iK (u j k)) = iK ∘ u j from rfl, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, hueig j a]
      simp)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨c', ⟨hc1, hc2⟩, rfl⟩
  refine ⟨c', (hr' tt c').1.2 ⟨hc1, fun a => ?_⟩, rfl⟩
  have := hc2 a
  rw [LinearMap.toMatrix'_mulVec] at this
  rw [this, ← algebraMap_smul K (tt a) c']
