import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.FlagComponentTrueModel
import Development.AutomorphicArithmetic.DivisorFrames.GenericPointOfCoverLifts
import Development.AutomorphicArithmetic.DivisorFrames.NormalSchemePAdicReduction
import Development.AutomorphicArithmetic.DivisorFrames.GenericCoverPointModel
import Development.AutomorphicArithmetic.DivisorFrames.ConjugateEmbeddingsCutAndDual
import Development.AutomorphicArithmetic.DivisorFrames.LocalFramesOverCover
import Development.AutomorphicArithmetic.DivisorFrames.FlagComponentEigenFrame
import Development.AutomorphicArithmetic.DivisorFrames.FlagComponentEigenCoordinates
import Development.AutomorphicArithmetic.DivisorFrames.ChartMinorsValuationBound
import Development.AutomorphicArithmetic.DivisorFrames.AffineOpenTangentCombinations
import Development.AutomorphicArithmetic.DivisorFrames.HeightChartsCoverPowerTangents
import Development.AutomorphicArithmetic.DivisorFrames.HeightChartsTwoFamilies
import Development.AutomorphicArithmetic.DivisorFrames.PairDataLocalFrames
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.RootFrame

open GlobalTheory.LineNorm GlobalTheory.Toroidal

private theorem pairData_root (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [IsGalois ℚ E] (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (F : Type) [Field F] [NumberField F] (ε : F ≃+* c.F) (C : FlagCpt Z ε) [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated)
    (M₀ : GlobalTheory.TrueGeo.Model C.Y) (ρ₀ : M₀.X ⟶ Z.X) (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₀.X)
    (hρ₀ : M₀.j ≫ ρ₀ = C.π ≫ genι Z) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (a : ℕ → Bool) (R : Option ℝ) (p : ℕ)
    (hp : p.Prime) (ha : a p = true) {Cx : CxSt F} (hm : Mets C Cx) :
    PairData (fun i : Fin (Dw.p + Dw.q) => adlOf C hm (rootSym Dw a R τ i)) p := by
  haveI := Fact.mk hp
  have hκ : 0 ≤ vDiff E p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_ge (vDiff E p + 2)
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  obtain ⟨V₀, hV₀⟩ := UpperTheory.flag_component_true_model E H Dw l Xo c Z F ε C hX M₀ ρ₀ hM hρ₀ τ a R p (Dw.p + Dw.q)
  obtain ⟨V, b, g, ρ', -, e₁, e₂, -, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists E H Z.X Z.t F C.Y M₀ ρ₀ V₀ (p ^ n) (pow_ne_zero _ hp.ne_zero)
  rw [hρ₀] at e₄
  haveI := Z.jQ_open
  let W : C.Y.X.Opens := C.π ⁻¹ᵁ Z.jQ.opensRange
  have hgen : C.π (genericPoint C.Y.X) ∈ Set.range Z.jQ := by
    have h := congrArg (fun f => f (IsLocalRing.closedPoint C.Y.Fn)) C.y0_x
    refine ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (h.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg _ ?_)))⟩
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨y₀, hy₀⟩ := UpperTheory.generic_point_of_cover_lifts E H Dw l Xo c Z F C.Y V ρ' C.π e₄ hgen
  have hL := UpperTheory.normal_scheme_p_adic_reduction E H Dw l Xo c Z hX V.X ρ' y₀ p n V.normal hz hζ hs hy₀
  obtain ⟨K, hK₁, hK₂⟩ := UpperTheory.generic_cover_point_model hK E H Dw l Xo c Z hX F C.Y V ρ' C.π e₄ W (fun _ h => h) p n hn2 hL
  obtain ⟨M, o, S, S', hS, hS', hD⟩ := UpperTheory.conjugate_embeddings_cut_and_dual E H Dw p F (ε.symm.toRingHom.comp (embK c τ))
    (ε.symm.toRingHom.comp (embK c (conjEmb τ))) fun x => congrArg ε.symm (Subtype.ext (by
      show (starRingEnd ℂ) (τ (x : E)) = τ ((H.bar x : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]))
  have tri (σ : E →+* ℂ) : ∃ T, TriOf Z.t (C.π ≫ genι Z) (C.f0.v σ) (fun y => (fr C y).v σ) (fun y => dg C y σ) T := by
    choose cf h₁ h₂ h₃ using (isFlagFrame_eig C σ).tri
    exact ⟨fun y => Matrix.of fun k i => cf y i k, fun y => ⟨fun k i h => h₂ y i k h, fun i => ⟨h₁ y i, h₃ y i⟩⟩⟩
  choose T hT using tri
  choose P hP using fun (σ : E →+* ℂ) (j : V.X) => UpperTheory.local_frames_over_cover E H Z.X Z.t F C.Y V ρ' _ e₄ _ _ _ _ _
    (isFlagFrame_eig C σ).tan (hT σ) (K.U j) (K.aff j) (K.g j) (K.e j) (K.basis j) M fun m => K.h j (o m)
  have hE := UpperTheory.flag_component_eigen_frame E H Dw l Xo c Z F ε C p
  obtain ⟨r₁, r₂⟩ := UpperTheory.flag_component_eigen_coordinates E H Dw l Xo c Z F ε C τ hτ a R p hp ha
  have hd (σ : E →+* ℂ) (y : C.Y.X) (i : Fin (Dw.mult σ)) : T σ y i i = dg C y σ i := ((hT σ y).2 i).1
  refine ⟨V, W, V.X, K.U, Dw.mult τ, Dw.mult (conjEmb τ), GlobalTheory.ShFam.Pad.AdmExist.mult_add_mult_conj Dw τ,
    fun j => constM V S * P τ j, T τ, fun j => constM V S' * P (conjEmb τ) j, T (conjEmb τ), hgen,
    fun x _ => ⟨x, hK₁ x⟩, hV₀ V b g e₁ e₂, ?_, ?_, ?_⟩
  · refine UpperTheory.chart_minors_valuation_bound E H Z.X Z.t F C.Y V W p (C.π ≫ genι Z) V.X K.U _ _ (fun y => (fr C y).v τ) _ _ (vDiff E p) _ _
      (fun x => ⟨(hT τ x).1, fun i => ?_⟩)
      (fun j z hz' => UpperTheory.affine_open_tangent_combinations E H Z.X Z.t F C.Y V ρ' _ _ _ _ _ _ _ _ _ _ (hP τ j) _ S z hz') (fun i v e y hv => ?_)
      (UpperTheory.height_charts_cover_power_tangents E H Dw Z.X Z.t F C.Y V ρ' _ V.X K W p n hK₂ _ _ _ (hE τ) _ _ o S _ hS hκ hn _ _ (hP τ))
    · rw [hd]; exact (r₁ i).1 x
    · rw [hd]; exact (r₁ i).2 v e y hv
  · refine UpperTheory.chart_minors_valuation_bound E H Z.X Z.t F C.Y V W p (C.π ≫ genι Z) V.X K.U _ _ (fun y => (fr C y).v (conjEmb τ)) _ _ 0 _ _
      (fun x => ⟨(hT _ x).1, fun i => ?_⟩)
      (fun j z hz' => UpperTheory.affine_open_tangent_combinations E H Z.X Z.t F C.Y V ρ' _ _ _ _ _ _ _ _ _ _ (hP _ j) _ S' z hz') (fun i v e y hv => ?_)
      (UpperTheory.height_charts_cover_power_tangents E H Dw Z.X Z.t F C.Y V ρ' _ V.X K W p n hK₂ _ _ _ (hE _) _ _ o S' _ hS' le_rfl (by linarith) _ _ (hP _))
    · rw [hd]; exact (r₂ i).1 x
    · rw [hd]; exact (r₂ i).2 v e y hv
  · exact UpperTheory.height_charts_two_families E H Dw Z.X Z.t F C.Y V ρ' _ V.X K W p n hK₂ _ _ _ _ _ _ (hE τ) (hE _) _ _ o S S' _ hS hS' hD hκ hn
      _ _ _ _ (hP τ) (hP _)

end GlobalTheory.RootFrame

theorem _root_.GlobalTheory.T.root_symbol_local_frames : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (c : s.Comp) (hm : Mets (Φ.C c) (cxSt D.what₂.LL)) (p : ℕ), p.Prime → ∀ (a : ℕ → Bool), a p = true → ∀ (R : Option ℝ) (τ : D.what₂.Tau), LocFrames (fun i : Fin N => adlOf (Φ.C c) hm (rootSym S.Dw a R (DV.tauEmb D τ) i)) p := by
  intro h2 _ D A N j S κ s Φ c hm p hp a ha R τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨hX, hN, M₀, ρ₀, hM, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (Φ.C c).Y (𝓞 κ.c.F) (RingOfIntegers.mapRingEquiv κ.e)
    s.T.Z.X s.T.Z.s ((Φ.C c).π ≫ GlobalTheory.Toroidal.genι s.T.Z) s.T.Z.proj (by
      rw [← (Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hpq : S.Dw.p + S.Dw.q = N := S.rank_eq
  have h := GlobalTheory.RootFrame.pairData_root (GlobalTheory.HTKernel.hodgeTateKernelAtPoint h2) _ _ _ _ _ _ s.T.Z _ _ (Φ.C c) hX M₀ ρ₀ hM hρ
    (DV.tauEmb D τ) (A.cm τ) a R p hp ha hm
  have key : ∀ (n : ℕ), S.Dw.p + S.Dw.q = n →
      LocFrames (fun i : Fin n => adlOf (Φ.C c) hm (rootSym S.Dw a R (DV.tauEmb D τ) i)) p := by
    rintro n rfl
    exact UpperTheory.pair_data_local_frames _ _ _ _ _ p hp h
  exact key N hpq
