import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameVal

theorem exists_framed_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ y h hO hτ _ hy hf₁ hf₂
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  have hfib : (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  obtain ⟨g, b, hb, hS⟩ := h3 _ hfib
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G ℂ (y ≫ Y.j)
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h ER MR Z.gen inferInstance
  have hval : ∀ {n : ℕ} (τ' : E →+* ℂ) (e : Fin n → Z.V), (Z.eig τ').IsFrameAt e ⟨centre (y ≫ Y.j), h⟩ →
      ∀ i, ∃ w, Z.M.ValAt (y ≫ Y.j) (e i) (MR.pt w) := fun τ' e hf i => by
    have hmem : e i ∈ Z.eig τ' ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨ev ⟨e i, hmem.1⟩, (hev _ _).2 ⟨hmem.1, rfl⟩⟩
  choose w₁ hw₁ using hval τ b₁ hf₁
  choose w₂ hw₂ using hval _ b₂ hf₂
  choose v hv using fun i => exists_sameVec_left Y y (MR.pt (w₁ i))
  choose w hw using fun j => exists_sameVec_left Y y (MR.pt (w₂ j))
  obtain ⟨hL₁, hL₂⟩ := GlobalTheory.CompanionTheory.Ar.LocFrames.lieMult_at y σ τ hy hτ
  refine ⟨v, w, ⟨hy, Set.subset_univ _, ?_, ?_⟩, fun i => ⟨_, hw₁ i, hv i⟩, fun j => ⟨_, hw₂ j, hw j⟩⟩
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y τ D.p b₁ v (fun i => MR.pt (w₁ i)) h hO.2.2 hy hL₁
      ⟨g, b, hb, hS τ⟩ hf₁ hw₁ hv
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y _ D.q b₂ w (fun j => MR.pt (w₂ j)) h hO.2.2 hy hL₂
      ⟨g, b, hb, hS _⟩ hf₂ hw₂ hw

end GlobalTheory.CompanionTheory.Ar.FrameVal
