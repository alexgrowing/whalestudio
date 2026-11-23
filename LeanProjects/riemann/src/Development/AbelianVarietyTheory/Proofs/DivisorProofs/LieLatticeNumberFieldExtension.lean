import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTangentEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperPointExtendsRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyIndependentTangentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentTangentLettersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentBaseChangeTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEquivFinStatement

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightParts

set_option maxHeartbeats 1000000 in
theorem exists_isLieAtWith : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∀ (y : Pt O.s) (K₀ : Type) [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (io : K →+* Qb) (j : K₀ →+* K) (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)), io.comp j = io₀ ∧ IsLieAtWith O x P y K io L h := by
  intro _ _ D O x P hC y K₀ _ _ io₀
  obtain ⟨K, _, _, io, j, fK, yK, hio, b, hj, hK, hb⟩ := GlobalTheory.T.base_change_tangent_embedding D O y K₀ io₀
  have hs : (yK ≫ genι O.s.T.Z) ≫ O.s.T.Z.s = spMap (fK.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) := by
    rw [Category.assoc, show genι O.s.T.Z ≫ O.s.T.Z.s = genStr O.s.T.Z ≫ spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F) from
      Limits.pullback.condition, ← Category.assoc, hK, spMap_comp_spMap]
  obtain ⟨xO, hx⟩ := GlobalTheory.T.proper_point_extends_ring_of_integers O.κ.c.F O.s.T.Z.X O.s.T.Z.s O.s.T.Z.proj K fK (yK ≫ genι O.s.T.Z) hs
  obtain ⟨e⟩ := GlobalTheory.T.letters_equiv_fin D O
  have hio' : spMap io ≫ yK ≫ genι O.s.T.Z = y.y ≫ genι O.s.T.Z := by rw [← Category.assoc, hio]
  have hliK : LinearIndependent K (fun i => b (e i)) := by
    have hQ := (GlobalTheory.T.linearIndependent_tangent_letters D O y).comp e e.injective
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h2 : ∀ k, bcTan (t := O.s.T.Z.t) io hio' (b (e k)) = tanOf (y.tan (e k).1 (e k).2) :=
      fun k => tan_ext ((hb (e k)).trans (left_tanOf _).symm)
    have h1 := congrArg (bcTan (t := O.s.T.Z.t) io hio') hc
    rw [map_zero, map_sum] at h1
    simp only [map_smulₛₗ, h2] at h1
    exact io.injective ((Fintype.linearIndependent_iff.1 hQ (fun k => io (c k)) h1 i).trans (map_zero io).symm)
  have hli : ∀ σ : K →+* ℂ, LinearIndependent ℂ
      (fun i => bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (b (e i))) := fun σ =>
    GlobalTheory.T.linearIndependent_base_change_tangent O.s.T.Z.t σ _ _ hliK
  obtain ⟨h, hh⟩ := GlobalTheory.T.hermitian_family_independent_tangents D O x K fK yK hK (fun i => b (e i)) hli
  exact ⟨K, inferInstance, inferInstance, io, j, lieCoordLat O.s.T.Z.t hx (fun i => b (e i)), h, hj,
    fK, yK, xO, hx, hio, e, fun i => b (e i), hC, hK, fun i => hb (e i), rfl, hh⟩

end GlobalTheory.HeightParts

end
