import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoOfNoEmbOfInjectiveGenSpecial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelGenericSpecialDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelFrobeniusNoEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfMinorDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfEpimorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesFamilyStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ImageDescent

theorem mono_of_injective_codimOne : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (F : B.X.Modules) (u : P.mod ⟶ F), (∀ x : B.X, ringKrullDim (B.X.presheaf.stalk x) ≤ 1 → Function.Injective (stalkLinear u x)) → Mono u := by
  intro O _ _ _ p _ _ _ B hB P F u h
  refine GlobalTheory.FrobFilt.mono_of_noEmb_of_injective_genSpecial O B P.mod F u
    (GlobalTheory.FrobFilt.noEmb_pres hB P) fun η hη => h η ?_
  haveI := GlobalTheory.T.normal_model_generic_special_dvr O B hB η hη
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one]

theorem main : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (F : B.X.Modules) (u : P.mod ⟶ F), (∀ x : B.X, ringKrullDim (B.X.presheaf.stalk x) ≤ 1 → Function.Injective (stalkLinear u x)) → Mono u) ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (n : ℕ) (r m : Fin n → ℕ) (E F : Fin n → B.X.Modules) (u : ∀ i, F i ⟶ E i), (∀ i, GlobalTheory.VB.IsVB (E i) (r i) ∧ GlobalTheory.VB.IsVB (F i) (m i) ∧ Epi (B.genRes.map (u i))) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ i, GlobalTheory.VB.IsVB (Limits.image ((Scheme.Modules.pullback f.f).map (u i))) (r i)) := by
  refine ⟨mono_of_injective_codimOne, ?_⟩
  intro O _ _ _ p _ _ _ B hB n r m E F u hu
  obtain ⟨B', f, hn, hd, H⟩ := GlobalTheory.T.exists_local_frames_family O B hB n r m E F u fun i x =>
    GlobalTheory.T.exists_local_frames_of_epimorphism O B (r i) (m i) (E i) (F i) (u i) (hu i).1 (hu i).2.1 (hu i).2.2 x
  exact ⟨B', f, hn, hd, fun i => GlobalTheory.T.vector_bundle_of_minor_divisibility B'.X _ _ _ (r i) (m i) (H i)⟩

end GlobalTheory.ImageDescent
