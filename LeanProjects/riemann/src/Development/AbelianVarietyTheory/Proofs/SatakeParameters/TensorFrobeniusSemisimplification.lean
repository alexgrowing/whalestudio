import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.WeilDeligne

theorem isNilpotent_map_left {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X : Module.End K U} (Y : Module.End K W) (hX : IsNilpotent X) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem isNilpotent_map_right {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] (X : Module.End K U) {Y : Module.End K W} (hY : IsNilpotent Y) :
    IsNilpotent (TensorProduct.map X Y) := by
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, ?_⟩
  rw [TensorProduct.map_pow, hn]
  exact TensorProduct.ext' fun x y => by simp

theorem commute_map {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] {X X' : Module.End K U} {Y Y' : Module.End K W}
    (hX : Commute X X') (hY : Commute Y Y') :
    Commute (TensorProduct.map X Y) (TensorProduct.map X' Y') := by
  show TensorProduct.map X Y * TensorProduct.map X' Y' = TensorProduct.map X' Y' * TensorProduct.map X Y
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hX.eq, hY.eq]

theorem IsFrobSS.tensor : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → Module.End ℂ V} {N : Module.End ℂ V} {a : WDRep h V} {ρ' : ↥(Weil h) → Module.End ℂ V'} {N' : Module.End ℂ V'} {b : WDRep h V'}, IsFrobSS ρ N a → IsFrobSS ρ' N' b → IsFrobSS (fun g => TensorProduct.map (ρ g) (ρ' g)) (N.rTensor V' + N'.lTensor V) (a.tensor b) := by
  intro E Ω _ _ _ _ _ A w h V V' _ _ _ _ _ _ ρ N a ρ' N' b ha hb
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ]
    exact commute_map (ha.2 g).1 (hb.2 g).1
  · rw [WDRep.tensor_ρ]
    have e : TensorProduct.map (ρ g) (ρ' g) - TensorProduct.map (a.ρ g) (b.ρ g) =
        TensorProduct.map (ρ g - a.ρ g) (ρ' g) + TensorProduct.map (a.ρ g) (ρ' g - b.ρ g) :=
      TensorProduct.ext' fun x y => by
        simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    rw [e]
    refine Commute.isNilpotent_add ?_ (isNilpotent_map_left _ (ha.2 g).2)
      (isNilpotent_map_right _ (hb.2 g).2)
    exact commute_map ((ha.2 g).1.symm.sub_left (Commute.refl _))
      ((Commute.refl _).sub_right (hb.2 g).1.symm)

end GlobalTheory.WeilDeligne
