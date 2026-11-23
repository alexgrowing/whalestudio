import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hz

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hE : ∀ l k, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (y : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) l k ∈ Formalism.UG.intL (w.adicCompletion L) :=
    fun l k => (Dv.integ _).1 (compAt_mem_tensInt L v (hy l k))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hE l k)) (hP k j)

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
