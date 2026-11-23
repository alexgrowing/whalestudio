import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem lacunary_image_sub {J : Finset ℤ} (c : ℤ) (h : Lacunary J) :
    Lacunary (J.image fun x => c - x) := by
  classical
  intro A B hA hB hd hAn hBn e
  have inj : Function.Injective (fun x : ℤ => c - x) := fun x y e => by simpa using e
  have back : ∀ S : Finset ℤ, S ⊆ J.image (fun x => c - x) → S.image (fun x => c - x) ⊆ J := by
    intro S hS x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (hS hy)
    simpa using hz
  have hsum : ∀ S : Finset ℤ, (S.image fun x => c - x).sum id = (S.card : ℤ) * c - S.sum id := by
    intro S
    rw [Finset.sum_image (fun x _ y _ e => inj e)]
    simp only [id]
    rw [Finset.sum_sub_distrib (fun _ => c) (fun x => x), Finset.sum_const, nsmul_eq_mul]
  refine h _ _ (back A hA) (back B hB) ((Finset.disjoint_image inj).2 hd) (hAn.image _) (hBn.image _) ?_
  rw [Finset.card_image_of_injective _ inj, Finset.card_image_of_injective _ inj, hsum, hsum]
  linear_combination -e

private theorem wtJumps_dual {a : ℕ} (lam : DomWeight a) :
    wtJumps lam.dual = (wtJumps lam).image fun x => ((a : ℤ) - 1) - x := by
  have key : ∀ k : Fin a, ((k : ℕ) : ℤ) - lam.dual.w k = ((a : ℤ) - 1) - (((k.rev : ℕ) : ℤ) - lam.w k.rev) := by
    intro k
    have h1 : lam.dual.w k = -lam.w k.rev := rfl
    have h2 := Fin.val_rev k
    have h3 := k.2
    rw [h1]
    omega
  ext x
  simp only [wtJumps, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k.rev, rfl⟩, (key k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k.rev, ?_⟩
    rw [key, Fin.rev_rev]

theorem UpperTheory.Gal.Int.Div.lacConj_of :
    CplMem → LacConj := by
  intro hC E _ _ _ l _ ι a ha U v ⟨τ, hτ, lam, hw, hl⟩
  refine ⟨ComplexEmbedding.conjugate τ, ?_, lam.dual, GlobalTheory.DefiniteBC.hasWeightAt_conjugate ha hw, ?_⟩
  · intro x hx
    have hy : ((IsCMField.ringOfIntegersComplexConj E x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := rfl
    have h := hτ _ ((hC E v x _ hy).1 hx)
    rw [hy, IsCMField.complexEmbedding_complexConj] at h
    exact h
  · rw [wtJumps_dual]
    exact lacunary_image_sub _ hl
