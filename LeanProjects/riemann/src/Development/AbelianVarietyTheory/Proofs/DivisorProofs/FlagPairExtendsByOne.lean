import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundle

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.Vert.Model.FlagPair

theorem nonempty_extend : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O) (E E' K K' : Z.X.Modules) (φ : Z.GenIso E E') (i : K ⟶ E) (i' : K' ⟶ E') (ψ : Z.GenIso K K') (r : ℕ), GlobalTheory.VB.IsSubbundle i → GlobalTheory.VB.IsSubbundle i' → GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom → GlobalTheory.Vert.Model.FlagPair ψ r → Nonempty (GlobalTheory.Vert.Model.FlagPair φ (r + 1)) := by
  intro O _ _ _ Z E E' K K' φ i i' ψ r hi hi' hE hE' hcomm P

  let G : Fin (r + 2) → Σ A : Z.X.Modules, Σ A' : Z.X.Modules,
      (A ⟶ E) × (A' ⟶ E') × Z.GenIso A A' :=
    fun j => Fin.lastCases
      (motive := fun _ => Σ A : Z.X.Modules, Σ A' : Z.X.Modules, (A ⟶ E) × (A' ⟶ E') × Z.GenIso A A')
      ⟨E, E', 𝟙 E, 𝟙 E', φ⟩
      (fun k => ⟨P.fl.F k, P.fl'.F k, P.fl.ι k ≫ i, P.fl'.ι k ≫ i', P.gen k⟩) j
  have hlast : G (Fin.last (r + 1)) = ⟨E, E', 𝟙 E, 𝟙 E', φ⟩ := Fin.lastCases_last ..
  have hcast (k : Fin (r + 1)) :
      G k.castSucc = ⟨P.fl.F k, P.fl'.F k, P.fl.ι k ≫ i, P.fl'.ι k ≫ i', P.gen k⟩ :=
    Fin.lastCases_castSucc ..
  have hsub (j : Fin (r + 2)) : GlobalTheory.VB.IsSubbundle (G j).2.2.1 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact Flag.isSubbundle_ι_comp hi P.fl k
  have hsub' (j : Fin (r + 2)) : GlobalTheory.VB.IsSubbundle (G j).2.2.2.1 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact Flag.isSubbundle_ι_comp hi' P.fl' k
  have hvb (j : Fin (r + 2)) : GlobalTheory.VB.IsVB (G j).1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE
    | cast k => rw [hcast]; exact P.fl.isVB k
  have hvb' (j : Fin (r + 2)) : GlobalTheory.VB.IsVB (G j).2.1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE'
    | cast k => rw [hcast]; exact P.fl'.isVB k
  have hstep (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).1 ⟶ (G k.succ).1, f ≫ (G k.succ).2.2.1 = (G k.castSucc).2.2.1 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨P.fl.ι _ ≫ i, Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨P.fl.step k, P.fl.step_ι_assoc k i⟩
  have hstep' (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).2.1 ⟶ (G k.succ).2.1,
        f ≫ (G k.succ).2.2.2.1 = (G k.castSucc).2.2.2.1 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨P.fl'.ι _ ≫ i', Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨P.fl'.step k, P.fl'.step_ι_assoc k i'⟩
  have hgen (j : Fin (r + 2)) : (G j).2.2.2.2.hom ≫ Z.genRes.map (G j).2.2.2.1 =
      Z.genRes.map (G j).2.2.1 ≫ φ.hom := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; simp
    | cast k =>
      rw [hcast]
      dsimp only
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, P.gen_ι, Category.assoc, hcomm,
        Category.assoc]
  choose step step_ι using hstep
  choose step' step_ι' using hstep'
  have hiso : IsIso (G (Fin.last (r + 1))).2.2.1 := by
    rw [hlast]; exact IsIso.id E
  have hiso' : IsIso (G (Fin.last (r + 1))).2.2.2.1 := by
    rw [hlast]; exact IsIso.id E'
  exact ⟨{ fl := { F := fun j => (G j).1
                   ι := fun j => (G j).2.2.1
                   isSubbundle := hsub
                   isVB := hvb
                   step := step
                   step_ι := step_ι
                   isIso_last := hiso }
           fl' := { F := fun j => (G j).2.1
                    ι := fun j => (G j).2.2.2.1
                    isSubbundle := hsub'
                    isVB := hvb'
                    step := step'
                    step_ι := step_ι'
                    isIso_last := hiso' }
           gen := fun j => (G j).2.2.2.2
           gen_ι := hgen }⟩

end GlobalTheory.Vert.Model.FlagPair
