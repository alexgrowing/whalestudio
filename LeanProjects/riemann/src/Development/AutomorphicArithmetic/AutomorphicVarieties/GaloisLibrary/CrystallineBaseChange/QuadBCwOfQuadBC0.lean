import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ConjAlgebraMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcDual0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.V.Br

theorem quadBC0_of_cyclic (art : GlobalTheory.Published.GlobalArtinReciprocity) (smo : StrongMultOneReal) (cyc : CyclicBaseChange) : QuadBC0 :=
  fun F E _ _ _ _ _ _ _ h2 a _ ha π _ => (weakEx cyc F E h2 a ha π).imp_left fun ⟨η, hη, ht⟩ =>
    ⟨η, normQuad art F E h2 η hη, selfIso smo F a ha π η (h2 ▸ hη.2.1) ht⟩

theorem quadBCw_of_quadBC0 (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hC : ExC) (hR : ExR) (h : QuadBC0) : QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a _ ha π hr
  refine (h F E h2 a ha π hr).imp_right fun ⟨P, hP⟩ => ⟨P, hP, fun hreg ⟨χ, hχ⟩ => ?_⟩
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  exact splitOf hN hC hR F E h2 a ha π χ P hreg hχ hP

theorem quadBCw (P : Hypotheses₂) : QuadBCw :=
  quadBCw_of_quadBC0 P.litN (galoisExistence_from_published P) (realExistence_from_published P) P.bc

def BcPolarW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ n),
      π.IsRegAlg → Continuous r → AttR ι r π → IsCycWt l wt θ → DualTw r θ → IsIrr (r.comp (res ℚ Ω K)) →
      ∃ (P : CuspSub K n) (χ : HChar (maximalRealSubfield K)) (μ : G (maximalRealSubfield K) Ω →* (Qbar l)ˣ),
        IsBCw π P ∧ AttC ι (r.comp (res ℚ Ω K)) P ∧ GlobalTheory.ContraPair.PolarizedPair P χ ∧ IsLAdicCharOf ι χ μ ∧
        μ.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1)

end UpperTheory.V.Br
