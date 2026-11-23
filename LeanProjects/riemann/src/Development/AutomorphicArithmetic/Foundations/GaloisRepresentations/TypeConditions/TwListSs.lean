import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.HeckeCharacterEqualityOfRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

end Alg

variable (D : D7) (i : D.nd.Loc)

theorem isSSRep_of_mem_twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (hR : ∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) : ∀ p ∈ twList D i Pa R, IsSSRep p.2 := by
  intro p hp
  obtain ⟨k, a, -, rfl⟩ := mem_twList D i hp
  exact ss_twGL _ _ (hR k).2.1

theorem segment_eq_of_eigenvector_chi1 (_h3 : HeckeCharEqOfLAdicRealisation) (h4 : MuChar) (hA : Formalism.MainNotions.SumRepresentations.admitted D) (hg : HG D.nd D.naut i)
    (p : Part D.naut.CG) (Rk : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)))
    (hR : UpperTheory.GalS.IsStringRepN D i p Rk) (ha : p.a = 1) (hd : p.d = D.R.t) (u : Fin p.a → Qbar (D.nd.l i)) (hu0 : u ≠ 0)
    (hu : ∀ g, ((Rk g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i))).mulVec u =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) • u) :
    p = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
  have h3 := GlobalTheory.HeckeCharacterEquality.heckeCharacterEqualityOfRealisation
  rcases p with ⟨a, π, d⟩
  dsimp only at ha hd
  subst ha hd
  have hu00 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
  have h00 : ∀ g, ((Rk g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) := fun g => by
    have := congrFun (hu g) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hu00 this
  have hπ := h3 D hA i π (D.naut.tw (D.naut.muC i) D.naut.etaTinv) _ Rk hR.2.2 (h4 D hA i hg Rk h00)
  subst hπ
  rfl

end GlobalTheory.EigenPoint
