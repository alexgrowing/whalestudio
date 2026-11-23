import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bridge
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology
section BN
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end BN
section G1
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end G1
section SS
variable {Γ : Type} [Group Γ] {a : ℕ}
variable {K L : Type} [Field K] [Field L] [Algebra K L]
end SS
section Cont
end Cont
section Main
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end Main
section C42
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
namespace At
end At
end C42
section Del
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end Del
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Quad
end Quad
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Cont
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Cont
section G5b
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
end G5b
section Maschke
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end Maschke
section G5a
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
theorem splitI_of_monodromyInertiaType_of_lgCatN (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A) (w : PlE H)
    (hSQ : w ∈ N.S i ∨ w ∈ N.Q i)
    (hcond : w ∈ N.Q i ∨ (At.Del N i ∧
      (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde'))))
    (hL : _root_.UpperTheory.GalS.LGCatN N r A w) (x : N.X i) : SplitI N r w x :=
  _root_.UpperTheory.GalS.SplitI_of_TY N r A hr w (N.SQ_l i w hSQ) hL (fun P => hTY.1 i P w hSQ hcond) x
end G5a
section H0
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
end H0
section Lin
end Lin
section Z
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
end Z
namespace At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
def SufficientGaloisClauseAlt (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    _root_.UpperTheory.GalS.LGCatN N r A w ∧
    (w ∈ N.S i → (∃ rb, IsRhoBar N i rb) ∧ ∀ rb, IsRhoBar N i rb →
      ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) ∧
      ∀ e : ℤ, HOneTwoZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))
theorem galois_clause_of_sufficient_alt (hC : Cheb N) (hT : TieGal N A) (hTY : MonodromyInertiaType N A) (i : N.Loc) (hDel : Del N i)
    (h : _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt N A i) : ConclusionG5 N A i := by
  rw [galois_clause_iff_reduced N A i hDel]
  intro hg r hr w hw hl
  obtain ⟨hL, hS⟩ := h hg r hr w hw
  refine ⟨fun hq x => _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN N r A hr hTY w hw ?_ hL x, fun hgk hS' => ?_,
    fun hS' rb hrb e => ?_⟩
  · rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr ⟨hDel, hq⟩
  · obtain ⟨⟨rb, hrb⟩, hall⟩ := hS hS'
    exact _root_.UpperTheory.GalS.exists_inertia_charpoly_factor_of_tame_type N r A hC hr hT hTY w hS' hgk hL rb hrb (hall rb hrb).1
  · exact (HStarZero_iff N rb w hl ((hS hS').2 rb hrb).1 e).2 (((hS hS').2 rb hrb).2 e)
end At
def SufficientGaloisClauseAlt (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt D.nd D.naut i
theorem galois_clause_of_sufficient_alt (D : D7) (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (ho : _root_.Formalism.MainNotions.SumRepresentations.SufficientGaloisClauseAlt D) : ConclusionG5 D := fun i =>
  _root_.Formalism.MainNotions.SumRepresentations.At.galois_clause_of_sufficient_alt D.nd D.naut h.2.2.2.2.2.2.2.2.1 h.1.2.2 h.2.2.2.2.2.1 i (Del_holds D i) (ho i)
end Formalism.MainNotions.SumRepresentations
end
end
