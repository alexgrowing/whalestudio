import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplementStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTermsStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocComm

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrel d τ hτ
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hrel
  obtain ⟨hUW, -, -, -, hAut, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, -, -, hStab, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨hTC, -, -⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have key : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.IsTerm (c.dat d) (c.lat τ.abelian₂) := fun d τ h => (hTC d τ h).1
  have eA : ∀ Λ, P.UW0 ⊓ LocNG.Aut Λ =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat Λ)).comap c.grp.toMonoidHom := by
    intro Λ
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rw [hUW, hAut]
  have eS : ∀ d : LocNG.Datum P, LocNG.Datum.Stab d =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
    intro d
    ext g
    rw [Subgroup.mem_comap, hStab]
    rfl
  have rel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  have fixd : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂) ≤ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d) := by
    intro d τ h x hx
    obtain ⟨hx0, hxs⟩ := Subgroup.mem_inf.mp hx
    have ht := key d τ h
    have h1 := (GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms M.L r k S _ _ ht x hx0).1
    rw [MulAction.mem_stabilizer_iff.mp hxs] at h1
    have h2 := (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ ht).2.2.2.2.2.2.2 _ h1
    exact Subgroup.mem_inf.mpr ⟨hx0, MulAction.mem_stabilizer_iff.mpr h2⟩
  have volH := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement M.L r k S
  have cLam : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂)) := by
    intro d τ h
    have := volH.1 _ (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ (key d τ h)).1.1
    exact ⟨this.1, this.2.1⟩
  have cDat : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
    intro d τ h
    exact volH.2 _ _ (key d τ h)
  refine ⟨?_, ?_, ?_⟩
  · rw [eA, eS]
    exact Subgroup.comap_mono (fixd d τ hτ)
  · rw [eA, eS, rel]
    exact ((cLam d τ hτ).symm.trans (cDat d τ hτ)).1
  · intro d' τ' hτ'
    rw [eS, eS, rel]
    exact ((cDat d τ hτ).symm.trans (cDat d' τ' hτ')).1

end GlobalTheory.HL.LocComm
