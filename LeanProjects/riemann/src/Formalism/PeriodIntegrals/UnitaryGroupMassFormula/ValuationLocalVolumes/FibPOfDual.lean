import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimIndep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimDual (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∃ W ∈ LamT v Λ a, ∀ i j,
      hR (Fv F v) σ J (y i) (W j) = (if i = j then 1 else 0) ∧
        hR (Fv F v) σ J (W j) (y i) = (if i = j then 1 else 0)

def HensOntoP (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∀ S : HermR (Fv F v) σ a, S ∈ hermOE σ v a →
      ∃ W0 ∈ LamT v Λ a, crossM σ J y W0 = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))

theorem henselSurjective_of_primitiveDual (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : HensOntoP σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy S hS'
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL y hy
  obtain ⟨L, -, hLΛ⟩ := hL
  have hTr : TrOnto σ v := PI.OmLocU.Red.trOnto_holds σ J ψ v hS
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hUn _ (hS' i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS' i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  subst hLΛ
  refine ⟨fun j => ∑ k, A k j • W k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hA k j) (hW k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, A k j * hR (Fv F v) σ J (y i) (W k) = A i j := by
      simp only [fun k => (hd i k).1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e2 : ∑ k, sigR (Fv F v) σ (A k i) * hR (Fv F v) σ J (W k) (y j) = sigR (Fv F v) σ (A j i) := by
      simp only [fun k => (hd j k).2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e1, e2, hAS]

theorem fiberHensel_of_henselOnto (a : ℕ) (Y : TupV (E := E) v n a) (h : HensOntoP σ J ψ v Λ a) :
    FibHensP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ hσ hJ y hy hyT
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  refine ⟨dH σ J v hσ hJ y, fun k => ?_, fun k Z hZ W hW => ?_⟩
  · ext S
    constructor
    · rintro ⟨W, hW, rfl⟩
      obtain ⟨W0, hW0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hW
      rw [mem_hN σ v ϖ h0]
      intro i j
      refine ⟨crossM σ J y W0 i j, ?_, ?_⟩
      · exact oEv_add v (hR_mem_oEv σ J v Λ hSD (hy.1 i) (hW0 j)) (hR_mem_oEv σ J v Λ hSD (hW0 i) (hy.1 j))
      · rw [coe_dH, crossM_smul_right]
    · intro hS
      obtain ⟨S0, hS0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hS
      obtain ⟨W0, hW0, hc⟩ := h hG.1 hSD hG.2.2.2.1 hG.2.1 y hy S0 hS0
      refine AddSubgroup.mem_map.2 ⟨ϖ ^ (k + 1) • W0, (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨W0, hW0, rfl⟩, ?_⟩
      apply Subtype.ext
      funext i j
      rw [coe_dH, crossM_smul_right, hc, PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, smul_eq_sc]
  · apply rem_mem σ J v Λ hSD ϖ h0 hint hZ hW
    show gramR (Fv F v) σ J (y + Z + W) - gramR (Fv F v) σ J (y + Z) -
      (gramR (Fv F v) σ J (y + W) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W) = _
    exact gram_rem σ J y Z W

theorem fibP_of_dual (a : ℕ) (Y : TupV (E := E) v n a) (hC : PrimCos σ J ψ v Λ a) (hD : PrimDual σ J ψ v Λ a) :
    FibP σ J ψ v Λ a Y :=
  fibP_of σ J ψ v Λ a Y hC (fiberHensel_of_henselOnto σ J ψ v Λ a Y (henselSurjective_of_primitiveDual σ J ψ v Λ a hD))

end PI.OmVd
