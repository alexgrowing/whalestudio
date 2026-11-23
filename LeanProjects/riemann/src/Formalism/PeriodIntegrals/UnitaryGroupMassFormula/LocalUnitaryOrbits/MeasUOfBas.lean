import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem lamT_open (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) (hG : GoodY σ J ψ v Λ a Y) :
    IsOpen (LamT v Λ a) := by
  obtain ⟨b, hb, hmem⟩ := hB hG
  have hCM := hG.1.1
  have hfr : Module.finrank F E = 2 := hCM.2.2.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hV : Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_baseChange, hfr, mul_comm]
  have : FiniteDimensional (Fv F v) (Fin n → Fv F v ⊗[F] E) := inferInstance
  let bb := basisOfLinearIndependentOfCardEqFinrank' b hb (by rw [Fintype.card_fin, hV])
  have hbb : ∀ i, bb i = b i := fun i => by simp [bb]
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      bb.equivFun.symm '' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      refine ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
    · rintro ⟨c, hc, rfl⟩
      refine (hmem _).2 ⟨fun i => ⟨c i, hc i (Set.mem_univ i)⟩, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
  have hc : Continuous bb.equivFun := IsModuleTopology.continuous_of_linearMap bb.equivFun.toLinearMap
  have hL : IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [e, LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  have : LamT v Λ a = Set.univ.pi (fun _ => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => hL

theorem measU_of_bas (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) :
    MeasU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := lamT_open σ J ψ v Λ a Y hB hG
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem countU_of_bas' (a : ℕ) (Y : TupV (E := E) v n a)
    (hB : LatBasO σ J ψ v Λ a Y) (hQ : ResIdx v) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of σ J ψ v Λ a Y (measU_of_bas σ J ψ v Λ a Y hB)
    (idxU_of σ J ψ v Λ a Y (idxV_of σ J ψ v Λ a Y hB hQ)) (clsU_of σ J ψ v Λ a Y hR)

end PI.OmLocU
