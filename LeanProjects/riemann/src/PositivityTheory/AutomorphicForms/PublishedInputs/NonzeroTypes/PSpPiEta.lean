import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ.Grp

namespace P_spPiEta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem twD_hasDetVec {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : HasDetVec (τ a) (G.μ a)) : HasDetVec (G.twD τ a) (G.μ a) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  have h1 := detChar_of_mem_KO
    (isUnram_absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) hg
  rw [twD, twist_apply, h1, hv g hg, Units.val_one, one_smul]

theorem twD_isSmooth {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : IsSmooth (τ a)) : IsSmooth (G.twD τ a) :=
  isSmooth_twist h (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem jacU_eq_jac {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (m : Levi k fun a : Fin G.s => Fin (G.d a)) (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)))
    (y : Jacquet π (unipRad k G.e)) : jacU G.e π m y = jac G.e π m y := by
  rw [jac, twist_apply, MonoidHom.inv_apply, deltaHalf_of_mem_leviK hm, inv_one, Units.val_one, one_smul]

end P_spPiEta

theorem step_spPiEta {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SpecialRepresentationEtaProp := by
  unfold SpecialRepresentationEtaProp
  intro hLift Y _ _ τ hsm hdet
  obtain ⟨v, hv0, hv⟩ := step_tensorVec k G.s G.d Y (G.twD τ) G.μ
    (fun a => P_spPiEta.twD_hasDetVec G τ a (hdet a))
  have hsm' : IsSmooth (piTensor (G.twD τ)) :=
    isSmooth_piTensor fun a => P_spPiEta.twD_isSmooth G τ a (hsm a)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one G.e (piTensor (G.twD τ)) hsm' v
  let φ := Model.evalOne G.e (Representation.IntertwiningMap.id (multiProd G.e (G.twD τ)))
  have hφ : φ (Submodule.Quotient.mk f) = v := hf1
  let T : Subrepresentation (piTensor (G.twD τ)) := φ.range
  have hmem : ∀ x, φ x ∈ T.toSubmodule := fun x =>
    (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨x, rfl⟩
  let ψ : (jac G.e (multiProd G.e (G.twD τ))).IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule φ.toLinearMap hmem, fun g => LinearMap.ext fun x => Subtype.ext (φ.isIntertwining _ _ g x)⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hw
    exact ⟨x, rfl⟩
  have hsub : IsSubquotient T.toRepresentation (jac G.e (multiProd G.e (G.twD τ))) :=
    IsSubquotient.of_surjective ψ hψ
  have hη : G.HasEtaVec T.toRepresentation := by
    refine ⟨⟨v, hφ ▸ hmem _⟩, fun h => hv0 (congrArg Subtype.val h), fun m hm => ?_⟩
    apply Subtype.ext
    exact hv m fun a => hm a (Set.mem_univ a)
  obtain ⟨y, hy0, hy⟩ := hLift _ _ _ T.toRepresentation
    (isSmooth_jac G.e (isSmooth_parInd _ _)) hsub hη
  refine ⟨y, hy0, fun m hm => ?_⟩
  exact (P_spPiEta.jacU_eq_jac G _ m hm y).trans (hy m hm)

end UpperTheory.TNZ.Grp
