import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.FinTensor

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose r hr using fun τ =>
    LinearMap.exists_leftInverse_of_injective (Submodule.inclusion (h τ))
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective (h τ)))
  have key : PiTensorProduct.map r ∘ₗ inclK h = LinearMap.id := by
    unfold inclK
    rw [← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id]
  intro x y hxy
  calc x = (PiTensorProduct.map r ∘ₗ inclK h) x := by rw [key, LinearMap.id_apply]
    _ = (PiTensorProduct.map r ∘ₗ inclK h) y := by rw [LinearMap.comp_apply, hxy, ← LinearMap.comp_apply]
    _ = y := by rw [key, LinearMap.id_apply]

theorem incl_tprod (h : KSm M) (v : ∀ ρ, kFin M ρ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  simp [inclT, inclK]

theorem incl_tprod_update (h : KSm M) (v : ∀ ρ, kFin M ρ) (τ : D.what₂.Tau) (u : kFin M τ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ (Function.update v τ u))) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (u : M.H τ)) := by
  rw [incl_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem act_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  simp only [actT, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem ell_update (w v : ∀ ρ, M.H ρ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  have hs : ∀ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = ⟪w ρ, v ρ⟫_ℂ := fun ρ hρ => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  simp only [ellT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  show ∏ ρ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl hs

private theorem hasDerivAt_ellT_actT_exp_tprod (h : KSm M) (τ : D.what₂.Tau)
    (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) (ha : IsKAct M τ a)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (w : ∀ ρ, M.H ρ) (v : ∀ ρ, kFin M ρ) :
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v)))))
      (ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v))))) 0 := by
  have hd := ha.der X hX (v τ)
  have hi : HasDerivAt (fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ)
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ 0 := by
    have hc := ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using hc
  have e2 : ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v)))) =
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    rw [position_tprod, incl_tprod_update, ell_update]
  have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v))))) =
      fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    funext t
    rw [incl_tprod, act_tprod, ell_update]
  rw [e1, e2]
  exact hi.mul_const _

theorem derT_mapFactor (h : KSm M) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ))
    (ha : IsKAct M τ a) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (x : KT M) :
    DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x)) := by
  delta DerT
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, smul_eq_mul]
    exact (hasDerivAt_ellT_actT_exp_tprod h τ a ha X hX w v).const_mul r
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

theorem incl_mapFactor_kOp (h : KSm M) (τ : D.what₂.Tau) (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ)
    (x : KT M) : inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    congr 1
    rw [position_tprod, incl_tprod_update, incl_tprod, act_tprod] <;> rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem kFinTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (h : KSm M), Function.Injective (inclK h) ∧ (∀ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a → ∀ X ∈ lieAt V τ, ∀ x : KT M, DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x))) ∧ ∀ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ) (x : KT M), inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  intro D V S M τ h
  refine ⟨inclK_injective h, ?_, ?_⟩
  · intro a ha X hX x
    exact derT_mapFactor h τ a ha X hX x
  · intro k hk x
    exact incl_mapFactor_kOp h τ k hk x

end GlobalTheory.Chain.IoLift.FinTensor

end
