import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceConj

theorem conj_lat : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  intro D j B hB hlam Φ κ hκ0 hval hκ τ hτ ψ ψ' hψ hψ' hcc hf
  have huq := GlobalTheory.CoefLatConj.existsUnique_eq Φ hB hlam hκ0 hval hκ
  have hinj : Function.Injective Φ := fun x y hxy => (huq (Φ x) (hval x)).unique rfl hxy
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hinj)
  have hπx : ∀ x, π (Φ x) = x := fun x => LinearMap.congr_fun hπ x
  have hπv : ∀ P ∈ B.valSpace, Φ (π P) = P := fun P hP => by
    obtain ⟨x, rfl, -⟩ := huq P hP
    rw [hπx]
  let C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j :=
    { toFun := fun F h => Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)))
      map_add' := fun F G => by
        funext h
        simp only [Pi.add_apply, map_add, smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Pi.smul_apply, map_smul, map_smulₛₗ, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hC : ∀ F h, C F h = Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h))) := fun _ _ => rfl
  have hconjAt : ∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) := fun F hF h =>
    ⟨π (F h), GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)), rfl, (hπv _ (hF h)).symm, hC F h⟩
  refine ⟨C, fun F hF => ⟨hconjAt F hF, fun h0 => ?_⟩, fun O hO => ?_⟩
  · funext h
    have e := congrFun h0 h
    rw [hC, Pi.zero_apply, ← map_zero Φ] at e
    have e1 := hinj e
    have hc : τ κ / κ ≠ 0 := div_ne_zero ((map_ne_zero _).2 hκ0) hκ0
    rw [smul_eq_zero] at e1
    have e2 : π (F h) = 0 := by
      rcases e1 with e1 | e1
      · exact absurd e1 hc
      · have := congrArg (GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j)) e1
        rwa [GlobalTheory.CoefLatConj.mapVV_symm_mapVV, map_zero] at this
    rw [Pi.zero_apply, ← hπv _ (hF h), e2, map_zero]
  · have hτ' : ∀ a, τ.symm (embLL0 D a) = embLL0 D a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hO' : IsCoefRing (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) :=
      ⟨hO.emb, fun a => Subring.mem_map.2 ⟨_, hO.int a, hτ _⟩⟩
    have hOO : (O.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = O := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    ext F'
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hFv : ∀ h, F h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF).1).1
      exact GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) O hO τ hτ ψ ψ' hψ hψ' hcc hf
        F (C F) (hconjAt F hFv) hF
    · intro hF'
      have hF'v : ∀ h, F' h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF').1).1
      let F : Amb D j := fun h => Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))
      have hFm : F ∈ B.mtLat (embLL0 D) (labLL0 D) O ψ := by
        have key := GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) hO'
          τ.symm hτ' ψ' ψ hψ' hψ hcc.symm hf.symm F' F
          (fun h => ⟨π (F' h), GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)), rfl, (hπv _ (hF'v h)).symm, rfl⟩) hF'
        rwa [hOO] at key
      refine ⟨F, hFm, funext fun h => ?_⟩
      rw [hC]
      change Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j)
        (π (Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))))) = F' h
      rw [hπx, map_smulₛₗ (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j))]
      have e3 := GlobalTheory.CoefLatConj.mapVV_symm_mapVV (lamV D j) τ.symm (π (F' h))
      rw [RingEquiv.symm_symm] at e3
      rw [e3, smul_smul]
      have : τ κ / κ * (τ (τ.symm κ / κ)) = 1 := by
        rw [map_div₀, RingEquiv.apply_symm_apply]
        have : τ κ ≠ 0 := (map_ne_zero _).2 hκ0
        field_simp
      rw [RingHom.coe_coe, this, one_smul, hπv _ (hF'v h)]

end GlobalTheory.PlaceConj

end
