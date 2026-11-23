import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.ChainHilb

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem hp_add_right (h : PeterssonHilbertSpace.IsHermPos C ip) (x y y' : C) : ip x ((y : N) + y') = ip x y + ip x y' := by
  rw [← Submodule.coe_add, ← h.herm (y + y') x, Submodule.coe_add, h.add y y' x, map_add, h.herm y x, h.herm y' x]

theorem hp_smul_right (h : PeterssonHilbertSpace.IsHermPos C ip) (s : ℂ) (x y : C) : ip x (s • (y : N)) = s * ip x y := by
  rw [← Submodule.coe_smul, ← h.herm (s • y) x, Submodule.coe_smul, h.smul s y x, map_mul, h.herm y x,
    Complex.conj_conj]

theorem hp_restrict (h : PeterssonHilbertSpace.IsHermPos C ip) {C' : Submodule ℂ N} (hle : C' ≤ C) : PeterssonHilbertSpace.IsHermPos C' ip := by
  haveI := h.fd
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_, ?_, ?_, ?_⟩
  · intro x x' y; exact h.add ⟨x, hle x.2⟩ ⟨x', hle x'.2⟩ ⟨y, hle y.2⟩
  · intro s x y; exact h.smul s ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x y; exact h.herm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x hx
    refine h.pos ⟨x, hle x.2⟩ ?_
    intro h0; apply hx; ext; simpa using congrArg Subtype.val h0

theorem hp_model (h : PeterssonHilbertSpace.IsHermPos C ip) : ∃ H : Hs, ∃ j : H.T →ₗ[ℂ] N,
    Function.Injective j ∧ LinearMap.range j = C ∧ ∀ x x', ⟪x, x'⟫_ℂ = ip (j x) (j x') := by
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y) := by
    intro x hx y hy z hz c
    refine ⟨?_, ?_⟩
    · have e1 := hp_add_right h ⟨x, hx⟩ ⟨y, hy⟩ ⟨c • z, C.smul_mem c hz⟩
      have e2 := hp_smul_right h c ⟨x, hx⟩ ⟨z, hz⟩
      exact e1.trans (congrArg (fun t => ip x y + t) e2)
    · exact (h.herm ⟨x, hx⟩ ⟨y, hy⟩).symm
  have h2 : ∀ x ∈ C, x ≠ 0 → 0 < (ip x x).re := fun x hx hne =>
    h.pos ⟨x, hx⟩ (fun h0 => hne (by simpa using congrArg Subtype.val h0))
  obtain ⟨M, hM⟩ := GlobalTheory.HilbertModel.exists_hmod N C ip h.fd h1 h2
  exact ⟨⟨M.H⟩, M.e, hM.1, hM.2.1, hM.2.2⟩

theorem hp_riesz {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (h : PeterssonHilbertSpace.IsHermPos C ip) (j : H →ₗ[ℂ] N) (hj : ∀ x, j x ∈ C) :
    ∃ r : C →ₗ[ℂ] H, ∀ x (w : C), ⟪x, r w⟫_ℂ = ip (j x) w := by
  have key : ∀ w : C, ∃ y : H, ∀ x, ⟪x, y⟫_ℂ = ip (j x) w := by
    intro w
    let φ : H →ₗ[ℂ] ℂ :=
      { toFun := fun x => ip w (j x)
        map_add' := fun a b => by
          have := hp_add_right h w ⟨j a, hj a⟩ ⟨j b, hj b⟩
          simpa [map_add] using this
        map_smul' := fun s a => by
          have := hp_smul_right h s w ⟨j a, hj a⟩
          simpa [map_smul] using this }
    refine ⟨(InnerProductSpace.toDual ℂ H).symm (LinearMap.toContinuousLinearMap φ), fun x => ?_⟩
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    exact h.herm w ⟨j x, hj x⟩
  choose y hy using key
  refine ⟨⟨⟨y, fun a b => ext_inner_left ℂ fun x => ?_⟩, fun s a => ext_inner_left ℂ fun x => ?_⟩, fun x w => hy w x⟩
  · rw [inner_add_right, hy, hy, hy, Submodule.coe_add]
    exact hp_add_right h ⟨j x, hj x⟩ a b
  · rw [RingHom.id_apply, inner_smul_right, hy, hy, Submodule.coe_smul]
    exact hp_smul_right h s ⟨j x, hj x⟩ a

end Gen

def heqv {A B : Hs} (h : A = B) : A.T ≃ₗᵢ[ℂ] B.T := by
  subst h; exact LinearIsometryEquiv.refl ℂ A.T

theorem heqv_heq {A B E : Hs} (e1 : A = E) (e2 : B = E) (v' : A.T) (v : B.T) (h : HEq v' v) :
    heqv e1 v' = heqv e2 v := by
  subst e1; subst e2; cases h; rfl

theorem heqv_self {A : Hs} (h : A = A) (x : A.T) : heqv h x = x := rfl

def chSel (m : ℕ) (A B : Hs) (L : ℕ → Hs) (j : ℕ) : Hs := if j = 0 then A else if j = m then B else L j

theorem chSel_zero {m : ℕ} {A B : Hs} {L : ℕ → Hs} : chSel m A B L 0 = A := if_pos rfl

theorem chSel_top {m : ℕ} {A B : Hs} {L : ℕ → Hs} (hm : m ≠ 0) : chSel m A B L m = B := by
  rw [chSel, if_neg hm, if_pos rfl]

theorem chSel_mid {m j : ℕ} {A B : Hs} {L : ℕ → Hs} (h1 : j ≠ 0) (h2 : j ≠ m) : chSel m A B L j = L j := by
  rw [chSel, if_neg h1, if_neg h2]

end GlobalTheory.ChainHilb

namespace GlobalTheory.ChainHilb

theorem exists_chainHilb : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  classical
  intro D C b U Top jX hm hE hle hE0 hX
  obtain ⟨EE, jE, hEi, hEr, hEip⟩ := hp_model hE
  have jE_mem : ∀ μ x, jE x ∈ C.CC b μ 0 := fun μ x =>
    (hle μ).1 (by rw [← hEr]; exact LinearMap.mem_range_self jE x)
  have hLo : ∀ (μ : D.what₂.Tup) (j : ℕ), ∃ H : Hs, ∃ jj : H.T →ₗ[ℂ] C.Amb j, j ≤ D.R.m - 1 →
      Function.Injective jj ∧ LinearMap.range jj = C.CCP b μ j ∧
        ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jj x) (jj x') := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨h1, h2⟩ := (hle μ).2.2.2 j hj
      obtain ⟨H, jj, a1, a2, a3⟩ := hp_model (hp_restrict h2 h1)
      exact ⟨H, jj, fun _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨EE, 0, fun h => absurd h hj⟩
  choose Lo jL hL using hLo
  let Mult : D.what₂.Tup → ℕ → Hs := fun μ => chSel D.R.m EE (Top μ) (Lo μ)
  let jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m - 1 then
      (jL μ j).comp (heqv (chSel_mid (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)
        (by have := h.1; omega) (by have := h.2; omega))).toLinearEquiv.toLinearMap
    else 0
  have jM_mem : ∀ μ j x, jM μ j x ∈ C.CC b μ j := by
    intro μ j x
    dsimp only [jM]
    split_ifs with h
    · rw [LinearMap.comp_apply]
      refine ((hle μ).2.2.2 j h.2).1 ?_
      rw [← (hL μ j h.2).2.1]
      exact LinearMap.mem_range_self _ _
    · rw [LinearMap.zero_apply]; exact zero_mem _
  have hr0 : ∀ μ, ∃ r : C.CC b μ 0 →ₗ[ℂ] EE.T, ∀ x (w : C.CC b μ 0), ⟪x, r w⟫_ℂ = C.ipE b (jE x) w :=
    fun μ => hp_riesz (hE0 μ) jE (jE_mem μ)
  choose r0 hr0 using hr0
  have hR : ∀ μ j, ∃ r : C.CC b μ j →ₗ[ℂ] (Mult μ j).T, j ≤ D.R.m - 1 →
      ∀ x (w : C.CC b μ j), ⟪x, r w⟫_ℂ = C.ipP b μ j (jM μ j x) w := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨r, hr⟩ := hp_riesz ((hle μ).2.2.2 j hj).2 (jM μ j) (jM_mem μ j)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose R hR using hR
  have memX : ∀ μ, U μ → ∀ y, jX μ y ∈ C.CCX b μ := fun μ hU y =>
    (hle μ).2.1 (by rw [← (hX μ hU).2.1]; exact LinearMap.mem_range_self (jX μ) y)
  let io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T := fun μ j =>
    if hU : U μ then
      if h0 : j = 0 then
        (heqv (show Mult μ j = EE by rw [h0]; exact chSel_zero)).symm.toLinearEquiv.toLinearMap ∘ₗ r0 μ ∘ₗ
          C.ioC b μ 0 ∘ₗ (jM μ 1 ∘ₗ (heqv (show Mult μ (j + 1) = Mult μ 1 by rw [h0])).toLinearEquiv.toLinearMap).codRestrict
            (C.CC b μ 1) (fun y => jM_mem μ 1 _)
      else if hT : j + 1 = D.R.m then
        (heqv (show Mult μ (D.R.m - 1) = Mult μ j by rw [show D.R.m - 1 = j by omega])).toLinearEquiv.toLinearMap ∘ₗ
          R μ (D.R.m - 1) ∘ₗ C.ioX b μ ∘ₗ
          (jX μ ∘ₗ (heqv (show Mult μ (j + 1) = Top μ by rw [hT]; exact chSel_top (by omega))).toLinearEquiv.toLinearMap).codRestrict
            (C.CCX b μ) (fun y => memX μ hU _)
      else
        R μ j ∘ₗ C.ioC b μ j ∘ₗ (jM μ (j + 1)).codRestrict (C.CC b μ (j + 1)) (jM_mem μ (j + 1))
    else 0
  refine ⟨EE, Mult, fun μ => heqv (chSel_zero (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)),
    fun μ => heqv (chSel_top (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ) (by omega)), io, jE, jM,
    hEi, hEr, hEip, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ j h1 h2
    have hh : 1 ≤ j ∧ j ≤ D.R.m - 1 := ⟨h1, h2⟩
    obtain ⟨hi, hr, hip⟩ := hL μ j h2
    dsimp only [jM]
    rw [dif_pos hh]
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.coe_comp]; exact hi.comp (LinearEquiv.injective _)
    · rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), hr]
    · intro x x'
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hip]
      exact (LinearIsometryEquiv.inner_map_map _ x x').symm
  · intro μ hU x v h
    dsimp only [io]
    rw [dif_pos hU, dif_pos rfl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    exact hr0 μ x _
  · intro μ hU j h1 h2 x v h
    dsimp only [io]
    rw [dif_pos hU, dif_neg (by omega), dif_neg (by omega)]
    rw [LinearMap.comp_apply, hR μ j (by omega)]
    rfl
  · intro μ hU x v v' hv h
    dsimp only [io]
    rw [dif_pos hU, dif_neg (by omega), dif_pos (by omega)]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [heqv_self, hR μ _ le_rfl]
    refine congrArg (fun y => C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x)
      ((C.ioX b μ y : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1))) (Subtype.ext ?_)
    exact congrArg (jX μ) (heqv_heq _ _ v' v hv)
  · intro μ hU j
    dsimp only [io]
    rw [dif_neg hU]

end GlobalTheory.ChainHilb
