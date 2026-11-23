import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMemAsp

noncomputable section

open Module Matrix
open Formalism.MainNotions.S Formalism.BasicNotions

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem sub_mem_X_of_mem_Asp_of_hT_orth {F : FlagG S r T} {F' : FlagG S r T'} (hG : Gflag F F' ≠ 0) (hT : T ≠ 0)
    (hTs : star T = T) (σ : S.V →ₗ[E] S.V) (hσf : ∀ x ∈ F.X, σ x - x ∈ F.X) (hσz : σ F.z - F.z ∈ F.X)
    (hσω : σ (omp F F') - omp F F' ∈ F.X) {a : S.V} (ha : a ∈ Asp F F')
    (hX : ∀ x ∈ F.X, S.hT x a = 0) : σ a - a ∈ F.X := by
  classical
  have hz : F.z ∈ Asp F F' := by
    simpa [FlagG.fvec, Fin.snoc_last] using fvec_mem_Asp F F' (Fin.last r)
  have hom : omp F F' ∈ Asp F F' := by
    unfold omp
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (fvec'_mem_Asp F F' b)
  have homX : ∀ x ∈ F.X, S.hT x (omp F F') = 0 := by
    intro x hx
    have hle : F.X ≤ LinearMap.ker (S.hT.flip (omp F F')) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      simpa [brS] using brS_omp_e F F' i
    simpa using hle hx
  have hzX : ∀ x ∈ F.X, S.hT x F.z = 0 := by
    intro x hx
    have h := brS_swap (S := S) x F.z
    simp only [brS] at h
    rw [h, hT_z_X F hx, star_zero]
  have hzz : S.hT F.z F.z = -T := F.z_norm
  have hzo : S.hT F.z (omp F F') = Dl F F' (r + 1) := by simpa [brS] using pairing_omegaPrime_z F F'
  have hoz : S.hT (omp F F') F.z = star (Dl F F' (r + 1)) := by
    have h := brS_swap (S := S) (omp F F') F.z
    simp only [brS] at h
    rw [h, hzo]
  have hoo : S.hT (omp F F') (omp F F') = -T' * (Dl F F' r * star (Dl F F' r)) := by
    simpa [brS] using brS_omp_omp F F'
  obtain ⟨y0, hy0⟩ : ∃ y0 : S.V, y0 = T • omp F F' + Dl F F' (r + 1) • F.z := ⟨_, rfl⟩
  have hy0A : y0 ∈ Asp F F' := by
    rw [hy0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hom) (Submodule.smul_mem _ _ hz)
  have hXy0 : ∀ x ∈ F.X, S.hT x y0 = 0 := by
    intro x hx
    rw [hy0]
    simp [homX x hx, hzX x hx]
  have hzy0 : S.hT F.z y0 = 0 := by
    rw [hy0]
    simp only [map_add, map_smul, smul_eq_mul, hzo, hzz]
    ring
  have hy0z : S.hT y0 F.z = 0 := by
    rw [hy0]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hoz, hzz, hTs]
    ring
  have hy0o : S.hT y0 (omp F F') = T * (-T' * (Dl F F' r * star (Dl F F' r))) + star (Dl F F' (r + 1)) * Dl F F' (r + 1) := by
    rw [hy0]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hoo, hzo, hTs]
  have hy0y0 : S.hT y0 y0 = T * Gflag F F' := by
    have e : S.hT y0 y0 = T * S.hT y0 (omp F F') + Dl F F' (r + 1) * S.hT y0 F.z := by
      conv_lhs => rw [show S.hT y0 y0 = S.hT y0 (T • omp F F' + Dl F F' (r + 1) • F.z) by rw [← hy0]]
      simp only [map_add, map_smul, smul_eq_mul]
    rw [e, hy0o, hy0z]
    simp only [Gflag]
    ring
  have hy0ne : S.hT y0 y0 ≠ 0 := by
    rw [hy0y0]
    exact mul_ne_zero hT hG
  have horth : ∀ u : S.V, (∀ x ∈ F.X, S.hT x u = 0) → S.hT F.z u = 0 → u ∈ Asp F F' →
      u ∈ Qsp F (Hsp F F') := by
    intro u h1 h2 h3
    have hle : F.X ⊔ E ∙ F.z ⊔ Hsp F F' ≤ LinearMap.ker (S.hT.flip u) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        simpa using h1 x hx
      · rw [Submodule.span_singleton_le_iff_mem]
        simpa using h2
      · intro x hx
        simpa using hT_H_A h3 hx
    simp only [Qsp, Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    simpa using hle hx
  obtain ⟨v, hv⟩ : ∃ v : S.V, v = a - (-(S.hT F.z a) / T) • F.z - (S.hT y0 a / (T * Gflag F F')) • y0 :=
    ⟨_, rfl⟩
  have hvA : v ∈ Asp F F' := by
    rw [hv]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hz))
      (Submodule.smul_mem _ _ hy0A)
  have hvXo : ∀ x ∈ F.X, S.hT x v = 0 := by
    intro x hx
    rw [hv]
    simp [hX x hx, hzX x hx, hXy0 x hx]
  have hzv : S.hT F.z v = 0 := by
    rw [hv]
    simp only [map_sub, map_smul, smul_eq_mul, hzz, hzy0]
    field_simp
    ring
  have hy0v : S.hT y0 v = 0 := by
    rw [hv]
    simp only [map_sub, map_smul, smul_eq_mul, hy0z, hy0y0]
    field_simp
    ring
  have hy0Q : y0 ∈ Qsp F (Hsp F F') := horth y0 hXy0 hzy0 hy0A
  have hvQ : v ∈ Qsp F (Hsp F F') := horth v hvXo hzv hvA
  have hvX : v ∈ F.X := line F hT (Hsp F F') (fun x hx h hh => hT_A_H (X_le_Asp F F' hx) hh)
      (fun h hh => hT_A_H hz hh)
      (fun x hx hxH => by
        have hm : x ∈ Asp F F' ⊓ Hsp F F' := ⟨X_le_Asp F F' hx, hxH⟩
        rwa [Asp_inf_Hsp F F' hG, Submodule.mem_bot] at hm)
      (by have := finrank_Hsp F F' hG; omega)
      hy0Q (by simpa [brS] using hy0ne) hvQ (by simpa [brS] using hy0v)
  have hW : ∀ u, u ∈ F.X.comap (σ - LinearMap.id) ↔ σ u - u ∈ F.X := fun u => by simp
  have hy0W : σ y0 - y0 ∈ F.X := by
    have e : σ y0 - y0 = T • (σ (omp F F') - omp F F') + Dl F F' (r + 1) • (σ F.z - F.z) := by
      rw [hy0]
      simp only [map_add, map_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hσω) (Submodule.smul_mem _ _ hσz)
  have hav : a = v + (-(S.hT F.z a) / T) • F.z + (S.hT y0 a / (T * Gflag F F')) • y0 := by
    rw [hv]
    abel
  rw [← hW, hav]
  exact Submodule.add_mem _ (Submodule.add_mem _ ((hW v).2 (hσf v hvX))
    (Submodule.smul_mem _ _ ((hW _).2 hσz))) (Submodule.smul_mem _ _ ((hW _).2 hy0W))

theorem tau_exists (F : FlagG S r T) (F1 : FlagG S r T') (hG : Gflag F F1 ≠ 0) (hT : T ≠ 0) (hTs : star T = T)
    (hT' : T' ≠ 0) (hTs' : star T' = T') (σ ς : S.V ≃ₗ[E] S.V) (hσi : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ x ∈ F.X, σ x - x ∈ F.X) (hσX : ∀ x ∈ F.X, σ.symm x ∈ F.X) (hσz : σ F.z - F.z ∈ F.X)
    (hςf : ∀ x ∈ F1.X, ς x - x ∈ F1.X) (hςz : ς F1.z - F1.z ∈ F1.X)
    (hσω : σ (omp F F1) - omp F F1 ∈ F.X) (hςω : ς (omp F1 F) - omp F1 F ∈ F1.X)
    (h3 : ∀ w ∈ Hsp F F1, ∃ w0 ∈ Hsp F F1, σ w - w0 ∈ F.X ∧ ς w - w0 ∈ F1.X) :
    ∃ τ : S.V ≃ₗ[E] S.V, τ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a ∈ Asp F F1, τ a = a) ∧
      (∀ y ∈ Lat.orth S F.X, τ y - σ y ∈ F.X) ∧ (∀ y ∈ Lat.orth S F1.X, τ y - ς y ∈ F1.X) := by
  classical
  have hc := isCompl_AH F F1 hG
  have hσ : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσi
  choose p hpH hpσ hpς using fun w : Hsp F F1 => h3 w.1 w.2
  have huniq : ∀ (w : Hsp F F1) (u : S.V), u ∈ Hsp F F1 → σ w - u ∈ F.X → p w = u := by
    intro w u hu hσu
    have hd : p w - u ∈ Asp F F1 ⊓ Hsp F F1 := by
      refine ⟨X_le_Asp F F1 ?_, Submodule.sub_mem _ (hpH w) hu⟩
      have h := Submodule.sub_mem _ hσu (hpσ w)
      rwa [sub_sub_sub_cancel_left] at h
    rw [Asp_inf_Hsp F F1 hG, Submodule.mem_bot] at hd
    exact sub_eq_zero.mp hd
  let Pl : Hsp F F1 →ₗ[E] S.V :=
    { toFun := p
      map_add' := fun w1 w2 => huniq (w1 + w2) (p w1 + p w2) (Submodule.add_mem _ (hpH w1) (hpH w2)) (by
        have h := Submodule.add_mem _ (hpσ w1) (hpσ w2)
        rw [Submodule.coe_add, map_add]
        convert h using 1
        abel)
      map_smul' := fun c w => huniq (c • w) (c • p w) (Submodule.smul_mem _ c (hpH w)) (by
        have h := Submodule.smul_mem _ c (hpσ w)
        rw [Submodule.coe_smul, map_smul]
        convert h using 1
        rw [smul_sub]) }
  have hp0 : p 0 = 0 := map_zero Pl
  let τl : S.V →ₗ[E] S.V := (Asp F F1).subtype ∘ₗ (Asp F F1).projectionOnto (Hsp F F1) hc +
    Pl ∘ₗ (Hsp F F1).projectionOnto (Asp F F1) hc.symm
  have hsplit : ∀ y, ∃ a ∈ Asp F F1, ∃ w : Hsp F F1, y = a + w ∧ τl y = a + p w := fun y =>
    ⟨_, Submodule.projection_apply_mem hc y, (Hsp F F1).projectionOnto (Asp F F1) hc.symm y,
      (Submodule.projection_add_projection_eq_self hc y).symm, rfl⟩
  have hσXH : ∀ x ∈ F.X, ∀ w : Hsp F F1, S.hT (σ w) x = 0 ∧ S.hT x (σ w) = 0 := by
    intro x hx w
    have hx' : σ.symm x ∈ Asp F F1 := X_le_Asp F F1 (hσX x hx)
    have e : x = σ (σ.symm x) := (σ.apply_symm_apply x).symm
    constructor
    · rw [e, hσ]
      exact hT_H_A hx' w.2
    · rw [e, hσ]
      exact hT_A_H hx' w.2
  have hpp : ∀ w w' : Hsp F F1, S.hT (p w) (p w') = S.hT (w : S.V) w' := by
    intro w w'
    obtain ⟨x, hx, hxe⟩ : ∃ x ∈ F.X, p w = σ w - x := ⟨σ w - p w, hpσ w, by abel⟩
    obtain ⟨x', hx', hxe'⟩ : ∃ x' ∈ F.X, p w' = σ w' - x' := ⟨σ w' - p w', hpσ w', by abel⟩
    rw [hxe, hxe']
    simp only [map_sub, LinearMap.sub_apply, hσ, (hσXH x hx w').2, (hσXH x' hx' w).1,
      hT_X_X F hx hx', sub_zero]
  have hiso : ∀ x y, S.hT (τl x) (τl y) = S.hT x y := by
    intro x y
    obtain ⟨a, ha, w, hx, hτx⟩ := hsplit x
    obtain ⟨a', ha', w', hy, hτy⟩ := hsplit y
    rw [hτx, hτy, hx, hy]
    simp only [map_add, LinearMap.add_apply, hT_A_H ha (hpH w'), hT_H_A ha' (hpH w),
      hT_A_H ha w'.2, hT_H_A ha' w.2, hpp, add_zero, zero_add]
  have hinj : Function.Injective τl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine S.nondeg.1 x fun y => ?_
    rw [← hiso x y, hx, map_zero, LinearMap.zero_apply]
  refine ⟨LinearEquiv.ofInjectiveEndo τl hinj, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, S.hT (LinearEquiv.ofInjectiveEndo τl hinj x) (LinearEquiv.ofInjectiveEndo τl hinj y) =
      S.hT x y
    intro x y
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    exact hiso x y
  · intro a ha
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a', ha', w, hs, hτa⟩ := hsplit a
    have hw0 : (w : S.V) = 0 := by
      have hwA : (w : S.V) ∈ Asp F F1 := by
        have e : (w : S.V) = a - a' := by rw [hs]; abel
        rw [e]
        exact Submodule.sub_mem _ ha ha'
      have hm : (w : S.V) ∈ Asp F F1 ⊓ Hsp F F1 := ⟨hwA, w.2⟩
      rwa [Asp_inf_Hsp F F1 hG, Submodule.mem_bot] at hm
    have hw : w = 0 := Subtype.ext hw0
    rw [hτa, hw, hp0, add_zero]
    rw [hs, hw0, add_zero]
  · intro y hy
    have hyo : ∀ x ∈ F.X, S.hT x y = 0 := by
      simpa [Lat.orth, Submodule.mem_iInf] using hy
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a, ha, w, hs, hτy⟩ := hsplit y
    have hX : ∀ x ∈ F.X, S.hT x a = 0 := by
      intro x hx
      have e : a = y - w := by rw [hs]; abel
      rw [e, map_sub, hyo x hx, hT_A_H (X_le_Asp F F1 hx) w.2, sub_zero]
    have key := sub_mem_X_of_mem_Asp_of_hT_orth hG hT hTs σ.toLinearMap hσf hσz hσω ha hX
    rw [hτy, hs, map_add]
    have e : a + p w - (σ a + σ w) = -(σ.toLinearMap a - a) - (σ w - p w) := by
      simp only [LinearEquiv.coe_coe]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ key) (hpσ w)
  · intro y hy
    have hyo : ∀ x ∈ F1.X, S.hT x y = 0 := by
      simpa [Lat.orth, Submodule.mem_iInf] using hy
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a, ha, w, hs, hτy⟩ := hsplit y
    have hX : ∀ x ∈ F1.X, S.hT x a = 0 := by
      intro x hx
      have hxA : x ∈ Asp F F1 := by
        rw [← Asp_symm F F1]
        exact X_le_Asp F1 F hx
      have e : a = y - w := by rw [hs]; abel
      rw [e, map_sub, hyo x hx, hT_A_H hxA w.2, sub_zero]
    have hG' : Gflag F1 F ≠ 0 := by rw [Gflag_swap]; exact hG
    have ha' : a ∈ Asp F1 F := by rw [Asp_symm]; exact ha
    have key := sub_mem_X_of_mem_Asp_of_hT_orth hG' hT' hTs' ς.toLinearMap hςf hςz hςω ha' hX
    rw [hτy, hs, map_add]
    have e : a + p w - (ς a + ς w) = -(ς.toLinearMap a - a) - (ς w - p w) := by
      simp only [LinearEquiv.coe_coe]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ key) (hpς w)

end Formalism.L2.SG.NGCut.NormalVectorPairings
