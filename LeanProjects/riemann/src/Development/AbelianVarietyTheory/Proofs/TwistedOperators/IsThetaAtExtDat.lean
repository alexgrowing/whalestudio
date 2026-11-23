import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ExtDatTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

theorem half_of_half {e e' : AE D} (h1 : e * e' = e') {x : Mx D m n} (hx : IsHalf e' x) : IsHalf e x := by
  intro i j
  rw [← hx i j, ← mul_assoc, h1]

theorem map_sub_half {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') {x : Mx D m n} (hx : IsHalf e' x) :
    x.map ((e - e') * ·) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [sub_mul, half_of_half h1 hx i j, hx i j, sub_self]

theorem map_half {e' : AE D} {x : Mx D m n} (hx : IsHalf e' x) : x.map (e' * ·) = x := by
  ext i j
  simp only [Matrix.map_apply]
  exact hx i j

theorem map_sub_eq {e e' : AE D} {u : Mx D m n} (hu : IsHalf e u) :
    u.map ((e - e') * ·) = u - u.map (e' * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, sub_mul, hu i j]

theorem half_add_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) : IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h' := h i j
    rw [Matrix.add_apply, mul_add, hx i j] at h'
    exact add_right_cancel h'
  · intro h i j
    rw [Matrix.add_apply, mul_add, h i j, hx i j]

theorem map_add_mul (a : AE D) (t x : Mx D m n) : (t + x).map (a * ·) = t.map (a * ·) + x.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, mul_add]

theorem mul_nsmul_comm' (a x : AE D) (k : ℕ) : a * (k • x) = k • (a * x) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]

theorem map_add_nsmul (a : AE D) (t u : Mx D m n) (k : ℕ) :
    (t + k • u).map (a * ·) = t.map (a * ·) + k • u.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, mul_add, mul_nsmul_comm']

theorem half_map_self {e' : AE D} (h2 : e' * e' = e') (t : Mx D m n) : IsHalf e' (t.map (e' * ·)) := by
  intro i j
  simp only [Matrix.map_apply]
  rw [← mul_assoc, h2]

def extL (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun φ := GlobalTheory.ChainCol.extDat e e' Λ φ
  map_add' φ φ' := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c φ := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extL_apply (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) :
    extL e e' Λ φ = GlobalTheory.ChainCol.extDat e e' Λ φ := rfl

open Classical in
theorem extDat_trans {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (Φ : Mx D m n → ℂ) {x : Mx D m n} (hx : IsHalf e' x) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => Φ (t + x)) = fun t => GlobalTheory.ChainCol.extDat e e' Λ Φ (t + x) := by
  funext t
  have hxe : IsHalf e x := half_of_half h1 hx
  simp only [GlobalTheory.ChainCol.extDat, half_add_iff hxe, map_add_mul, map_sub_half h1 h2 hx, add_zero, map_half hx]

theorem extDat_sb {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf e' Λ Φ) :
    IsSBHalf e Λ (GlobalTheory.ChainCol.extDat e e' Λ Φ) := by
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨-, k, hk, hper, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hn
    apply ht
    simp only [GlobalTheory.ChainCol.extDat]
    exact if_neg fun hc => hn hc.1
  · have hku : IsHalf e (k • u) := fun i j => by rw [Matrix.smul_apply, mul_nsmul_comm', hue i j]
    have hsu : u.map ((e - e') * ·) ∈ Λ := by
      rw [map_sub_eq hue]
      exact sub_mem hu (hstab u hu)
    have hmem : (t + k • u).map ((e - e') * ·) ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ := by
      rw [map_add_nsmul]
      exact add_mem_cancel_right (nsmul_mem hsu k)
    have hval : Φ ((t + k • u).map (e' * ·)) = Φ (t.map (e' * ·)) := by
      rw [map_add_nsmul]
      exact hper _ (hstab u hu) (half_map_self h2 u) _
    simp only [GlobalTheory.ChainCol.extDat, half_add_iff hku, hmem, hval]
  · have hc : IsHalf e t ∧ t.map ((e - e') * ·) ∈ Λ := by
      by_contra hn
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      exact if_neg hn
    have hΦt : Φ (t.map (e' * ·)) ≠ 0 := by
      intro h0
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      rw [if_pos hc, h0]
    have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq hc.1]
      abel
    rw [hsplit, nsmul_add]
    exact add_mem (hlat _ hΦt) (nsmul_mem hc.2 k)

theorem symplO_map_eq {S T : HSp D} {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e')
    {t y : WO S T} (ht : IsHalf e t) (hy : IsHalf (cA D e') y) :
    symplO S T (t.map (e' * ·)) y = symplO S T t y := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hyc : cA D (y c b) = e' * cA D (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, Formalism.IndefR.Fin.cA_cA]
  rw [Matrix.map_apply]
  calc _ = incA D ((HSpace.gram S)⁻¹ a b) * (e' * cA D (y c b)) * incA D (HSpace.gram T c d) * t d a := by ring
    _ = _ := by rw [← hyc]

open Classical in
theorem extDat_modul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) {e e' : AE D} (h1 : e * e' = e')
    (h2 : e' * e' = e') (Λ : AddSubgroup (WO S T)) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e') y) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => ψ (symplO S T t y) * Φ t) =
      fun t => ψ (symplO S T t y) * GlobalTheory.ChainCol.extDat e e' Λ Φ t := by
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  split_ifs with hc
  · rw [symplO_map_eq h1 h2 hc.1 hy]
  · rw [mul_zero]

open Classical in
theorem extDat_halfInd {e e' : AE D} (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) :
    GlobalTheory.ChainCol.extDat e e' Λ ((1 : ℂ) • halfInd e' Λ) = (1 : ℂ) • halfInd e Λ := by
  unfold halfInd
  rw [one_smul, one_smul]
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  by_cases ht : IsHalf e t
  · have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq ht]
      abel
    have hiff : t ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ ∧ t.map (e' * ·) ∈ Λ := by
      constructor
      · intro h
        refine ⟨?_, hstab t h⟩
        rw [map_sub_eq ht]
        exact sub_mem h (hstab t h)
      · rintro ⟨ha, hb⟩
        rw [hsplit]
        exact add_mem hb ha
    by_cases hA : t.map ((e - e') * ·) ∈ Λ <;> by_cases hB : t.map (e' * ·) ∈ Λ <;>
      simp [ht, hA, hB, hiff, half_map_self h2 t]
  · simp [ht]

theorem isThetaAt_extDat : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ φ f : WO S T → ℂ} {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P → IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T ΛS ΛT fun _ => True) 1 f₀ φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (extDat e e' (latO S T ΛS ΛT fun _ => True) φ) f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ φ f e e' P P' hS hT hV he he' hP h
  unfold IsThetaAt at h ⊢
  obtain ⟨-, hall⟩ := h
  obtain ⟨hstd, hvac⟩ := hV
  have h1 : e * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he hP
  have h2 : e' * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he' (Finset.Subset.refl _)
  have hstab : ∀ u ∈ (latO S T ↑ΛS ↑ΛT fun _ => True),
      u.map (e' * ·) ∈ (latO S T ↑ΛS ↑ΛT fun _ => True) := by
    intro u hu
    have hsm : u.map (e' * ·) = e' • u := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul]
    rw [hsm]
    exact GlobalTheory.PlaceModelSum.idem_smul_latO h2 hu
  have hce : cA D e * cA D e' = cA D e' := by
    rw [← map_mul (cA D), h1]
  refine ⟨?_, fun Tm hTm => ?_⟩
  · have hlv : IsLatVac (heisO ψ S T) (latO S T ↑ΛS ↑ΛT fun _ => True) f₀ := hvac.lat
    have hec : e * cA D e = 0 := by
      unfold IsIdemSum at he
      exact he.2
    exact GlobalTheory.PlaceModelSum.IsOrthSum.exists_model hstd hS hT
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he) hec hlv
  · have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e' (latO S T ↑ΛS ↑ΛT fun _ => True) 1 f₀
        (Tm ∘ₗ extL e e' (latO S T ↑ΛS ↑ΛT fun _ => True)) := by
      obtain ⟨htr, hmo, hva⟩ := hTm
      refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_trans h1 h2 _ Φ hx]
        exact htr _ (extDat_sb h1 h2 _ hstab hΦ) x (half_of_half h1 hx)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_modul ψ h1 h2 _ Φ hy]
        exact hmo _ (extDat_sb h1 h2 _ hstab hΦ) y (half_of_half hce hy)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_halfInd h2 _ hstab]
        exact hva
    rw [hall _ hT', LinearMap.comp_apply, extL_apply]

end GlobalTheory.ExtDatTheta

end
