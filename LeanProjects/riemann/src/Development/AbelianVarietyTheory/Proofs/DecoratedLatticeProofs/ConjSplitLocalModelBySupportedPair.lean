import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def conjH (gk : GL Y' k) (hk : GL Y k) : Matrix Y Y' k ≃ₜ Matrix Y Y' k where
  toFun x := (hk⁻¹).val * x * gk.val
  invFun x := hk.val * x * (gk⁻¹).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def twist (c : ℂ) (gk : GL Y' k) (hk : GL Y k) : SB (Matrix Y Y' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => c * Φ.1 ((hk⁻¹).val * x * gk.val),
    (SB _).smul_mem c (show Φ.1 ∘ conjH gk hk ∈ SB _ from ⟨Φ.2.1.comp_continuous (conjH gk hk).continuous,
      Φ.2.2.comp_homeomorph (conjH gk hk)⟩)⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' a Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (c : ℂ) (gk : GL Y' k) (hk : GL Y k) (Φ : SB (Matrix Y Y' k)) (x) :
    (twist c gk hk Φ).1 x = c * Φ.1 ((hk⁻¹).val * x * gk.val) := rfl

variable {D : D7} (p : Place D k)

theorem mt_inv_mul' {S : HSp D} (g : GA D S) : mt S g⁻¹ * mt S g = 1 := by
  rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
  simp [Formalism.L2.Theta.mt]

theorem actO_up {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {g : GA D S} {gk : GL Y' k}
    {h : GA D T} {hk : GL Y k} (hg : p.IsLoc FS g gk) (hh : p.IsLoc FT h hk) (x : Matrix Y Y' k) :
    actO S T g h (p.up FS FT x) = p.up FS FT (hk.val * x * (gk⁻¹).val) := by
  have h1 : IsHalf p.e (actO S T g h (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO g h (Witness.up_half p FS FT x)
  rw [← Witness.up_down p FS FT h1]
  congr 1
  set M := (mt S g⁻¹).map p.π with hMdef
  have hM : M * (FS.β * gk.val * FS.γ) = 1 := by
    rw [← hg.2, hMdef, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : FS.γ * (M * FS.β) * gk.val = 1 := by
    have : FS.γ * (M * (FS.β * gk.val * FS.γ)) * FS.β = 1 := by rw [hM, Matrix.mul_one, FS.γβ]
    rw [← this]
    simp only [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hN : FS.γ * (M * FS.β) = (gk⁻¹).val := by
    calc FS.γ * (M * FS.β) = FS.γ * (M * FS.β) * gk.val * (gk⁻¹).val := by
          rw [Matrix.mul_assoc (FS.γ * (M * FS.β)), Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e1, Matrix.one_mul]
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hh.2, hu, ← hMdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, hN]

end GlobalTheory.LocTwist

namespace GlobalTheory.LocTwist

theorem conj_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → ∃ T₂ : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ), p.IsModel ψ FS FT T₂ ∧ ∀ Φ Φ' : SB (Matrix Y Y' k), Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → T₂ Φ = ω (g⁻¹, h⁻¹) (Tm Φ') := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT Y Y' _ _ _ _ FS FT Tm hm g gk h hk hg hh
  set c : ℂ := (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) *
    ((μS⁻¹ (Matrix.GeneralLinearGroup.det gk) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det hk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) : ℝ) : ℂ)) with hc
  let L := LocTwist.twist c gk hk
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (g⁻¹, h⁻¹)
  have hA := LocTwist.actO_up p FS FT hg hh
  have hback : ∀ z, actO S T g⁻¹ h⁻¹ (p.up FS FT (hk.val * z * (gk⁻¹).val)) = p.up FS FT z := fun z => by
    rw [← hA, GlobalTheory.SplitHecke.actO_inv_actO]
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun x Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + hk.val * x * (gk⁻¹).val) := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      congr 2
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc ((hk⁻¹).val) hk.val, Units.inv_mul, Matrix.one_mul]
    have h2 := hm.trans _ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hback]
  · set y' := actO S T g h y
    have hy' : IsHalf (cA D p.e) y' := GlobalTheory.SplitHecke.isHalf_actO g h hy
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y') * (L Φ).1 t := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      have hu : p.up FS FT ((hk⁻¹).val * t * gk.val) = actO S T g⁻¹ h⁻¹ (p.up FS FT t) := by
        rw [← hback ((hk⁻¹).val * t * gk.val)]
        congr 2
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hs : symplO S T (p.up FS FT ((hk⁻¹).val * t * gk.val)) y = symplO S T (p.up FS FT t) y' := by
        rw [hu, ← GlobalTheory.SplitHecke.symplO_actO S T g⁻¹ h⁻¹ (p.up FS FT t) y', GlobalTheory.SplitHecke.actO_inv_actO]
      rw [hs]; ring
    have h2 := hm.modul y' hy' (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), GlobalTheory.SplitHecke.actO_inv_actO]
  · have : Φ' = L Φ := by
      apply Subtype.ext; funext t
      rw [e]
      simp only [L, LocTwist.twist_apply, Pi.smul_apply, smul_eq_mul, om, hc]
      ring
    rw [this]; rfl

end GlobalTheory.LocTwist
end
