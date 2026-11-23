import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem levi_one_iff {δ : X.B.I.Gf} (gδ : Good X δ) :
    levi TR δ = 1 ↔ ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  refine ⟨fun h1 i => ?_, fun h => Formalism.L2.SG.Pf.AmpIota.levi_eq_one_of TR gδ h⟩
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set w := X.B.I.fmat δ *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I gδ.1.1 (hB i)
  have hwM := gδ.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat δ *ᵥ X.bw i)) * this
  have hcoef : ∀ j : Fin D.R.k, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hent : leviM TR δ v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR gδ, h1, Pi.one_apply, Units.val_one, Matrix.one_apply]
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h2 : TR.res v ⟨_, hI⟩ = leviM TR δ v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat δ *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h2, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew δ j i]
      split_ifs <;> ring
    simpa [e] using hZ
  have e1 : (X.B.I.fmat δ - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 → c • s ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) ⟨a, rfl⟩
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · exact sum_mem fun j _ => mL_Mo X.B.I (Z_smul_mL X (hcoef j) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

theorem iotaOf_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    Good X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      NCong X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ = levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) *
        iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ := by
  have hTF := Formalism.L2.SG.Full.Full.frameTie (X := X) u u'
  have hN := adm_norm_of_fixed_frames (Y.cs u) (Y.cs u') hTF (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm (Y.cs u) (Y.cs u') (Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u')) hN
  have g1 := hA s₁
  have g2 := hA s₂
  have n1 := hN s₁
  have n2 := hN s₂
  have k1 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₁
  have k2 := Formalism.L2.SG.Pf.termK X (Y.cs u) (Y.cs u') (F0 := X.Fu u) (F0' := X.Fu u') s₂
  rw [← hl, ← hl'] at g2 n2 k2
  have e : (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) *
      (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u) =
      kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₂.pt *
      (kOf X u u' ((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s₁.lam') : X.B.I.Gf) s₁.pt)⁻¹ := by
    unfold kOf; group
  rw [e]
  refine ⟨good_mul X g2 (good_inv X g1), ncong_mul X k2 n2 (ncong_inv X k1 n1), ?_⟩
  unfold iotaOf
  rw [← hl, ← hl', levi_mul Y.TR g2 (good_inv X g1), mul_assoc, ← levi_mul Y.TR (good_inv X g1) g1, inv_mul_cancel,
    levi_one, mul_one]

end Formalism.L2.SG.Pf.IotaDictPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IotaDictPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AdTriv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (δ : X.B.I.Gf) : Prop :=
  ∀ j, (X.B.I.fmat δ - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)

def RatTriv {D : D7} (u : D.what₂.Word) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ x ∈ Lrep Λ (lf D (X.Fu u)), β x - x ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u))

def IotaDictC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

def RatIotaC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic → s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) ↔
        RatTriv u X s₁.lam (s₂.lin * s₁.lin⁻¹))

def IotaBridgeC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      (AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) ↔ RatTriv u X Λ β)

theorem iotaDictC_of (h3 : RatIotaC) (h4 : IotaBridgeC) : IotaDictC := by
  intro D X Y u u' s₁ s₂ hG1 hG2 hg1 hg2 hl hl'
  obtain ⟨hgood, hN, heq⟩ := iotaOf_split Y s₁ s₂ hl hl'
  rw [h3 D X Y u u' s₁ s₂ hG1 hG2 hg1 hg2 hl hl', heq]
  have hlink : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) := ratLink_mul X s₂.rep.2.1 (ratLink_inv X s₁.rep.2.1)
  have hB := h4 D X Y u s₁.lam s₁.mem (s₂.lin * s₁.lin⁻¹) (s₂.pt * s₁.pt⁻¹) hlink hgood.1.1 hN
  have hc : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) *
      X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) *
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ ↔ levi Y.TR ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) *
      X.xu u)⁻¹ * (s₂.pt.2 * s₁.pt.2⁻¹) * (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)) = 1 := by
    constructor
    · intro h
      have h' := congrArg (· * (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁)⁻¹) h
      simpa using h'.symm
    · intro h
      rw [h, one_mul]
  exact hc.trans ((levi_one_iff Y.TR hgood).trans hB)

end Formalism.L2.SG.Pf
