import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.MemMLOfInAt

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section LeviHom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem leviM_mul_inv {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : leviM TR x v * leviM TR x⁻¹ v = 1 := by
  rw [← leviM_mul_par TR hx.1 hx.2, mul_inv_cancel, leviM_one]

theorem isUnit_det_leviM {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : IsUnit (leviM TR x v).det :=
  isUnit_iff_exists_inv.2 ⟨(leviM TR x⁻¹ v).det, by rw [← Matrix.det_mul, leviM_mul_inv TR hx, Matrix.det_one]⟩

theorem levi_coe {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = leviM TR x v := by
  unfold levi
  rw [dif_pos (isUnit_det_leviM TR hx v)]
  rfl

theorem levi_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : levi TR (x * y) = levi TR x * levi TR y := by
  funext v
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, levi_coe TR (good_mul X hx hy), levi_coe TR hx, levi_coe TR hy,
    leviM_mul_par TR hx.1 hy.1]

theorem levi_one : levi TR (1 : X.B.I.Gf) = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR (good_one X), leviM_one]
  rfl

end LeviHom

section FixAux

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fmat_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem fixes_mul {x y : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) (hy : X.B.I.fmat y *ᵥ v = v) :
    X.B.I.fmat (x * y) *ᵥ v = v := by
  rw [fmat_mul, ← Matrix.mulVec_mulVec, hy, hx]

theorem fixes_inv {x : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) : X.B.I.fmat x⁻¹ *ᵥ v = v := by
  calc X.B.I.fmat x⁻¹ *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ v) := by rw [hx]
    _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]

theorem mem_mL_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (m : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I m) :
    X.B.I.fmat x *ᵥ y ∈ mL X.B.I m := by
  unfold mL at *
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨X.B.I.fmat x *ᵥ w, ?_, ?_⟩
    · exact (hx w).1 hw
    · rw [Matrix.mulVec_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ c ha

theorem congG_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) {δ : VA X.B.I} (hδ : InAt X.B.I X.B.g X.B.g δ) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat x *ᵥ δ - δ) := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  refine ⟨c, hc, ?_⟩
  rw [smul_sub, ← Matrix.mulVec_smul]
  exact Submodule.sub_mem _ (mem_mL_of_Kset X hx _ hcδ) hcδ

end FixAux

section ColGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_hA_mL {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I d w) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (mL_Qs X.B.I X.B.g hw hd)

theorem colStab (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    (∀ a, X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.e0 a - X.e0 a ∈
      mL X.B.I X.B.g) ∧
    X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  set k := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) with hkdef
  obtain ⟨hE0, hF0, hZ0, -, -⟩ := frame_Lf X
  have hk' : k = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by rw [hkdef]; group
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y → X.B.I.fmat k *ᵥ incl X.B.I y = incl X.B.I y := by
    intro y hy hxu
    rw [hk']
    have h1 : X.B.I.fmat (h' : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h'.2 y hy
    have h2 : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := fixes_inv X (h.2 y hy)
    exact fixes_mul X (fixes_inv X hxu) (fixes_mul X h2 (fixes_mul X h1 hxu))
  have hE : ∀ a, X.B.I.fmat k *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) := fun a =>
    hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)) ((X.xu_fix u a).1)
  have hZ : X.B.I.fmat k *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u))) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) := by
    rw [Matrix.mulVec_mulVec, ← fmat_mul]
    have e : k * (X.xu u)⁻¹ = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by rw [hkdef]; group
    rw [e, fmat_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have hy : X.crd (X.zu u) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u := Or.inr rfl
    exact fixes_mul X (fixes_inv X (h.2 _ hy)) (h'.2 _ hy)
  have key : ∀ (w v : VA X.B.I), v ∈ X.B.I.Lf → X.B.I.fmat k *ᵥ w = w → InAt X.B.I X.B.g X.B.g (v - w) →
      X.B.I.fmat k *ᵥ v - v ∈ mL X.B.I X.B.g := by
    intro w v hv hw hvw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hk hv) hv) ?_
    have := congG_of_Kset X hk hvw
    have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - w) - (v - w) := by
      rw [Matrix.mulVec_sub, hw]; abel
    rw [e]; exact this
  refine ⟨fun a => key _ _ (hE0 a) (hE a) (X.basisApprox a).1, key _ _ hZ0 hZ ?_⟩
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  refine ⟨c, hc, ?_⟩
  rw [show X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) =
    -(X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) - X.z0) by abel, smul_neg]
  exact Submodule.neg_mem _ hcm

theorem par_of_stab {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    (he : ∀ a, X.B.I.fmat k *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hie : ∀ a, X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hiz : X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g) : Par X k := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hk, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat k *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k *ᵥ X.e0 a - X.e0 a) by abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (mL_Mo X.B.I (he a))
  · refine mem_Mo_eb X (K_mv X.B.I hk (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a) by abel,
        hA_add_left]
      exact Z_add X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1 (Z_hA_mL X (hie a) (hB j))
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0) by abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (Z_hA_mL X hiz (hB j))
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem colGood (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset)
    (hki : ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    Good X (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by
  have einv : (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) := by group
  have s1 := colStab X u h h' hk
  have s2 := colStab X u h' h hki
  refine ⟨par_of_stab X hk s1.1 (by rw [einv]; exact s2.1) (by rw [einv]; exact s2.2), ?_⟩
  rw [einv]
  have einv2 : (((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) := by group
  exact par_of_stab X hki s2.1 (by rw [einv2]; exact s1.1) (by rw [einv2]; exact s1.2)

end ColGood

end PI.UnitaryDimensionFormula.NormCutK
