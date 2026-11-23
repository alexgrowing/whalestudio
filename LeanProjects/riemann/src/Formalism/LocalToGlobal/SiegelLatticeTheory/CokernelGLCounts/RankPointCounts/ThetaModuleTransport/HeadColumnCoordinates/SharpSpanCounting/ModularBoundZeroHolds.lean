import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Gen

variable {R : Type} [CommRing R] {r : ℕ}

theorem col_mem_headCols (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (a : Fin r) :
    (fun i => Z i a.castSucc) ∈ headCols Z := Submodule.subset_span ⟨a, rfl⟩

theorem col_eq_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (j : Fin (r + 1)) :
    (fun i => Z i j) = Z.mulVec (Pi.single j 1) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mulVec_mem_headCols (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (w : Fin (r + 1) → R)
    (hw : w (Fin.last r) = 0) : Z.mulVec w ∈ headCols Z := by
  have hw' : w = ∑ j, w j • Pi.single j (1 : R) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : Z.mulVec w = ∑ j, w j • Z.mulVec (Pi.single j 1) := by
    conv_lhs => rw [hw']
    rw [← Matrix.mulVecLin_apply, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  rw [hsum, Fin.sum_univ_castSucc, hw, zero_smul, add_zero]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  rw [← col_eq_mulVec]
  exact col_mem_headCols Z a

theorem mk_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (w : Fin (r + 1) → R) :
    (Submodule.Quotient.mk (Z.mulVec w) : MbMod Z) = w (Fin.last r) • bCls Z := by
  unfold bCls
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have h : Z.mulVec w - w (Fin.last r) • (fun i => Z i (Fin.last r)) =
      Z.mulVec (w - w (Fin.last r) • Pi.single (Fin.last r) 1) := by
    rw [col_eq_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [h]
  apply mulVec_mem_headCols
  simp

end Gen

section Mod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {r : ℕ}

def ellRaw (Z : M.Mat (r + 1)) : (Fin (r + 1) → M.R) →ₗ[M.R] E :=
  (LinearMap.proj (Fin.last r)) ∘ₗ ((Z.Z.map M.R.subtype)⁻¹.mulVecLin.restrictScalars M.R) ∘ₗ
    (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (r + 1)))

theorem ellRaw_apply (Z : M.Mat (r + 1)) (v : Fin (r + 1) → M.R) :
    ellRaw Z v = ((Z.Z.map M.R.subtype)⁻¹.mulVec (fun j => (v j : E))) (Fin.last r) := rfl

theorem ellRaw_mulVec (Z : M.Mat (r + 1)) (w : Fin (r + 1) → M.R) :
    ellRaw Z (Z.Z.mulVec w) = (w (Fin.last r) : E) := by
  rw [ellRaw_apply]
  have h : (fun j => ((Z.Z.mulVec w j : M.R) : E)) =
      (Z.Z.map M.R.subtype).mulVec (fun j => (w j : E)) := by
    funext j
    simp [Matrix.mulVec, dotProduct]
  rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec]

theorem ellRaw_col (Z : M.Mat (r + 1)) (j : Fin (r + 1)) :
    ellRaw Z (fun i => Z.Z i j) = (((Pi.single j (1 : M.R) : Fin (r + 1) → M.R) (Fin.last r) : M.R) : E) := by
  rw [col_eq_mulVec, ellRaw_mulVec]

theorem headCols_le_ker (Z : M.Mat (r + 1)) : headCols Z.Z ≤ LinearMap.ker (ellRaw Z) := by
  unfold headCols
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rw [ellRaw_col]
  simp [Pi.single_apply, (Fin.castSucc_lt_last a).ne']

theorem headCols_le_range (Z : M.Mat (r + 1)) :
    headCols Z.Z ≤ (LinearMap.range Z.Z.mulVecLin).comap LinearMap.id := by
  have h : headCols Z.Z ≤ LinearMap.range Z.Z.mulVecLin := by
    unfold headCols
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a.castSucc 1, (col_eq_mulVec Z.Z a.castSucc).symm⟩
  intro x hx
  exact h hx

def ell (Z : M.Mat (r + 1)) : MbMod Z.Z →ₗ[M.R] E :=
  (headCols Z.Z).liftQ (ellRaw Z) (headCols_le_ker Z)

def piC (Z : M.Mat (r + 1)) : MbMod Z.Z →ₗ[M.R] M.Cok Z :=
  (headCols Z.Z).mapQ (LinearMap.range Z.Z.mulVecLin) LinearMap.id (headCols_le_range Z)

theorem ell_mk (Z : M.Mat (r + 1)) (v : Fin (r + 1) → M.R) :
    ell Z (Submodule.Quotient.mk v) = ellRaw Z v := rfl

theorem piC_mk (Z : M.Mat (r + 1)) (v : Fin (r + 1) → M.R) :
    piC Z (Submodule.Quotient.mk v) = (Submodule.Quotient.mk v : M.Cok Z) := rfl

theorem ell_smul (Z : M.Mat (r + 1)) (s : M.R) (m : MbMod Z.Z) :
    ell Z (s • m) = (s : E) * ell Z m := by
  rw [map_smul, Subring.smul_def, smul_eq_mul]

theorem ell_b (Z : M.Mat (r + 1)) : ell Z (bCls Z.Z) = 1 := by
  unfold bCls
  rw [ell_mk, ellRaw_col]
  simp

theorem piC_b (Z : M.Mat (r + 1)) : piC Z (bCls Z.Z) = 0 := by
  unfold bCls
  rw [piC_mk, Submodule.Quotient.mk_eq_zero]
  exact ⟨Pi.single (Fin.last r) 1, (col_eq_mulVec Z.Z _).symm⟩

theorem piC_e (Z : M.Mat (r + 1)) : piC Z (eCl Z.Z) = M.eCls Z := rfl

theorem ell_e (Z : M.Mat (r + 1)) (hD : headDet M Z.Z = 0) : ell Z (eCl Z.Z) = 0 := by
  unfold eCl
  unfold headDet at hD
  rw [ell_mk, ellRaw_apply]
  have h1 : (fun j => (((Pi.single (Fin.last r) (1 : M.R) : Fin (r + 1) → M.R) j : M.R) : E)) =
      Pi.single (Fin.last r) (1 : E) := by
    funext j
    by_cases hj : j = Fin.last r
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  have h2 : (Z.Z.map M.R.subtype).adjugate (Fin.last r) (Fin.last r) = 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, hD, mul_zero]
  rw [h1, Matrix.inv_def]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  exact mul_eq_zero_of_right _ h2

theorem lam_piC (Z : M.Mat (r + 1)) (m : MbMod Z.Z) :
    M.lam Z (piC Z m) = M.Rsub.mkQ (ell Z m) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [piC_mk, ell_mk]
  rfl

theorem piC_surj (Z : M.Mat (r + 1)) : Function.Surjective (piC Z) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk v, piC_mk Z v⟩

def Phi (Z : M.Mat (r + 1)) : MbMod Z.Z →ₗ[M.R] M.Cok Z × E := (piC Z).prod (ell Z)

theorem Phi_apply (Z : M.Mat (r + 1)) (m : MbMod Z.Z) : Phi Z m = (piC Z m, ell Z m) := rfl

theorem Phi_inj (Z : M.Mat (r + 1)) : Function.Injective (Phi Z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Phi_apply, Prod.mk_eq_zero, piC_mk, ell_mk, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨⟨w, hw⟩, h2⟩ := hm
  rw [Matrix.mulVecLin_apply] at hw
  subst hw
  rw [Submodule.Quotient.mk_eq_zero]
  apply mulVec_mem_headCols
  have h3 : ((w (Fin.last r) : M.R) : E) = 0 := by
    rw [← ellRaw_mulVec]
    exact h2
  exact Subtype.ext h3

theorem mem_range_Phi (Z : M.Mat (r + 1)) (p : M.Cok Z × E) :
    p ∈ LinearMap.range (Phi Z) ↔ M.Rsub.mkQ p.2 = M.lam Z p.1 := by
  constructor
  · rintro ⟨m, rfl⟩
    rw [Phi_apply, lam_piC]
  · intro h
    obtain ⟨c, x⟩ := p
    obtain ⟨m, rfl⟩ := piC_surj Z c
    dsimp only at h
    rw [lam_piC, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
    simp only [Model.Rsub, LinearMap.mem_range] at h
    obtain ⟨s, hs⟩ := h
    have hs' : (s : E) = x - ell Z m := hs
    refine ⟨m + s • bCls Z.Z, ?_⟩
    rw [Phi_apply, map_add, map_smul, piC_b, smul_zero, add_zero, map_add, ell_smul, ell_b,
      mul_one, hs']
    congr 1
    abel

def ePhi (Z : M.Mat (r + 1)) : MbMod Z.Z ≃ₗ[M.R] LinearMap.range (Phi Z) :=
  LinearEquiv.ofInjective (Phi Z) (Phi_inj Z)

theorem ePhi_coe (Z : M.Mat (r + 1)) (m : MbMod Z.Z) : (ePhi Z m : M.Cok Z × E) = Phi Z m := rfl

theorem det_unit (Z : M.Mat (r + 1)) : IsUnit ((Z.Z.det : M.R) : E) := by
  have h := Z.unit
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact h

theorem det_smul_mk (Z : M.Mat (r + 1)) (v : Fin (r + 1) → M.R) :
    Z.Z.det • (Submodule.Quotient.mk v : MbMod Z.Z) =
      (Z.Z.adjugate.mulVec v) (Fin.last r) • bCls Z.Z := by
  rw [← Submodule.Quotient.mk_smul, ← mk_mulVec Z.Z (Z.Z.adjugate.mulVec v), Matrix.mulVec_mulVec,
    Matrix.mul_adjugate]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

variable {Z₁ Z₂ : M.Mat (r + 1)}

theorem ell_comp (g : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : g (bCls Z₁.Z) = bCls Z₂.Z)
    (m : MbMod Z₁.Z) : ell Z₂ (g m) = ell Z₁ m := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h1 := det_smul_mk Z₁ v
  have h2 : ell Z₂ (g (Z₁.Z.det • Submodule.Quotient.mk v)) =
      ell Z₁ (Z₁.Z.det • (Submodule.Quotient.mk v : MbMod Z₁.Z)) := by
    rw [h1, map_smul, hb, ell_smul, ell_smul, ell_b, ell_b]
  rw [map_smul, ell_smul, ell_smul] at h2
  exact (det_unit Z₁).mul_left_cancel h2

theorem ell_equiv (γ : MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (m : MbMod Z₁.Z) : ell Z₂ (γ m) = ell Z₁ m := ell_comp γ.toLinearMap hb m

theorem range_le_ker_ind (g : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : g (bCls Z₁.Z) = bCls Z₂.Z) :
    LinearMap.range Z₁.Z.mulVecLin ≤ LinearMap.ker (piC Z₂ ∘ₗ g ∘ₗ (headCols Z₁.Z).mkQ) := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    Matrix.mulVecLin_apply, mk_mulVec, map_smul, hb, map_smul, piC_b, smul_zero]

def ind (g : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : g (bCls Z₁.Z) = bCls Z₂.Z) :
    M.Cok Z₁ →ₗ[M.R] M.Cok Z₂ :=
  (LinearMap.range Z₁.Z.mulVecLin).liftQ _ (range_le_ker_ind g hb)

theorem ind_piC (g : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : g (bCls Z₁.Z) = bCls Z₂.Z)
    (m : MbMod Z₁.Z) : ind g hb (piC Z₁ m) = piC Z₂ (g m) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [piC_mk]
  rfl

theorem symm_b (γ : MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z) :
    γ.symm.toLinearMap (bCls Z₂.Z) = bCls Z₁.Z := by
  rw [← hb]
  exact γ.symm_apply_apply _

def psiOf (γ : MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z) :
    M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂ :=
  LinearEquiv.ofLinear (ind γ.toLinearMap hb) (ind γ.symm.toLinearMap (symm_b γ hb))
    (by
      apply LinearMap.ext; intro x
      obtain ⟨m, rfl⟩ := piC_surj Z₂ x
      rw [LinearMap.comp_apply, ind_piC, ind_piC, LinearMap.id_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
    (by
      apply LinearMap.ext; intro x
      obtain ⟨m, rfl⟩ := piC_surj Z₁ x
      rw [LinearMap.comp_apply, ind_piC, ind_piC, LinearMap.id_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

theorem psiOf_piC (γ : MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (m : MbMod Z₁.Z) : psiOf γ hb (piC Z₁ m) = piC Z₂ (γ m) := ind_piC γ.toLinearMap hb m

def sig (ψ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂) : (M.Cok Z₁ × E) ≃ₗ[M.R] (M.Cok Z₂ × E) :=
  ψ.prodCongr (LinearEquiv.refl M.R E)

theorem sig_apply (ψ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂) (p : M.Cok Z₁ × E) :
    sig ψ p = (ψ p.1, p.2) := LinearEquiv.prodCongr_apply _ _ p

theorem map_sig (ψ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂) (hl : ∀ v, M.lam Z₂ (ψ v) = M.lam Z₁ v) :
    (LinearMap.range (Phi Z₁)).map (sig ψ : (M.Cok Z₁ × E) →ₗ[M.R] (M.Cok Z₂ × E)) =
      LinearMap.range (Phi Z₂) := by
  ext p
  rw [Submodule.mem_map, mem_range_Phi Z₂ p]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_range_Phi] at hq
    simp only [LinearEquiv.coe_coe, sig_apply, hl]
    exact hq
  · intro hp
    refine ⟨(ψ.symm p.1, p.2), ?_, ?_⟩
    · rw [mem_range_Phi]
      dsimp only
      rw [← hl (ψ.symm p.1), LinearEquiv.apply_symm_apply]
      exact hp
    · rw [LinearEquiv.coe_coe, sig_apply]
      dsimp only
      rw [LinearEquiv.apply_symm_apply]

def gamOf (ψ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂) (hl : ∀ v, M.lam Z₂ (ψ v) = M.lam Z₁ v) :
    MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z :=
  ((ePhi Z₁).trans ((sig ψ).ofSubmodules _ _ (map_sig ψ hl))).trans (ePhi Z₂).symm

theorem Phi_gamOf (ψ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂) (hl : ∀ v, M.lam Z₂ (ψ v) = M.lam Z₁ v)
    (m : MbMod Z₁.Z) : Phi Z₂ (gamOf ψ hl m) = sig ψ (Phi Z₁ m) := by
  have h1 : ∀ y : LinearMap.range (Phi Z₂), Phi Z₂ ((ePhi Z₂).symm y) = y := by
    intro y
    rw [← ePhi_coe, LinearEquiv.apply_symm_apply]
  unfold gamOf
  rw [LinearEquiv.trans_apply, h1, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_apply, ePhi_coe]

def isoEquiv (hD₁ : headDet M Z₁.Z = 0) (hD₂ : headDet M Z₂.Z = 0) :
    IsoMbe Z₁.Z Z₂.Z ≃ M.Iso Z₁ Z₂ where
  toFun γ := ⟨psiOf γ.1 γ.2.1, by rw [← piC_e, psiOf_piC, γ.2.2, piC_e], fun v => by
      obtain ⟨m, rfl⟩ := piC_surj Z₁ v
      rw [psiOf_piC, lam_piC, lam_piC, ell_equiv γ.1 γ.2.1]⟩
  invFun ψ := ⟨gamOf ψ.1 ψ.2.2, by
      apply Phi_inj Z₂
      rw [Phi_gamOf]
      simp [Phi_apply, sig_apply, piC_b, ell_b], by
      apply Phi_inj Z₂
      rw [Phi_gamOf]
      simp [Phi_apply, sig_apply, piC_e, ell_e Z₁ hD₁, ell_e Z₂ hD₂, ψ.2.1]⟩
  left_inv γ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro m
    apply Phi_inj Z₂
    rw [Phi_gamOf]
    simp [Phi_apply, sig_apply, psiOf_piC, ell_equiv γ.1 γ.2.1]
  right_inv ψ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    obtain ⟨m, rfl⟩ := piC_surj Z₁ x
    have := congrArg Prod.fst (Phi_gamOf ψ.1 ψ.2.2 m)
    simp only [Phi_apply, sig_apply] at this
    exact (psiOf_piC _ _ m).trans this

theorem modularBoundZero_holds (M : Model F E) (r : ℕ) : Mbe0 M r := by
  unfold Mbe0
  intro Z₁ Z₂ hD₁ hD₂
  exact Nat.card_congr (isoEquiv hD₁ hD₂)

end Mod

end Formalism.L2.SG.LocalCountModules.LocCntCommon
