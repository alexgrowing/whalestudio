import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

def conjJAt (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u →ₗ[ℂ] ℂ where
  toFun η := star (tr.J η z)
  map_add' η η' := by simp [map_add]
  map_smul' c η := by simp [map_smulₛₗ]

def rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (conjJAt tr z))

theorem inner_rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) (η : X.Vpi u) :
    ⟪η, rieszJ tr z⟫_ℂ = tr.J η z := by
  rw [← inner_conj_symm]
  simp [rieszJ, conjJAt]

variable (X) in

def RepM (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ Formalism.L2.SG.ColDict.qA X wt j = ∑ i, ιA.symm (M i j) • Formalism.L2.SG.ColDict.qA X wt i

end GlobalTheory.Core.Mi

end

namespace GlobalTheory.Core.Mi

section Helpers

variable {D : D7}

theorem unitaryAdelicPointFiniteMatrix_base_space_mul (a b : GA D (D.sp.X 0)) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) =
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointFiniteMatrix_base_space_one : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) = 1 := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_base_space_mul (θ : InfFam D) (a b : GA D (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) τ =
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b τ := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointInfiniteMatrices_base_space_one (θ : InfFam D) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) τ = 1 := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, map_one, Units.val_one]
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_eq_one_of_finite (θ : InfFam D) (a : GA D (D.sp.X 0)) (ha : a ∈ GfC (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 := by
  have h1 : Formalism.L2.Theta.infHom (D.sp.X 0) a = 1 := ha
  unfold Formalism.L2.Theta.infHom at h1
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have h2 := congrArg (fun x : GL (Fin (D.sp.X 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => ((x.1).map (θ τ))) h1
  simp only [MonoidHom.comp_apply, Units.val_one] at h2
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = (M.map (infPart D)).map (θ τ) := fun M => by ext; rfl
  rw [e]
  have h3 : ((Formalism.L2.Theta.matHom (D.sp.X 0)) a).1.map (infPart D) =
      ((Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom)
        ((Formalism.L2.Theta.matHom (D.sp.X 0)) a) : GL _ _).1 := rfl
  rw [h3, h2]
  simp [Matrix.reindex_apply]

end Helpers

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem toH_mul {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D}
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (a b : GA D A) :
    B.toH (a * b) = B.toH a * B.toH b := by
  unfold SBes.toH
  ext <;> simp [map_mul]

theorem RepM_cancel {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F}
    {h k : X.B.I.Gf} {A M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)}
    (hA : RepM X wt ιA h A) (hAM : RepM X wt ιA (h * k) (A * M)) : RepM X wt ιA k M := by
  intro j
  have hmul : X.B.I.fmat (h * k) = X.B.I.fmat h * X.B.I.fmat k := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat h⁻¹ * X.B.I.fmat h = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j) =
      X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hAM j, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hA, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  calc X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j
      = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l)) := by rw [key]
    _ = _ := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem span_rieszJ {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    Submodule.span ℂ (Set.range fun y => rieszJ tr (F.val0.eY y)) = ⊤ := by
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro η hη
  apply tr.J_injective c
  rw [map_zero]
  funext z
  obtain ⟨y, rfl⟩ := F.val0.eY.surjective z
  rw [← inner_rieszJ]
  exact (Submodule.mem_orthogonal' _ _).1 hη _ (Submodule.subset_span ⟨y, rfl⟩)

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem colDictL_eY_symm {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (c : (D.mem u).C.cls 0)
    (w : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) :
    Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) = tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w := by
  have : Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) (F.val0.eY (F.val0.eY.symm w)) := rfl
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.Core.Mi
