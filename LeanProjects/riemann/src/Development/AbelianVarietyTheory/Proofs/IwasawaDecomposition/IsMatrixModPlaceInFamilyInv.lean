import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem invMat_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] [Fact (1 < g)]
    (T S : Q →+ Q) (hST : ∀ q, S (T q) = q) (β : ι → Q) (hβ : ∀ i, g • β i = 0)
    (N N' : Matrix ι ι (ZMod g)) (hNN' : N * N' = 1)
    (hT : ∀ i, T (β i) = ∑ j, (N j i).val • β j) (m : ι) :
    S (β m) = ∑ i, (N' i m).val • β i := by
  have e1 : T (∑ i, (N' i m).val • β i) = ∑ l, ((N * N') l m).val • β l := by
    rw [map_sum]
    simp only [map_nsmul, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e2 : ∑ l, (((1 : Matrix ι ι (ZMod g))) l m).val • β l = β m := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.one_apply_eq, ZMod.val_one, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, ZMod.val_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hNN', e2] at e1
  rw [← e1, hST]

end GlobalTheory.Mem.SymFrame

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  intro D X kv hg u hu k hk N hN m
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  haveI : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  let W := (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
  have hk' : k⁻¹ ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk
  let fT := (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
  let fS := (Matrix.mulVecLin (X.B.I.fmat k⁻¹)).toAddMonoidHom
  let T := QuotientAddGroup.map W W fT (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
  let S := QuotientAddGroup.map W W fS (fun v hv => fmat_mulVec_mem_wLf X _ hk' hv)
  have key : ∀ a b : VA X.B.I, a - b ∈ wLf X (D.naut.plGw kv.1 kv.2) ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    show a - b ∈ W ↔ _
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hST : ∀ q, S (T q) = q := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      show QuotientAddGroup.mk' W (X.B.I.fmat k⁻¹ *ᵥ (X.B.I.fmat k *ᵥ v)) = QuotientAddGroup.mk' W v
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul X.B.I k, Matrix.one_mulVec]
  have hβ : ∀ i, D.host.g kv.1 • QuotientAddGroup.mk' W (u i) = 0 := fun i => by
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
      ⟨_, hg, by simp⟩ (y := u i) (hu i)
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
      simp [map_natCast]
    rw [e, Nat.cast_smul_eq_nsmul] at h1
    exact h1
  have hT : ∀ i, T (QuotientAddGroup.mk' W (u i)) =
      ∑ j, ((N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • QuotientAddGroup.mk' W (u j) := by
    intro i
    have := (key _ _).1 (by simpa only [Nat.cast_smul_eq_nsmul] using hN i)
    rw [map_sum] at this
    simp only [map_nsmul] at this
    rw [← this]; rfl
  have h := invMat_quot T S hST (fun i => QuotientAddGroup.mk' W (u i)) hβ
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hT m
  simp only [Nat.cast_smul_eq_nsmul]
  rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

end GlobalTheory.Mem.SymFrame
