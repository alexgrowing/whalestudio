import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

open GlobalTheory.Mem.SymChar.Resid in

theorem resid_at_w : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  intro D X _h _hE hgw kv k hk N hN
  classical
  have hg : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := hgw kv
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  set w := D.naut.plGw kv.1 kv.2 with hwdef
  let S : AddSubgroup (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := (wInt X w).toAddSubgroup
  let mk := QuotientAddGroup.mk' S
  have hmk : ∀ a b, a - b ∈ wInt X w → mk a = mk b := fun a b hab =>
    (QuotientAddGroup.eq_iff_sub_mem).2 hab
  let f0 : ℤ →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    mk.comp (Int.castAddHom (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
  have hf0 : f0 (D.host.g kv.1 : ℤ) = 0 := by
    show mk ((((D.host.g kv.1 : ℕ) : ℤ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) = 0
    rw [Int.cast_natCast]
    exact (QuotientAddGroup.eq_zero_iff _).2 (natCast_g_mem X kv.1 hg)
  let φ : ZMod (D.host.g kv.1) →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    ZMod.lift (D.host.g kv.1) ⟨f0, hf0⟩
  have hφ : ∀ t : ZMod (D.host.g kv.1), φ t = mk ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    intro t
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast]
    rw [ZMod.lift_coe]
    show mk _ = mk _
    congr 1
    simp
  suffices hs : mk (argS X k) = φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) by
    unfold ModW
    rw [hφ] at hs
    exact (QuotientAddGroup.eq_iff_sub_mem).1 hs
  have hsum : φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) =
      ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then wtA D.R.rS D.R.k (side X w) i j • φ (N i j) else 0 := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← zsmul_eq_mul, map_zsmul]
    · exact map_zero φ
  rw [hsum, GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex _ D.R.rS D.R.k D.R.r (rank_eq D) (side X w) (fun i j => φ (N i j))]
  unfold argS
  rw [map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ]
    apply hmk
    have := dual_row X w hN (X.vectorsInLattice.1 a).2 (posE D a) (GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg a) (posN D a)
    rw [symVec_posN] at this
    exact this
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dif_pos hi, dif_pos hi]
      by_cases hw : SymFrame.EwAt X w
      · have hs : side X w = true := by simp [side, hw]
        rw [if_pos hs, hφ]
        apply hmk
        have h1 := one_sub_ew_mem X kv.1 hg hw
        have := dual_row X w hN (X.vectorsInLattice.2.2 i).2 (posB D i) (GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg hw h1 i)
          (posB D ⟨i.1 + 1, hi⟩)
        rw [symVec_posB X w hw] at this
        have e1 : (posB D ⟨i.1 + 1, hi⟩) = ⟨D.R.rS + i.1 + 1, by have := rank_eq D; omega⟩ :=
          Fin.ext (by simp only [posB]; omega)
        rw [e1] at this
        exact this
      · have hs : side X w = false := by simp [side, hw]
        rw [if_neg (by simp [hs])]
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have hew := GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one D X kv hw
        have hbw : X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩ ∈ X.B.I.Lf :=
          Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1
        have hint := Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 i).2 hbw
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) =
            hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) * X.ew := by
          conv_lhs => rw [X.bwd_w i]
          rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, mul_comm]
        show hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) ∈ wInt X w
        rw [e]
        exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hew
    · rw [dif_neg hi, dif_neg hi, map_zero]

end GlobalTheory.Mem.SymChar
