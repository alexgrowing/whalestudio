import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInvStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdealStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.ResBar

variable {D : D7}

theorem unip_inv_sup {κ : Type} [CommRing κ] {r : ℕ} {N : GL (Fin r) κ} (hN : N ∈ unip κ r) (i j : Fin r)
    (hij : j.val = i.val + 1) :
    ((N⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = -(N : Matrix (Fin r) (Fin r) κ) i j := by
  have hi := Subgroup.inv_mem _ hN
  have h := unip_mul_entry hi hN (i := i) (j := j) (show i.val < j.val by omega) (fun l h1 h2 => by
    exfalso
    have : i.val < l.val := h1
    have : l.val < j.val := h2
    omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

abbrev QW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Type :=
  (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ (wInt X w).toAddSubgroup

abbrev mkW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) →+ QW X w :=
  QuotientAddGroup.mk' _

theorem mkW_eq {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a b : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a - b ∈ wInt X w) : mkW X w a = mkW X w b := by
  show (QuotientAddGroup.mk a : QW X w) = QuotientAddGroup.mk b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem mkW_zero {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a ∈ wInt X w) : mkW X w a = 0 := by
  rw [← map_zero (mkW X w)]
  exact mkW_eq (by rw [sub_zero]; exact h)

theorem phi_exists (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) [NeZero g]
    (hg : ((g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w) :
    ∃ φ : ZMod g →+ QW X w, ∀ t : ZMod g, φ t = t.val • mkW X w 1 := by
  refine ⟨ZMod.lift g ⟨zmultiplesHom _ (mkW X w 1), ?_⟩, fun t => ?_⟩
  · rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, nsmul_one]
    exact mkW_zero hg
  · conv_lhs => rw [← ZMod.natCast_zmod_val t]
    have e : ((t.val : ℕ) : ZMod g) = ((t.val : ℤ) : ZMod g) := by simp
    rw [e, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

theorem modW_of {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    {φ : ZMod g →+ QW X w} (hφ : ∀ t : ZMod g, φ t = t.val • mkW X w 1)
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} {t : ZMod g} (h : mkW X w c = φ t) : ModW X w c t := by
  unfold ModW
  rw [hφ, ← map_nsmul, nsmul_one] at h
  show (c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ (wInt X w).toAddSubgroup
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem read (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hM : GlobalTheory.Mem.SymFrame.IsMatIn X w u x M)
    {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (p q : Fin D.R.r) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hG : ∀ j, hA X.B.I v (u j) - (if j = q then c else 0) ∈ wInt X w) :
    mkW X w (hA X.B.I v (X.B.I.fmat x *ᵥ u p)) = (M q p).val • mkW X w c := by
  classical
  rw [mkW_eq (hA_isMatIn X w hM hv p), map_sum]
  have e : ∀ j, mkW X w ((((M j p).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I v (u j)) =
      if j = q then (M q p).val • mkW X w c else 0 := by
    intro j
    rw [← nsmul_eq_mul, map_nsmul, mkW_eq (hG j)]
    split_ifs with hj
    · rw [hj]
    · rw [map_zero, smul_zero]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem symVec_mem (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    GlobalTheory.Mem.SymFrame.symVec X w j ∈ X.B.I.Lf := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact (X.vectorsInLattice.2.2 _).1
  · exact (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem symmetricOrderFrameModPlace_last_block (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) (p : Fin D.R.r)
    (hp : p.val = 2 * D.R.rS + D.R.k - a.val) : GlobalTheory.Mem.SymFrame.symVec X w p = X.f0 a := by
  have hr := r_eq D
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp only
  omega

theorem symVec_bwd (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X w)
    (i : Fin D.R.k) (p : Fin D.R.r) (hp : p.val = D.R.rS + D.R.k - 1 - i.val) :
    GlobalTheory.Mem.SymFrame.symVec X w p = X.bwd i := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  rw [if_neg hE, dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp only [Fin.val_rev]
  omega

theorem ite_val {r : ℕ} {R : Type} [Zero R] (j q : Fin r) (n : ℕ) (hq : q.val = n) (c : R) :
    (if j.val = n then c else 0) = (if j = q then c else 0) := by
  by_cases h : j = q
  · subst h; simp [hq]
  · have : j.val ≠ n := fun e => h (Fin.ext (by omega))
    simp [h, this]

theorem resBar : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  intro D X h hι hg kv k hk N hN hNu
  classical
  have hgw := hg kv
  set w := D.naut.plGw kv.1 kv.2 with hw
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have hgA : (((D.host.g kv.1 : ℕ)) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E), ⟨_, hgw, ?_⟩, ?_⟩
    · simp
    · simp
  obtain ⟨φ, hφ⟩ := phi_exists X w _ hgA
  have hr := r_eq D
  set u := GlobalTheory.Mem.SymFrame.symVec X w with hu_def
  have hu : ∀ i, u i ∈ X.B.I.Lf := symVec_mem X w
  have hNi := GlobalTheory.T.isMatrixModPlaceInFamily_inv D X kv hgw u hu k hk N hN
  have hU : N ∈ unip _ _ := unipCol_le _ _ _ hNu
  rw [GlobalTheory.T.symEdge_conjWeighted_sum_eq_flag_and_unipotent_pairs _ _ _ hr]
  apply modW_of hφ
  simp only [argS, map_add, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (nxt X.e0 X.z0 a) (X.f0 a)
    rw [inv_inv] at e
    rw [← e, ← symmetricOrderFrameModPlace_last_block X w a ⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ rfl]
    by_cases ha : a.val + 1 < D.R.rS
    · rw [dif_pos ha]
      have hn : nxt X.e0 X.z0 a = X.e0 ⟨a.val + 1, ha⟩ := by unfold nxt; rw [dif_pos ha]
      rw [hn, read X w hNi (X.vectorsInLattice.1 _).1 _ ⟨2 * D.R.rS + D.R.k - a.val - 1, by omega⟩ 1 (fun j => by
        rw [← ite_val j _ (2 * D.R.rS + D.R.k - (a.val + 1)) (by simp only; omega)]
        exact GlobalTheory.T.hermitian_e0_symmetric_frame D X kv hgw ⟨a.val + 1, ha⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
    · rw [dif_neg ha]
      have hn : nxt X.e0 X.z0 a = X.z0 := by unfold nxt; rw [dif_neg ha]
      have hp : (⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ : Fin D.R.r) = ⟨D.R.rS + D.R.k + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [hn, hp, read X w hNi X.vectorsInLattice.2.1 _ ⟨D.R.rS + D.R.k, by omega⟩ (-1) (fun j => by
        rw [← ite_val j _ (D.R.rS + D.R.k) rfl]
        exact GlobalTheory.T.hermitian_z0_symmetric_frame D X kv hgw j), map_neg, smul_neg, ← hφ, ← map_neg, unip_inv_sup hU _ _ (by simp only),
        neg_neg]
  · by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X w
    · have hs : side X w = true := by simp [side, hE]
      rw [hs, if_pos rfl, map_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dif_pos hi]
        apply mkW_zero
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have hb : X.bwd i ∈ wLf X w := by
          have h1 := hE (X.bwd i) (X.vectorsInLattice.2.2 i).2
          have e : (1 - X.ew) • X.bwd i = X.bwd i := by
            conv_lhs => rw [X.bwd_w i]
            rw [smul_smul, sub_mul, one_mul, X.ew_orth, sub_zero, ← X.bwd_w i]
          rwa [e] at h1
        exact hA_mem_wInt X w (Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1) hb
      · rw [dif_neg hi, map_zero, map_zero]
    · have hs : side X w = false := by simp [side, hE]
      have hew := GlobalTheory.T.conj_idempotent_sub_one_mem_placeIdeal D X h hι kv hgw hE
      rw [hs, if_neg (by simp), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dif_pos hi, dif_pos hi]
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have e := GlobalTheory.St.G.FrameClose.hA_move k⁻¹ (X.bw ⟨i.val + 1, hi⟩) (X.bwd i)
        rw [inv_inv] at e
        rw [← e, ← symVec_bwd X w hE i ⟨D.R.rS + D.R.k - 1 - i.val, by omega⟩ rfl,
          read X w hNi (X.vectorsInLattice.2.2 _).1 _ ⟨D.R.rS + D.R.k - 2 - i.val, by omega⟩ 1 (fun j => by
            rw [← ite_val j _ (D.R.rS + D.R.k - 1 - (i.val + 1)) (by simp only; omega)]
            exact GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt D X kv hgw hE hew ⟨i.val + 1, hi⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
      · rw [dif_neg hi, dif_neg hi, map_zero, map_zero, map_zero]

end GlobalTheory.Mem.SymChar.ResBar
