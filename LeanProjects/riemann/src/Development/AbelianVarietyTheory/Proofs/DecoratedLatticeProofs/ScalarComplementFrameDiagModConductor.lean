import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdempStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefereStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNearStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalActionStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

set_option maxHeartbeats 800000 in
theorem scalar_diag_mod_g : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  intro D X u β hβ c hc hN
  have hg1 : 1 ≤ X.B.g := Formalism.L2.SG.PoincareInHH.Cut.one_le_g X
  obtain ⟨M6, hM6, hz6⟩ := GlobalTheory.T.exists_coprime_multiplier_one_sub_norm_congr_zero D X u
  have hTg : Nat.Coprime (D.mem u).A.T X.B.g := GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level X.B.I X.B.g _ M6 hg1 hM6 hz6
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  obtain ⟨Mb, hMb, hb7⟩ := GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference D X
  obtain ⟨Mc, hMc, hc7⟩ := GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near D X u
  have hc' : c.1 * sigA X.B.I c.1 = 1 := by
    have := congrArg Subtype.val hc
    simpa [sigInt_coe] using this
  obtain ⟨hfix, hfz, hidem⟩ := GlobalTheory.T.orthProjHyperbolicNegativeSpan_fixes_basis_and_idempotent D X u
  obtain ⟨h, hh, hhi⟩ := GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent X.B.I (GlobalTheory.ScalW.prjM X u) c.1
    (fun y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, hidem])
    (fun x y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint]) hc'
  have hh' : X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c.1 := hh
  have hhi' : X.B.I.fmat h⁻¹ = GlobalTheory.ScalW.hMat X u (sigA X.B.I c.1) := hhi
  obtain ⟨hH, hcomm⟩ := GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes D X u c.1 h hfix hfz hh'
  obtain ⟨hP0, hfl⟩ := GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level D X

  set P' : VA X.B.I → VA X.B.I := fun y => X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y)
    with hP'
  set M := Mb * Mc * M6 * (D.mem u).A.T with hMdef
  have hMg : Nat.Coprime M X.B.g := ((hMb.mul hMc).mul hM6).mul hTg
  have smulL : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ X.B.I.Lf → s • y ∈ X.B.I.Lf := fun hs _ hy => X.B.I.Lf.smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have smulM : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ mL X.B.I X.B.g → s • y ∈ mL X.B.I X.B.g := fun hs _ hy => (mL X.B.I X.B.g).smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have hnear : ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro y hy
    rw [hP']
    beta_reduce
    rw [GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq]
    simp only [GlobalTheory.ScalW.prj0]
    have hA1 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) -
        ∑ a, hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).1
    have hA2 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) -
        ∑ a, hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).2
    have hZ := hc7 y hy
    have hw0 : hA X.B.I X.z0 y • X.z0 ∈ X.B.I.Lf :=
      X.B.I.Lf.smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int X.vectorsInLattice.2.1 hy⟩ : IntAf X.B.I.F X.B.I.E) X.vectorsInLattice.2.1
    have hW : ((M6 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) •
        (hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X hz6 hw0
    have hTd : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) =
        hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y := Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I _ hT0 _
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) = S1 at hA1 ⊢
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) = S2 at hA2 ⊢
    generalize (∑ a, hA X.B.I (X.f0 a) y • X.e0 a) = S3 at hA1 ⊢
    generalize (∑ a, hA X.B.I (X.e0 a) y • X.f0 a) = S4 at hA2 ⊢
    generalize X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u = z' at hZ hTd ⊢
    generalize divN X.B.I (D.mem u).A.T (hA X.B.I z' y) = dd at hTd ⊢
    generalize hA X.B.I X.z0 y • X.z0 = w0 at hZ hW ⊢
    rw [← hTd] at hZ
    rw [hMdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, GlobalTheory.ScalW.scalW_ident]
    have hN' : ∀ m : ℕ, (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E := fun m => natCast_mem _ m
    exact sub_mem (sub_mem (add_mem (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA1)
      (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA2)) (smulM (mul_mem (hN' _) (hN' _)) hZ))
      (smulM (mul_mem (hN' _) (hN' _)) hW)
  have key : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, ZMod' X.B.I M (1 - s) → ∀ y ∈ X.B.I.Lf,
      (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro s hzs y hy
    obtain ⟨t, ht, e⟩ := hzs
    rw [e, mul_comm, mul_smul]
    exact smulM ht (hnear y hy)
  have hint : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, s ∈ IntAf X.B.I.F X.B.I.E → ZMod' X.B.I M (1 - s) →
      ∀ y ∈ X.B.I.Lf, s • y + (1 - s) • P' y ∈ X.B.I.Lf := by
    intro s hs hzs y hy
    have e : s • y + (1 - s) • P' y = s • y + (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) + (1 - s) • GlobalTheory.ScalW.prj0 X y := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (add_mem (smulL hs hy) (GlobalTheory.St.G.FrameClose.mL_le _ (key s hzs y hy)))
      (smulL (sub_mem (one_mem _) hs) (hP0 y hy))
  have hact : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.Gf), X.B.I.fmat k = GlobalTheory.ScalW.hMat X u s →
      ∀ y, X.B.I.fmat ((X.xu u)⁻¹ * k * X.xu u) *ᵥ y = s • y + (1 - s) • P' y := by
    intro s k hk y
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hk,
      GlobalTheory.ScalW.hMat_mulVec, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec,
      Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul, one_mulVec]
  have hcM : ZMod' X.B.I M (1 - c.1) := hN M hMg
  have hsM : ZMod' X.B.I M (1 - sigA X.B.I c.1) := by
    have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I M hcM
    rwa [map_sub, map_one] at this
  have hinvY : ((X.xu u)⁻¹ * h * X.xu u)⁻¹ = (X.xu u)⁻¹ * h⁻¹ * X.xu u := by group
  set d : Fin X.B.I.n → Formalism.L2.Herm.intAf X.B.I.F X.B.I.E :=
    fun i => if D.R.rS ≤ i.val ∧ i.val < D.R.rS + D.R.k then c else 1 with hd
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action X.B.I X.B.g _ β ((X.xu u)⁻¹ * h * X.xu u) d hβ
    (fun y hy => by rw [hact _ h hh']; exact hint _ c.2 hcM y hy)
    (fun y hy => by
      rw [hinvY, hact _ _ hhi']
      exact hint _ (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I c.2) hsM y hy)
    (fun j => by
      obtain ⟨hbL, hW, hnW⟩ := hfl j.val
      rw [hact _ h hh']
      have hk := key c.1 hcM _ hbL
      by_cases hj : D.R.rS ≤ j.val ∧ j.val < D.R.rS + D.R.k
      · have e1 : (d j).1 = c.1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          rw [smul_sub]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hW hj))
      · have e1 : (d j).1 = 1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • (GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hnW hj)))
  refine ⟨h, hH, hcomm, x, hx1, fun i j => ?_⟩
  have e : midDiag X.B.I.n D.R.rS D.R.k 1 c = Matrix.diagonal d := by
    simp only [midDiag, hd]
  rw [e]
  exact hx2 i j

end GlobalTheory.ScalW
