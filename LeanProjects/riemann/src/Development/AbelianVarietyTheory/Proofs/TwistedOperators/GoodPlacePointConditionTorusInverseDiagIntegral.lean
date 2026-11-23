import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLineStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAllStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.FinPl.PtInv

variable {D : D7}

theorem pairS_jX_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (N : Mx D ρ ρ) (i : Fin ρ) (b : AE D) :
    pairS W (dW.jX ⬝ N) (dW.jY ⬝ Matrix.single i i b) = cA D b * N i i := by
  rw [pairS, adj_mul, GlobalTheory.FinPl.InvStep.adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W),
    ← Matrix.mul_assoc (adj dW.jY), HypDec.gram_YX, Matrix.one_mul, GlobalTheory.FinPl.InvStep.trace_single_mul]

theorem pairS_add_left {W : HSp D} {ρ : ℕ} (x x' y : Mx D W.rank ρ) :
    pairS W (x + x') y = pairS W x y + pairS W x' y := by
  simp only [pairS, Matrix.mul_add, Matrix.trace_add]

theorem symplO_off {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) {v : Pl D} {M : Mx D W.rank ρ}
    (hM : GlobalTheory.AscFin.MxOff (· = v) M) (y : Mx D W.rank ρ) (hy : MxAt (· = v) (dV.extY W y)) :
    symplO V W (dV.extX W M) (dV.extY W y) = 0 := by
  have hfix : SelfDualAt.cP (· = v) • dV.extY W y = dV.extY W y := by
    ext k l
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact SuppShift.eps_mul (hy k l)
  have h0 : SelfDualAt.cP (· = v) • dV.extX W M = dV.extX W 0 := by
    ext k l
    rw [map_zero, Matrix.zero_apply, Matrix.smul_apply, Algebra.smul_def, HypDec.extX_apply, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    have h : M k m * algebraMap (AF D.host.F) (AE D) (SelfDualAt.cP (· = v)) = 0 :=
      GlobalTheory.DisjComb.mul_eq_zero_of_off (hM k m) (SuppShift.eps_idAt v)
    rw [← mul_assoc, mul_comm (algebraMap _ _ _), h, zero_mul]
  rw [← hfix, SelfDualAt.symplO_smul_swap, h0, InvStep.symplO_extX_extY]
  simp [pairS]

set_option maxHeartbeats 1600000 in

theorem inv_int_of_pt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∃ u : UX D ρ, ∃ a ∈ p.A₁, GlobalTheory.AscFin.MxOff (· = v) (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a)) → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t htd ht hpt i
  obtain ⟨-, h2, -⟩ := InvStep.diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := InvStep.levi_sub_one_mem dW (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  obtain ⟨u, a, ha, hoff⟩ := hpt
  obtain ⟨b₀, hab, hb₀⟩ := hS.a' a ha
  have hlev : mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) = dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1) := by
    rw [← map_inv dW.levi t, ← Matrix.mul_assoc, xZero, HypDec.levi_jX, Matrix.mul_assoc]
  have hu1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
  have hdiag : ((t⁻¹).1 ⬝ u.1.1) i i = (t⁻¹).1 i i := by
    conv_lhs => rw [h2]
    rw [diagonal_mul, hu1, mul_one]
  have hsum : dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1) = (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) + (a - b₀) + b₀ + dW.jX ⬝ (1 : Mx D ρ ρ) := by
    rw [hlev, Matrix.mul_one, xZero]
    abel
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v (GlobalTheory.T.isTameFinitePlaceHermitian_all D v) hG.sdV hG.sdW hG.monoV hG.monoW
    hG.cols i _ hc1 ?_
  intro b hb hY
  have hYm : MxAt (· = v) (dV.extY W (dW.jY ⬝ Matrix.single i i b)) := LatMem.latO_mxAt hY
  have hτ : ∀ M : Mx D W.rank ρ, ψ (symplO V W (dV.extX W M) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W M (dW.jY ⬝ Matrix.single i i b))) := fun M => by
    rw [InvStep.symplO_extX_extY]
  have e : cA D b * (t⁻¹).1 i i = pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b) + pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b) + pairS W b₀ (dW.jY ⬝ Matrix.single i i b) +
      pairS W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b) := by
    calc cA D b * (t⁻¹).1 i i = pairS W (dW.jX ⬝ ((t⁻¹).1 ⬝ u.1.1)) (dW.jY ⬝ Matrix.single i i b) := by rw [pairS_jX_single, hdiag]
      _ = pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b) + pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b) + pairS W b₀ (dW.jY ⬝ Matrix.single i i b) + pairS W (dW.jX ⬝ (1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b) := by
        rw [hsum, pairS_add_left, pairS_add_left, pairS_add_left]
      _ = _ := by
        rw [pairS_jX_single dW (1 : Mx D ρ ρ), pairS_jX_single dW ((Matrix.single i i 1 : Mx D ρ ρ)), Matrix.one_apply_eq, Matrix.single_apply_same]
  have k1 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ, symplO_off dV hoff _ hYm, AddChar.map_zero_eq_one]
  have k2 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (a - b₀) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ, symplO_off dV hab _ hYm, AddChar.map_zero_eq_one]
  have k3 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W b₀ (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    rw [← hτ]
    exact (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V W LV LW hG.sdV hG.sdW (· = v) _ (LatMem.latO_mxAt hb₀)).1 hb₀ _ hY
  have hlat : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V W LV LW hG.sdV hG.sdW (· = v) _).2 ⟨fun k l => ?_, fun y hy => ?_⟩
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (SuppShift.eps_idAt v)
    · have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) =
          SuppShift.eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      have ha' : SuppShift.eps v * (dV.pX *ᵥ y) i ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (SuppShift.eps_idAt v)
      have hV' : colMul dV.jX i (SuppShift.eps v * (dV.pX *ᵥ y) i) ∈ latV V LV (· = v) := by
        rw [SuppShift.colMul_mul]
        exact SuppShift.smul_latV (SuppShift.eps_int v) (((hG.monoV y).1 hy).1 i)
      have hA := (hG.cols i _ ha').1 hV'
      change (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ))) *ᵥ y ∈ _
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, SuppShift.single_mulVec', one_mul,
        ← SuppShift.colMul_mul]
      exact hA
  have k4 : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS W (dW.jX ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) (dW.jY ⬝ Matrix.single i i b))) = 1 := by
    have hfix : SelfDualAt.cP (· = v) • dV.extY W (dW.jY ⬝ Matrix.single i i b) = dV.extY W (dW.jY ⬝ Matrix.single i i b) := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact SuppShift.eps_mul (hYm k l)
    rw [← hτ, ← hfix, SelfDualAt.symplO_smul_swap]
    exact (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V W LV LW hG.sdV hG.sdW (· = v) _ (LatMem.latO_mxAt hlat)).1 hlat _ hY
  have hadd : ∀ x y : AE D, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (x + y))) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * x)) *
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * y)) := fun x y => by
    rw [mul_add, map_add, AddChar.map_add_eq_mul]
  rw [hτ, pairS_jX_single, Matrix.single_apply_same, e, hadd, hadd, hadd, k1, k2, k3, k4, one_mul, one_mul, one_mul]

end GlobalTheory.FinPl.PtInv
