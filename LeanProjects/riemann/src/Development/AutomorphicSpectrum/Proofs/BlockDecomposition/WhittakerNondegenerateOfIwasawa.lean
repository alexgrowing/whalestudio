import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpperLeftBlockMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

set_option maxHeartbeats 4000000 in
theorem whit_step (hK : WhitKA) {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) (hR : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hC : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0)
    (a : GL (Fin n) (AE D)) {m u k : G D n} (hk : k ∈ K D n) (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    (b1 : hermA D n) (hu : mat u = blk4 1 b1.1 0 1) :
    HolValueAt (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
      (s0 V n) (IfrB V ν (ω (m * u * k) Φ).1 β) := by
  have hω := hS.hω
  have hH := hS.hH
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hμ : μ.IsAddHaarMeasure := h𝓕.1
  have hl : lam.IsAddHaarMeasure := hC.2.1
  have hnb : IsNMap nb := hC.1
  have hub : u = nb b1 := mat_inj (by rw [hnb b1]; exact hu)
  set A := absA D (Matrix.GeneralLinearGroup.det a) with hAdef
  have hA : 0 < A := absA_pos _
  obtain ⟨m', hm'P, hm'⟩ := exists_ad a
  have hwm : w * m = m' * w := weyl_mul hw a hm hm'
  have hblk : blkA (mat m') = (ad a).1 := by rw [hm', upperLeft_blockMatrix]; rfl
  set φ0 : schwartzA θ V.rank n := ω k Φ with hφ0
  have hωe : ω (m * u * k) Φ = ω (m * u) φ0 := by
    rw [map_mul (f := ω) (m * u) k]; rfl
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT
  set ct : ℂ := ψ (halfTr (Matrix.trace (T * b1.1))) with hct
  set c0 : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow A ((V.rank : ℂ) / 2) with hc0
  have hpt : ∀ (z : ℂ) (b' : hermA D n),
      npow (H (w * nb (cg a (b' - b1)) * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
      (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        (npow (H (w * nb b' * k)) (z - s0 V n) * Jt ψ V μ φ0.1 b' *
          ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n)))) := by
    intro z b'
    have e : w * nb (cg a (b' - b1)) * (m * u * k) = m' * (w * nb b' * k) := by
      calc _ = w * (nb (cg a (b' - b1)) * m) * u * k := by simp only [mul_assoc]
        _ = w * (m * nb (b' - b1)) * u * k := by rw [nb_cg_mul hnb a hm]
        _ = (w * m) * (nb (b' - b1) * nb b1) * k := by rw [hub]; simp only [mul_assoc]
        _ = m' * w * nb b' * k := by rw [hwm, ← nb_add hnb, sub_add_cancel]
        _ = _ := by simp only [mul_assoc]
    have hHe : H (w * nb (cg a (b' - b1)) * (m * u * k)) = A⁻¹ * H (w * nb b' * k) := by
      rw [e, height_mul hH hm'P (ad a) hblk, absA_ad]
    have hJ : Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) = c0 * (npow A (-(V.rank : ℂ)) * Jt ψ V μ φ0.1 b') := by
      rw [hωe, jt_step hω hμ a hm hu φ0 (b' - b1), sub_add_cancel]
    have e1 : Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n) =
        Matrix.trace (T * (b' - b1).1) := trace_beta a _ _
    have e2 : Matrix.trace (T * (b' - b1).1) = Matrix.trace (T * b'.1) + -Matrix.trace (T * b1.1) := by
      have : (b' - b1).1 = b'.1 - b1.1 := rfl
      rw [this, Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg]
    have hch : ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
        ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n))) * ct := by
      rw [e1, e2, halfTr_add, halfTr_neg, neg_add, neg_neg, AddChar.map_add_eq_mul]
    rw [hHe, hJ, hch, npow_mul', npow_inv' hA, show -(z - s0 V n) = s0 V n - z from neg_sub z (s0 V n)]
    ring
  have hint : ∀ z : ℂ, (∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam) =
      npow A (s0 V n - z) * ((npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        whitT ψ V μ lam nb w H φ0.1 T k z) := by
    intro z
    set Gz : hermA D n → ℂ := fun b => npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hGz
    have h1 : ∫ c, Gz (cg a c) ∂lam = npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a Gz
    have h2 : ∫ x, Gz (cg a (x - b1)) ∂lam = ∫ c, Gz (cg a c) ∂lam :=
      integral_shift_herm lam hl (fun c => Gz (cg a c)) b1
    have h3 : ∫ x, Gz (cg a (x - b1)) ∂lam =
        (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) * whitT ψ V μ lam nb w H φ0.1 T k z := by
      simp only [hGz, hpt, integral_const_mul]
      rfl
    have h4 : npow A (n : ℂ) * npow A (-(n : ℂ)) = 1 := by
      rw [← npow_add' hA, add_neg_cancel, npow_zero' A hA]
    rw [h3, h1] at h2
    calc ∫ b, Gz b ∂lam = (npow A (n : ℂ) * npow A (-(n : ℂ))) * ∫ b, Gz b ∂lam := by rw [h4, one_mul]
      _ = npow A (n : ℂ) * (npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam) := by ring
      _ = _ := by rw [← h2]; ring
  have h0 := hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  have hc := (holValueAt_const (npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) (s0 V n)).mul h0
  have hfin := holValueAt_npow_sub_mul _ (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) *
      Jt ψ V μ (ω (m * u * k) Φ).1 b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
    (s0 V n) _ A 0 hA hc (fun z _ => hint z)
  have hval : npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β) = IfrB V ν (ω (m * u * k) Φ).1 β := by
    have h5 : npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n) = 1 := by
      rw [← npow_add' hA, ← npow_add' hA]
      have : (n : ℂ) + -(V.rank : ℂ) + ((V.rank : ℂ) - n) = 0 := by ring
      rw [this, npow_zero' A hA]
    have h6 : ψ (halfTr (Matrix.trace (b1.1 * T))) = ct := by
      rw [hct, Matrix.trace_mul_comm]
    rw [hωe, ifrB_step hω ν a hm hu φ0 β, ← hAdef, ← hT, ← hc0, h6]
    calc _ = (npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n)) * (c0 * ct *
            IfrB V ν (fun x => φ0.1 (HMul.hMul x a.1)) β) := by ring
      _ = _ := by rw [h5, one_mul]
  rw [hval] at hfin
  exact hfin

theorem iwaRedA : GlobalTheory.CompanionTheory.IwaAd.WhitKA → PositivityTheory.PfSWUS.WhitNDg := by
  intro hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨m, u, b, rfl, hm, hu⟩ := exists_levi_unip hp a ha
  have hbh : adj b = b := (exists_unip b).1 ⟨u, hu⟩
  exact whit_step hK hS hR hC hw hβ a hk hm ⟨b, hbh⟩ hu

end GlobalTheory.CompanionTheory.IwaAd
