import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInertStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

namespace GlobalTheory.KerInert

open scoped TensorProduct

theorem npow_zpow {q : ℕ} (hq : q ≠ 0) (r : ℝ≥0) (m : ℤ) (hr : (r : ℝ) = (q : ℝ) ^ (-(2 * m))) (t : ℂ) :
    GlobalTheory.Doubling.npow r t = (q : ℂ) ^ (-(2 * (m : ℂ) * t)) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by rw [hr]; exact_mod_cast (zpow_pos h0 _).ne'
  rw [GlobalTheory.Doubling.npow, Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hq),
    ← Complex.ofReal_log r.coe_nonneg, hr, Real.log_zpow, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem exists_isSphSec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (μ : (AF F ⊗[F] E)ˣ →* Circle)
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (hq : qV F v ≠ 0) {s : ℂ} {φ : GLoc σ Q v → ℂ} (h1 : φ ∈ degPSFin σ Q L v (charAt μ v) s)
    (h2 : ∀ k ∈ KFin σ Q L v, ∀ g, φ (g * k) = φ g) (h3 : φ 1 = 1)
    {c : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) :
    ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV F v) n (locChar μ w) s Φ ∧
      ∀ y, φ (ioH _ σ hQ (y, 1)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) := by
  obtain ⟨f, hK, hio, hP, ha⟩ := GlobalTheory.T.exists_doubling_chart_inert_place F E σ hc n J hJ Q hQ L v w h hw c e he
  refine ⟨fun g => φ (f.symm g), fun p k hk => ?_, fun y => ?_⟩
  · have hp : f.symm p ∈ siegelH (Fv F v) σ Q := (hP _).2 (by rw [f.apply_symm_apply]; exact p.2)
    have hk' : f.symm k ∈ KFin σ Q L v := (hK _).2 (by rwa [f.apply_symm_apply])
    have e1 := (mem_degPSH.1 h1).1 ⟨_, hp⟩ 1
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (GlobalTheory.LFun.toCompl h).toMonoidHom (aH _ σ Q ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (f.apply_symm_apply _).symm)).trans (ha ⟨_, hp⟩ ((hP _).1 hp))
    rw [mul_one, h3, mul_one, GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert F E μ v w h hw, npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hc v w h hw _)] at e1
    show φ (f.symm (p * k)) = _
    rw [map_mul, h2 _ hk', e3]
    exact e1
  · show _ = φ (f.symm _)
    rw [← hio y, f.symm_apply_apply]

theorem sphSec_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ (v : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χ w → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : (w.adicCompletion D.host.E)ˣ) (e : Gv A v ≃* GU c A.rank), IsUnramInv (ϖ : w.adicCompletion D.host.E) c (qV D.host.F v) → IsInertChart D.sp.cm.sig A.gram L h c e → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr (locChar χ⁻¹ w) ∧ locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ ∧ ((locChar χ⁻¹ w ϖ : ℂˣ) : ℂ) = (-1) ^ b ∧ ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV D.host.F v) A.rank (locChar χ⁻¹ w) s Φ ∧ ∀ y, φ (ioAt A v y) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c A.rank (e y)) := by
  intro D A L hL χ b hχ v w h hw hu s φ hφ c ϖ e hU he
  have h2 : locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ :=
    (hu.inv.locChar_eq_val hU.2.2.2.1).trans (GlobalTheory.LFun.val_inv χ w)
  have hq : qV D.host.F v ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  refine ⟨hu.inv, h2, ?_, exists_isSphSec (isCMExt_host D) (isHermND_gram A) (gram_hdbl A) L hL.1 χ⁻¹ h hw hq
    hφ.1 hφ.2.1 hφ.2.2 he⟩
  rw [h2, ((GlobalTheory.LFun.resEta_iff χ b).1 hχ).val_of_isInertAt (isCMExt_host D).2.2.1 hw hu, ← inv_pow, inv_neg_one]
  simp

end GlobalTheory.KerInert
