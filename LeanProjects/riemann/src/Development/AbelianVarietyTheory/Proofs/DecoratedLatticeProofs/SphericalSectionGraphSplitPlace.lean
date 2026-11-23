import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletioStatement

noncomputable section

namespace GlobalTheory.Core.Rk.KerSplit

section General

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LFun
open Formalism.UG (ordL)
open Formalism.L2.Host (atFin unif unif_spec IsUnifAt IsUnitAt)

theorem locChar_eq_val_zpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ : (AF F ⊗[F] E)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (y : (w.adicCompletion E)ˣ) :
    locChar χ w y = val χ w ^ ordL y.1 := by
  have hy : Valued.v y.1 ≠ 0 := by simp
  have h0 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dif_neg hy, neg_neg]
    exact (WithZero.coe_unzero hy).symm
  have h1 : IsUnitAt w (y * (atFin w (unif w)) ^ (-ordL y.1)) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, this, ← WithZero.exp_zsmul]
    nth_rewrite 1 [h0]
    rw [← WithZero.exp_add]
    simp
  have := h _ h1
  rwa [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at this

theorem npow_zpow_neg {r : ℝ≥0} {q : ℕ} {m : ℤ} (h : (r : ℝ) = (q : ℝ) ^ (-m)) (z : ℂ) :
    GlobalTheory.Doubling.npow r z = (q : ℂ) ^ (-z * (m : ℂ)) := by
  rw [GlobalTheory.Doubling.npow, h, Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast,
    ← Complex.cpow_mul]
  · congr 1; push_cast; ring
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos]
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos.le]

open GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.UG in
set_option maxHeartbeats 800000 in

theorem char_value {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {χ : (AF F ⊗[F] E)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 F)}
    {w w' : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (hall : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') (hU : UnrAt χ w) (hU' : UnrAt χ w')
    (hm : val χ w * val χ w' = 1) {n : ℕ} (d : Fin n → ℤ) (x : (Fv F v ⊗[F] E)ˣ)
    (o1 : ordL (toCompl h x.1) = ∑ i, max (d i) 0) (o2 : ordL (toCompl h' x.1) = -∑ i, min (d i) 0) (z : ℂ) :
    ((charAt χ⁻¹ v x : Circle) : ℂ) * GlobalTheory.Doubling.npow (absEv F E v x) z =
      (((val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-z * ((∑ i, |d i| : ℤ) : ℂ)) := by
  have habs := GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow _ _ _ hc v w h w' h' hne x
  have hch := GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split _ _ χ⁻¹ v w h w' h' hne hall x
  have s1 : ∑ i, max (d i) 0 + -∑ i, min (d i) 0 = ∑ i, |d i| := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [abs_eq_max_neg]; omega
  have s2 : ∑ i, max (d i) 0 + ∑ i, min (d i) 0 = ∑ i, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  rw [o1, o2, s1] at habs
  rw [locChar_eq_val_zpow hU.inv, locChar_eq_val_zpow hU'.inv, val_inv, val_inv, ← Units.val_mul] at hch
  change _ = (((val χ w)⁻¹ ^ ordL (toCompl h x.1) * (val χ w')⁻¹ ^ ordL (toCompl h' x.1) : ℂˣ) : ℂ) at hch
  rw [o1, o2, eq_inv_of_mul_eq_one_right hm, inv_inv, zpow_neg (val χ w), ← inv_zpow, ← zpow_add, s2,
    Units.val_zpow_eq_zpow_val] at hch
  rw [hch, npow_zpow_neg habs]

end General

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

set_option maxHeartbeats 1600000 in

theorem sphSec_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w A.rank, ∀ k₂ ∈ KGL w A.rank, φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  intro D A L hL χ b hχ v hv hU s φ hφ w h e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  haveI := hL.1
  have hc := isCMExt_host D
  obtain ⟨w', hne, hall, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hc h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val hc.2.2.1 ((GlobalTheory.LFun.resEta_iff χ _).1 hχ) hne h h' (hU w h) (hU w' h')
  obtain ⟨f, hfK, hfi, hfP, hfa⟩ := GlobalTheory.T.exists_doubled_unitary_chart_split_place _ _ _ hc A.rank A.gram (GlobalTheory.Doubling.isHermND_gram A) (dblSp A).gram
    (gram_hdbl A) L v w h hv (IwSplit.isSelfDualAt_of_isSelfDualC hL v) e he
  obtain ⟨κ, hκ, hP, hl, hq⟩ := GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion _ w A.rank ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hp : f (ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ) = blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ := by
    rw [map_mul, f.apply_symm_apply, ioAt, hfi, e.apply_symm_apply, map_one]
  rw [← hp] at hP hl hq
  rw [← hφ.2.1 (f.symm κ) ((hfK _).2 (by rwa [f.apply_symm_apply]))]
  generalize ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ = g at hP hl hq ⊢
  obtain ⟨ha, ha'⟩ := hfa ⟨g, (hfP g).2 hP⟩
  have ha' := ha' w' h' hne
  have law := (mem_degPSH.1 hφ.1).1 ⟨g, (hfP g).2 hP⟩ 1
  generalize aH _ D.sp.cm.sig (dblSp A).gram ⟨g, (hfP g).2 hP⟩ = x at ha ha' law
  have o1 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h x.1) = ∑ i, max (d i) 0 := by rw [ha]; exact hl
  have o2 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h' x.1) = -∑ i, min (d i) 0 := by rw [ha']; exact congrArg _ hq
  rw [mul_one, hφ.2.2, mul_one] at law
  refine law.trans ?_
  rw [add_comm ((A.rank : ℂ) / 2) s]
  exact char_value hc h h' hne hall (hU w h) (hU w' h') hm d x o1 o2 _

end GlobalTheory.Core.Rk.KerSplit
