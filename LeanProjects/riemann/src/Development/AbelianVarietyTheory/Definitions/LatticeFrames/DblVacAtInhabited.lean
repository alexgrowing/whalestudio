import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsParamVecOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule

noncomputable section

namespace GlobalTheory.Core.Rk.SW.Model

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

theorem exists_isSkewOne (D : D7) (n : ℕ) : ∃ κ 𝓒, IsSkewOne (D := D) (n := n) κ 𝓒 := by
  obtain ⟨κ, 𝓒, h1, -, h2, h3⟩ := GlobalTheory.SkewVol.exists_haar_covol_one D n
  exact ⟨κ, 𝓒, h1, h2, h3⟩

theorem exists_split (D : D7) : ∃ q : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q := by
  have h2 : ¬ IsUnit (2 : 𝓞 D.host.F) := fun h => by
    have h' := h.map (Algebra.norm ℤ)
    rw [show (2 : 𝓞 D.host.F) = algebraMap ℤ _ 2 by simp, Algebra.norm_algebraMap] at h'
    have h3 := (isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 D.host.F)).ne').1 h'
    exact absurd (Int.isUnit_iff.1 h3) (by decide)
  obtain ⟨M, hM, hle⟩ := exists_max_ideal_of_mem_nonunits h2
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, GlobalTheory.Core.Rk.IP.Model.isSplit_two _ hle⟩
  rw [h, Ideal.mem_bot] at hle
  exact two_ne_zero hle

theorem exists_dbl_vacAt (A B : HSp D) (hA : A.SigOK) (hB : B.SigOK) (h1 : 1 ≤ A.rank) (h2 : A.rank + 2 ≤ B.rank)
    (hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) :
    ∃ ψ χB omh a ν 𝓨 mH κ 𝓒 f, Dbl ψ A B χB omh a ν 𝓨 mH κ 𝓒 f ∧ swSec A B omh ν 𝓨 f 1 = 1 ∧
      sch ψ A B ν 𝓨 f 0 = 1 ∧
      ∀ q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → VacAt ψ A B χB omh (frameLat B) q f := by
  obtain ⟨ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, hP, hΦ, hone, hU⟩ :=
    GlobalTheory.Core.Rk.IP.Model.exists_pair_unram A B hA hB h1 (t := B.rank - A.rank) (by omega) (by omega) _ _
      (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat B)
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨omh, homh⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hP.weil.std (dblSp A) B 1 χB ⟨η, hη⟩
    ⟨continuous_const, fun _ => rfl⟩ hP.weil.hecT (by
      have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
      rwa [two_mul] at this) hP.weil.resT
  obtain ⟨κ, 𝓒, hκ⟩ := exists_isSkewOne D A.rank
  have hev : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero A B ν 𝓕 (delta A B Φ Φ) = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta]
    simpa only [wcoef, Prod.mk_one_one, map_one, Module.End.one_apply] using hone
  refine ⟨ψ, χB, omh, a, ν, 𝓕, Measure.haar, κ, 𝓒, delta A B Φ Φ,
    ⟨h1, h2, hw, homh, hP.maj, hP.covol, inferInstance, hκ,
      GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hP.weil.std Φ Φ hΦ.1 hΦ.1,
      delta_isKFinVec D ψ θ A B χA χB sA sB _ cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ⟩, ?_, ?_, fun q hq =>
    ⟨hq, fun w _ => (hU ∅).unr w (by simp [LFun.above]), (hU ∅).sdB, ?_,
      VacFix.main D ψ A B χB omh homh _ _ ∅ Φ Φ hΦ.1 hΦ.1 (hU ∅) q (by simp)⟩⟩
  · simpa only [swSec, Prod.mk_one_one, map_one, Module.End.one_apply] using hev
  · rw [sch, mixS_dblDec_zero, hev]
  · exact (GlobalTheory.Core.Rk.VacBox.doubling_isLatVac D ψ A B _ _ hP.weil.std (hU ∅).sdA).2 ∅ Φ Φ (hU ∅).sph₁ (hU ∅).sph₂ q
      (by simp)

theorem dbl_vacAt_inhabited (D : D7) {n t : ℕ} (hn : 1 ≤ n) (ht : 2 ≤ t) :
    ∃ (A B : HSp D) (ψ : _) (χB : _) (omh : _) (a : _) (ν : _) (𝓨 : _) (mH : _) (κ : _) (𝓒 : _) (f : _) (q : _),
      A.rank = n ∧ B.rank = n + t ∧ Dbl ψ A B χB omh a ν 𝓨 mH κ 𝓒 f ∧ swSec A B omh ν 𝓨 f 1 = 1 ∧
      VacAt ψ A B χB omh (frameLat B) q f := by
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (n + t)
  obtain ⟨q, hq⟩ := exists_split D
  obtain ⟨ψ, χB, omh, a, ν, 𝓨, mH, κ, 𝓒, f, h1, h2, -, h3⟩ := exists_dbl_vacAt A B (Examples₂.posSpace_sigOK _ _)
    (Examples₂.posSpace_sigOK _ _) hn (show n + 2 ≤ n + t by omega)
    (.inl (wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace _)))
  exact ⟨A, B, ψ, χB, omh, a, ν, 𝓨, mH, κ, 𝓒, f, q, rfl, rfl, h1, h2, h3 q hq⟩

theorem exists_isWeyl (A : HSp D) : ∃ w, IsWeyl A w ∧ lowC A w = 1 := by
  have h : HypDec.Images (dblSp A) (zeroSp D) (dblDec A).jY (dblDec A).j0 (dblDec A).jX :=
    ⟨(dblDec A).gram_YY, (dblDec A).gram_XX, (dblDec A).gram_XY, (dblDec A).gram_00, (dblDec A).gram_0Y,
      (dblDec A).gram_0X⟩
  refine ⟨(dblDec A).ofImages _ _ _ h, ⟨(dblDec A).ofImages_mem_GQ h (rat_mem _) (rat_mem _) (rat_mem _), ?_⟩, ?_⟩
  · rw [(dblDec A).ofImages_jY h, HypDec.pY_jX]
  · rw [lowC, (dblDec A).ofImages_jX h, HypDec.pY_jY]

theorem lowC_one (A : HSp D) : lowC A 1 = 0 := by rw [lowC, mt_one, Matrix.one_mul, HypDec.pY_jX]

theorem lowC_mul_nC (A : HSp D) (g : GA D (dblSp A)) (c : skewA D A.rank) : lowC A (g * (dblDec A).nC c) = lowC A g := by
  rw [lowC, lowC, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jX]

theorem chr_gramOf (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (x : Mx D B.rank A.rank) (c : skewA D A.rank) :
    chr ψ (gramOf B x) c = ψ ((dblDec A).qS B c x) := by
  rw [chr, HypDec.qS, HypDec.symplOH_extX_extY, pairS, adj_mul, mem_skewA.1 c.2, Matrix.mul_assoc, Matrix.neg_mul,
    Matrix.trace_neg, map_neg (trHalf D), Matrix.trace_mul_comm, gramOf]

theorem laws_of_formulas {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χB : (AE D)ˣ →* Circle} {omh : WRep (dblSp A) B}
    {om₀ : WRep (zeroSp D) B} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} {f : WO (dblSp A) B → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS (dblDec A) ψ χB omh om₀ ν 𝓨 f) :
    (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x =
      ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧
    ∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x := by
  refine ⟨fun m x => ?_, fun c x => ?_⟩
  · rw [sch, h.levi, Pi.smul_apply, smul_eq_mul, MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, GlobalTheory.Doubling.npow,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    push_cast
    rfl
  · rw [sch, h.centre, chr_gramOf ψ A B]
    rfl

theorem chr_add (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ} (T : Mx D n n) (c c' : skewA D n) :
    chr ψ T (c + c') = chr ψ T c * chr ψ T c' := by
  rw [chr, chr, chr, ← AddChar.map_add_eq_mul, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]

theorem nsAt_of_norm {par : LFun.Fam D.host.E} (χ : (AE D)ˣ →* Circle) {t : ℕ} {q : FinPl D}
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = q → ∀ β ∈ par w, ∃ j : ℤ, |j| < (t : ℤ) - 1 ∧
      ‖(β : ℂ)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((j : ℝ) / 2)) : NSAt par χ t q := by
  intro w hw β hβ k hk e
  obtain ⟨j, hj, hn⟩ := h w hw β hβ
  have e' := congrArg norm e
  rw [norm_mul, norm_inv, LFun.norm_val, inv_one, mul_one, hn, LFun.norm_npow] at e'
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have h3 := (Real.rpow_right_inj (by linarith) hN.ne').1 e'
  have h4 : (j : ℝ) = k := by
    have : ((k : ℂ) / 2).re = (k : ℝ) / 2 := by simp
    rw [this] at h3
    linarith
  have h5 : j = k := by exact_mod_cast h4
  subst h5
  rw [abs_lt] at hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  omega

theorem not_nsAt (χ : (AE D)ˣ →* Circle) (t : ℕ) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ par : LFun.Fam D.host.E, ¬ NSAt par χ t (w.under (𝓞 D.host.F)) := by
  refine ⟨fun w => {Units.mk0 _ (LFun.npow_ne_zero w ((((t : ℤ) + 1 : ℤ) : ℂ) / 2)) * LFun.val (F := D.host.F) χ w},
    fun h => h w rfl _ (Multiset.mem_singleton_self _) ((t : ℤ) + 1) (by simp) ?_⟩
  rw [Units.val_mul, Units.val_mk0, mul_inv_cancel_right₀ (Units.ne_zero _)]

theorem nsAt_one (A : HSp D) (χ : (AE D)ˣ →* Circle) {t : ℕ} (ht : A.rank < t) {q : FinPl D}
    (hq : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q) : ∃ par,
      LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) ({q}ᶜ : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧ NSAt par χ t q := by
  refine ⟨fun w => Finset.univ.val.map (TrivCoef.trivParGL w A.rank), fun v hv w h => ?_, nsAt_of_norm χ fun w _ β hβ => ?_⟩
  · obtain rfl : v = q := by simpa using hv
    have hL := isLattice_frameLat_host A
    obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) (isHermND_gram A) hL.fg hL.span_eq_top h hq
      (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D A v)
    exact Or.inl ⟨hq, e, he, (TrivCoef.isSatVecGL_one w A.rank).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl)
      fun e => one_ne_zero (congrFun e 1)⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
    have hi := i.2
    refine ⟨(A.rank : ℤ) - 1 - 2 * (i.val : ℤ), by rw [abs_lt]; omega, ?_⟩
    have := LFun.norm_npow w (((A.rank : ℂ) - 1 - 2 * (i : ℂ)) / 2)
    refine Eq.trans this ?_
    congr 1
    simp

end GlobalTheory.Core.Rk.SW.Model

end
