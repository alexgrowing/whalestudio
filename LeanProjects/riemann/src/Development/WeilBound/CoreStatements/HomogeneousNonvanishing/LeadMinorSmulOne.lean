import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEmptyZeroPieces
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CcPreserving
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.LowerWeightVolume
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCellMongeAmpereDensityConstant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLevi
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SepCountEqFactorialDegree
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT Formalism.L2.LamCM
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem ip_unique {z : Sp ℂ ⟶ Xo.X} (Φ : FibKey Xo ℂ z) {v w : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G} {a b : ℂ}
    (ha : GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z v w a)
    (hb : GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z v w b) : a = b := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Xo.X Xo.univ.t.G ℂ z
  obtain ⟨h, hh, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H Xo.X Xo.univ.t z V M
    ⟨Φ.T.t, Φ.m, Φ.T.ab.proper, Φ.T.ample⟩
  obtain ⟨v, rfl⟩ := M.onto v ha.isTanAt_left
  obtain ⟨w, rfl⟩ := M.onto w ha.isTanAt_right
  rw [(hh _ _ _).1 ha, (hh _ _ _).1 hb]

theorem ip_of_unif {z : Sp ℂ ⟶ Xo.X} (Φ : FibKey Xo ℂ z) {g : ℕ} (u : HolUnif Φ.T.t.G Φ.T.t.PP.L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ)
    {v w : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G} {c₀ : ℂ}
    (h : GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z v w c₀) {v' w' : epsR ℂ ⟶ Φ.T.t.G} {a b : Fin g → ℂ}
    (e1 : v'.left ≫ Φ.m.φ = v.left) (e2 : w'.left ≫ Φ.m.φ = w.left) (d1 : u.IsDiff a v') (d2 : u.IsDiff b w') :
    c₀ = Real.pi * hermForm Hm b a := by
  obtain ⟨w₀, hw₀, -⟩ := Φ.m.lin
  have hL := Φ.T.t.PP.isLB
  have hM := pull_isLB Xo.univ.t.PP.isLB Φ.m.φ
  let u₁ : HolUnif Φ.T.t.G (Xo.univ.t.PP.L.pull Φ.m.φ) g := GlobalTheory.ArchMetricCompare.carry u hL hM hw₀
  have hA₁ : u₁.IsAH Hm χ := GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hA
  exact ip_unique Φ h ⟨h.1, h.isTanAt_left, h.isTanAt_right, Φ.T.t.G, inferInstance, Φ.m.φ, g, u₁, Hm, χ,
    v', w', a, b, Φ.m.cart, hA₁, e1, e2, d1, d2, rfl⟩

theorem univ_ip {k : U.Comp} {x : (U.X k).dom} (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W) (hpq : 1 ≤ Dw.p + Dw.q)
    (z : Sp ℂ ⟶ Xo.X) (hz : z = (U.un k x).x) (a b : Fin W.g → ℂ) (v w : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G) (cc₀ : ℂ)
    (hv : IsDerivAt0 (fun z => (W.F.ex (W.ik k) W.Pm z).left) a v.left)
    (hw : IsDerivAt0 (fun z => (W.F.ex (W.ik k) W.Pm z).left) b w.left)
    (h : GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z v w cc₀) : cc₀ = Real.pi * hermForm Wu.Hm b a := by
  subst hz
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, -, hA, -, -, -, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  obtain ⟨v', e1, d1⟩ := hD a v.left ⟨Over.w v, h.isTanAt_left⟩ hv
  obtain ⟨w', e2, d2⟩ := hD b w.left ⟨Over.w w, h.isTanAt_right⟩ hw
  exact ip_of_unif Φ u hA h e1 e2 d1 d2

theorem letters (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) :
    ∃ f : (Σ τ, Fin (Dw.mult τ)) ≃ (U.X k).Ψ × Fin r, (∀ s,
      (relab c σ s.1 ∈ (U.X k).Ψ ∧ (f s).1.1 = relab c σ s.1 ∧ ((f s).2 : ℕ) = (U.X k).p0 + s.2) ∨
      (relab c σ s.1 ∉ (U.X k).Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (relab c σ s.1) ∧
        ((f s).2 : ℕ) = (U.X k).p0 - 1 - s.2 ∧ (s.2 : ℕ) < (U.X k).p0)) ∧
      ∀ x v s, perFr (U.X k) x v (relab c σ s.1) s.2 = RiemMaj.pc (U.X k) x v (f s) := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  refine ⟨f, hf, fun x v s => ?_⟩
  have h := hf s
  generalize f s = t at h ⊢
  obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
  dsimp only at h ⊢
  unfold RiemMaj.pc
  rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
  · rw [if_neg (by simp)]
    unfold perFr
    rw [dif_pos a, dif_pos hn]
  · rw [if_pos (by dsimp only; omega)]
    unfold perFr
    rw [dif_neg a, dif_pos (show conjEmb (relab c σ s.1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
    rfl

theorem hm_diag (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom} (W : PullbackSections.UnfAt U k x)
    (Wu : PullbackSections.UnitAt W) (hx : (U.X k).IsOrtho x.1) :
    Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  obtain ⟨f, hf, hper⟩ := letters hσ hU k
  have key : Wu.Hm = Matrix.diagonal fun j => ((-2 * (((W.e.trans f) j).1.1 (U.X k).ξ0).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    have e : ∀ a, W.Pm a = fun j => RiemMaj.pc (U.X k) x.1 (W.φ k a : Fin r → E) ((W.e.trans f) j) :=
      fun a => funext fun j => (W.pm_eq a j).trans (hper _ _ _)
    rw [Wu.c1, e, e, RiemMaj.im_diag (U.X k) (W.e.trans f) hx, ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, -2 * (((W.e.trans f) j).1.1 (U.X k).ξ0).im = 2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rw [Equiv.trans_apply]
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [h]
      · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    rw [hn]
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    rw [← Complex.abs_im_eq_norm.mpr (RiemMaj.re_xi (U.X k) τ), abs_of_neg (by linarith)]
    ring
  rw [key]
  simp only [hd]

theorem move (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} (x : (U.X k).dom) :
    ∃ (x₀ : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x₀.1 ∧ FrBor t (U.un k x₀) (U.un k x) ∧
      ∀ (s : Σ τ, Fin (Dw.mult τ)) (τ : (U.X k).Ψ) (a : Fin r),
        (τ.1 = relab c σ s.1 → (a : ℕ) = (U.X k).p0 + s.2 → ‖toC (t (some s) : CAt σ)‖ ^ 2 =
          ‖dmin (U.X k).Gm x.1 τ a.succ / dmin (U.X k).Gm x.1 τ a.castSucc‖) ∧
        (conjEmb τ.1 = relab c σ s.1 → (a : ℕ) + s.2 + 1 = (U.X k).p0 → ‖toC (t (some s) : CAt σ)‖ ^ 2 =
          ‖dmin (U.X k).Gm x.1 τ a.succ / dmin (U.X k).Gm x.1 τ a.castSucc‖⁻¹) := by
  obtain ⟨f, hf, hper⟩ := letters hσ hU k
  have hbij : Function.Bijective (relab c σ) := (GlobalTheory.Relab.relab_good E H l c σ hσ).1
  have hb := FrameDegreeData.bOf_mem (U.X k) x.2
  have ho := FrameDegreeData.ortho_bOf (U.X k) x.2
  set b := FrameDegreeData.bOf (U.X k) x.1
  have hy : rmul x.1 b ∈ (U.X k).dom := OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨P, h1, h2, h3, h4, -⟩ := hpt k x
  obtain ⟨P₀, k1, k2, k3, k4, -⟩ := hpt k ⟨_, hy⟩
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 (e.trans f) b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨g1, g2⟩ := PerBor.moveMat_support _ (e.trans f) hb j j' hne
    clear hpt
    rw [Equiv.trans_apply, Equiv.trans_apply] at g1 g2
    have g1' := congrArg Subtype.val g1
    rcases hf (e j) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ <;>
      rcases hf (e j') with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩
    · rw [if_neg (by omega)] at g2
      exact ⟨hbij.1 (by rw [← a2, ← b2, g1']), by omega⟩
    · rw [if_neg (by omega)] at g2
      omega
    · rw [if_pos (by omega)] at g2
      omega
    · rw [if_pos (by omega)] at g2
      refine ⟨hbij.1 ((ComplexEmbedding.involutive_conjugate E).injective (by rw [← a2, ← b2, g1'])), by omega⟩
  obtain ⟨t, ht, hd⟩ := FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F (ik k) P P₀
    (PerBor.moveMat (U.X k).p0 (e.trans f) b) (U.un k x) (U.un k ⟨_, hy⟩) h2 k2
    (fun a => PerBor.moveMat_mulVec _ (e.trans f) hb (U.X k).Gm x.1 (φ k a : Fin r → E) _ _
      (fun j => (h1 a j).trans (hper _ _ _)) (fun j => (k1 a j).trans (hper _ _ _))) hs h3 k3 h4 k4
  refine ⟨⟨_, hy⟩, t, ho, ht, fun s τ a => ?_⟩
  have hd' : toC (t (some (e (e.symm s))) : CAt σ) = _ := hd (e.symm s)
  clear hpt
  rw [PerBor.moveMat_diag _ _ hb] at hd'
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at hd'
  have hr := FrameDegreeData.ratio_rmul (U.X k) x.1 x.2 hb τ a
  rw [norm_div, RiemMaj.norm_dmin_ortho _ ho, RiemMaj.norm_dmin_ortho _ ho, div_one] at hr
  constructor
  · intro e1 e2
    rcases hf s with ⟨a1, a2, a3⟩ | ⟨a1, -⟩
    · have : f s = (τ, a) := Prod.ext (Subtype.ext (a2.trans e1.symm)) (Fin.ext (a3.trans e2.symm))
      rw [this, if_neg (by dsimp only; omega)] at hd'
      rw [hd', norm_inv, inv_pow]
      exact (eq_inv_of_mul_eq_one_right hr.symm).symm
    · exact absurd (e1 ▸ τ.2) a1
  · intro e1 e2
    rcases hf s with ⟨a1, -⟩ | ⟨a1, a2, a3, a4⟩
    · rw [← e1] at a1
      exact absurd a1 (((U.X k).cmType _).1 τ.2)
    · have : f s = (τ, a) := Prod.ext (Subtype.ext (a2.trans (by
        rw [← e1]; exact ComplexEmbedding.involutive_conjugate E τ.1))) (Fin.ext (by dsimp only; omega))
      rw [this, if_pos (by dsimp only; omega)] at hd'
      rw [hd']
      exact eq_inv_of_mul_eq_one_left hr.symm

theorem leadMinor_smul_one {n : ℕ} (κ : ℝ) (m : ℕ) (hm : m ≤ n) :
    GlobalTheory.CompanionTheory.Ar.leadMinor ((κ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) m = κ ^ m := by
  unfold GlobalTheory.CompanionTheory.Ar.leadMinor
  rw [dif_pos hm, Matrix.submatrix_smul, Pi.smul_apply, Pi.smul_apply,
    Matrix.submatrix_one _ (Fin.castLE_injective hm), Matrix.det_smul, Matrix.det_one, Fintype.card_fin, _root_.mul_one,
    ← Complex.ofReal_pow, Complex.ofReal_re]

theorem gram (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) {k : U.Comp} (x : (U.X k).dom)
    (hx : (U.X k).IsOrtho x.1) (y : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ) (ht : FrBor t (U.un k x) y)
    (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) (z : Sp ℂ ⟶ Xo.X) (hz : z = y.x)
    (v : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G)) (hv : ∀ i, (v i).left = y.u τ (Fin.cast hn.symm i))
    (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ p q, GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z (v p) (v q) (Γ p q)) (i : Fin n) :
    Real.sqrt (GlobalTheory.CompanionTheory.Ar.leadMinor Γ ((i : ℕ) + 1) / GlobalTheory.CompanionTheory.Ar.leadMinor Γ i) =
      Real.sqrt (Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖)) *
        ‖toC (t (some ⟨τ, Fin.cast hn.symm i⟩) : CAt σ)‖ := by
  classical
  subst hn
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_diag hσ hU W Wu hx
  choose cf h1 h2 h3 using ht.2.1 τ
  let Y : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := fun j i => toC (cf i j)
  have hd : ∀ i, IsDerivAt0 (fun z => (W.F.ex (W.ik k) W.Pm z).left)
      (∑ j, Y j i • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) (v i).left := fun i => by
    rw [hv]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per _ ((U.un k x).u τ)
      (fun i => Pi.single (W.e.symm ⟨τ, i⟩) 1) (W.der τ) (fun j => Y j i) _).1 ?_
    have := h3 i
    rw [W.pt] at this
    exact this
  set κ : ℝ := Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖) with hκ
  have hκ0 : 0 < κ := mul_pos Real.pi_pos (mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 (U.X k).ξ0_ne)))
  have hG : Γ = Yᴴ * ((κ : ℂ) • (1 : Matrix _ _ ℂ)) * Y := by
    ext p q
    rw [univ_ip W Wu hpq z (hz.trans ht.1) _ _ _ _ _ (hd p) (hd q) (hΓ p q), MetricChange.hermForm_sum]
    have hf : ∀ a b : Fin (Dw.mult τ), hermForm Wu.Hm (Pi.single (W.e.symm ⟨τ, a⟩) 1) (Pi.single (W.e.symm ⟨τ, b⟩) 1) =
        if a = b then ((2 * ‖relab c σ τ (U.X k).ξ0‖ : ℝ) : ℂ) else 0 := by
      intro a b
      rw [hH, hermForm, single_dotProduct, Matrix.mulVec_diagonal, _root_.one_mul, Equiv.apply_symm_apply, Pi.star_apply]
      split_ifs with hab
      · subst hab
        simp
      · rw [Pi.single_eq_of_ne (fun hh => hab (eq_of_heq (Sigma.mk.inj (W.e.symm.injective hh)).2))]
        simp
    simp only [hf, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      smul_eq_mul, Finset.mul_sum, hκ]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hdiag : ∀ i, Y i i = toC (t (some ⟨τ, i⟩) : CAt σ) := fun i => h1 i
  rw [hG, GlobalTheory.CompanionTheory.Ar.GrNorm.sqrt_ratio_conj _ Y (fun l k h => h2 k l h)
    (fun j => by rw [hdiag]; exact Units.ne_zero (M₀ := ℂ) (t (some ⟨τ, j⟩))), leadMinor_smul_one _ _ i.2, leadMinor_smul_one _ _ i.2.le,
    pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ hκ0.ne'), hdiag, mul_comm]
  rfl

theorem ip_iff {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    (z : Sp ℂ ⟶ X') (z' : Sp ℂ ⟶ X) (hz : z ≫ f = z') (v' w' : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ t'.G)
    (v w : GlobalTheory.CompanionTheory.Ar.epsAt z' ⟶ t.G) (cc₀ : ℂ) (hv : v.left = v'.left ≫ m.φ) (hw : w.left = w'.left ≫ m.φ) :
    GlobalTheory.CompanionTheory.Ar.HodgeIP t'.G t'.PP.L z v' w' cc₀ ↔ GlobalTheory.CompanionTheory.Ar.HodgeIP t.G t.PP.L z' v w cc₀ := by
  subst hz
  exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff E H X t X' t' f m z v' w' v w cc₀ hv hw

theorem valAt_unique {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) {e : 𝔐.Li} {v w : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ 𝔐.t.G}
    (hv : 𝔐.M.ValAt z e v) (hw : 𝔐.M.ValAt z e w) : v = w := by
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨ev, hev1, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z (𝔐.all _) Vz MR 𝔐.tie.gen 𝔐.t.semi.smooth
  obtain ⟨a, rfl⟩ := MR.onto v (GlobalTheory.CompanionTheory.Ar.GrNorm.tan_of_valAt hv)
  obtain ⟨b, rfl⟩ := MR.onto w (GlobalTheory.CompanionTheory.Ar.GrNorm.tan_of_valAt hw)
  obtain ⟨_, e1⟩ := (hev1 _ _).1 hv
  obtain ⟨_, e2⟩ := (hev1 _ _).1 hw
  rw [← e1, ← e2]

theorem transport {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y₁ : (Σ k, J k) → Ω}
    (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y₁) (z : Sp ℂ ⟶ 𝔐.X) (y : FrPt Xo c (CAt σ))
    (hz : z ≫ 𝔐.f = GlobalTheory.CompanionTheory.Ar.Small.ptY Y y) (τ : E →+* ℂ) {n : ℕ} (ιx : Fin n → Fin (Dw.mult τ))
    (b : Fin n → 𝔐.Li)
    (hb : ∀ i, ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (b i) v ∧
      v.left ≫ 𝔐.m.φ = GlobalTheory.CompanionTheory.Ar.Small.tanY Y y τ (ιx i))
    (Γ : Matrix (Fin n) (Fin n) ℂ) (hΓ : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) :
    ∃ (z' : Sp ℂ ⟶ Xo.X) (v : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt z' ⟶ Xo.univ.t.G)), z' = y.x ∧
      (∀ i, (v i).left = y.u τ (ιx i)) ∧
      ∀ p q, GlobalTheory.CompanionTheory.Ar.HodgeIP Xo.univ.t.G Xo.univ.t.PP.L z' (v p) (v q) (Γ p q) := by
  obtain ⟨v, hv, hI⟩ := hΓ
  have e : ∀ i, (v i).left ≫ 𝔐.m.φ = GlobalTheory.CompanionTheory.Ar.Small.tanY Y y τ (ιx i) := fun i => by
    obtain ⟨w, h1, h2⟩ := hb i
    rw [valAt_unique 𝔐 z (hv i) h1, h2]
  let zY : Sp ℂ ⟶ Y.X := GlobalTheory.CompanionTheory.Ar.Small.ptY (S := CAt σ) Y y
  let zF : Sp ℂ ⟶ Xo.XF c := GlobalTheory.CompanionTheory.Ar.Small.ptF (S := CAt σ) y
  let zU : Sp ℂ ⟶ Xo.X := y.x
  let vY : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt zY ⟶ Y.t.G) := fun i =>
    Over.homMk (GlobalTheory.CompanionTheory.Ar.Small.tanY (S := CAt σ) Y y τ (ιx i)) (GlobalTheory.CompanionTheory.Ar.Small.tanY_hom Y y τ (ιx i))
  let vF : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt zF ⟶ Y.oF.t.G) := fun i =>
    Over.homMk (GlobalTheory.CompanionTheory.Ar.Small.tanF (S := CAt σ) Y y τ (ιx i)) (GlobalTheory.CompanionTheory.Ar.Small.tanF_hom Y y τ (ιx i))
  let vU : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt zU ⟶ Xo.univ.t.G) := fun i => Over.homMk (y.u τ (ιx i)) (y.tan τ (ιx i)).1
  refine ⟨zU, vU, rfl, fun _ => rfl, fun p q => ?_⟩
  have h1 := (ip_iff 𝔐.m z zY hz _ _ (vY p) (vY q) _ (e p).symm (e q).symm).1 (hI p q)
  have h2 := (ip_iff Y.m zF zY rfl (vF p) (vF q) (vY p) (vY q) _ rfl rfl).2 h1
  exact (ip_iff Y.m0.toSABMap zF zU (GlobalTheory.CompanionTheory.Ar.Small.ptF_fst y) (vF p) (vF q) (vU p) (vU q) _
    (GlobalTheory.CompanionTheory.Ar.Small.tanF_φ Y y τ (ιx p)).symm (GlobalTheory.CompanionTheory.Ar.Small.tanF_φ Y y τ (ιx q)).symm).1 h2

end PositivityTheory.UnitarySelfGeneration.GF
