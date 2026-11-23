import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

namespace Integ

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem det_bl {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.det (bl hn 1 y 0 1 : Mx D n n) = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

def blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) :=
  ⟨bl hn 1 y 0 1, bl hn 1 (-y) 0 1, GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ rfl,
    GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ (neg_neg y).symm⟩

theorem det_blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 y 0 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, ha]
  exact det_bl hn y

theorem lintegral_comp_char_one {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (hc : addEquivAddHaarChar φ = 1) (g : A → ℝ≥0∞) :
    ∫⁻ y, g (φ y) ∂μ = ∫⁻ y, g y ∂μ := by
  have key := addEquivAddHaarChar_smul_map μ φ
  rw [hc, one_smul] at key
  have hp : MeasurePreserving φ μ μ := ⟨φ.continuous.measurable, key⟩
  exact hp.lintegral_comp_emb φ.toHomeomorph.measurableEmbedding g

theorem lintegral_bl {a r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (ν : Measure (Mx D a n))
    (hν : ν.IsAddHaarMeasure) (g : Mx D a n → ℝ≥0∞) :
    ∫⁻ U, g (mm U (bl hn 1 y 0 1)) ∂ν = ∫⁻ U, g U ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) (blU hn y)
  have hc : addEquivAddHaarChar φ = 1 := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a n
      (1 : GL (Fin a) (AE D)) (blU hn y)
    rw [det_blU hn y (blU hn y) rfl] at h
    simpa only [map_one, one_pow, mul_one] using h
  have e : ∀ U : Mx D a n, mm U (bl hn 1 y 0 1) = φ U := fun U => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
    rfl
  simp only [e]
  exact lintegral_comp_char_one ν φ hc g

theorem jn_first {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  simp [jn, Matrix.submatrix_apply, Matrix.fromCols]

theorem xu_bl (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    mm (XU d hn x₀ h U) (bl hn 1 y 0 1) =
      mm d.jX (mm U (bl hn 1 y 0 1)) + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1)) := by
  unfold XU
  simp only [mm]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem inner_eq (hIkL : IkLint) (hJn : JnBl) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) {θ : InfFam D}
    (hθ : IsInfFam θ) {M : Mx D B.rank n → ℂ} (hM : M ∈ schwartzA θ B.rank n)
    (hM0 : ∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W)
    (y : Mx D W.rank t) :
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK ∂I.μ₁ =
      ‖ikp I M (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))‖ₑ := by
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hb : mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1) = jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0) :=
    hJn D n t _ _ hn _ _ y
  rw [← hb, ← hIkL D n t B W d I θ hθ M hM hM0]
  simp only [xu_bl]
  exact lintegral_bl hn y I.μ₁ hf.1
    (fun U => ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1))))‖ₑ ∂I.νK)

theorem continuous_jn {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun u : Mx D a r × Mx D a t => jn hn u.1 u.2 := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun u : Mx D a r × Mx D a t =>
    Matrix.fromCols u.1 u.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact continuous_fst.matrix_elem i k
  | inr k => exact continuous_snd.matrix_elem i k

theorem continuous_bl {r t n : ℕ} (hn : r + t = n) : Continuous fun y : Mx D r t => (bl hn 1 y 0 1 : Mx D n n) :=
  (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_pt {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun p : I.l.K × Par D n t W =>
      mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨-, g2, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hT := (top_mx (D := D) B.rank n).1
  have hU : Continuous fun p : I.l.K × Par D n t W => p.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hh : Continuous fun p : I.l.K × Par D n t W => p.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hX : Continuous fun p : I.l.K × Par D n t W => XU d hn x₀ p.2.1 p.2.2.1 :=
    (continuous_const.matrix_mul hU).add (continuous_const.matrix_mul
      ((continuous_jn hn).comp (((continuous_ww x₀).comp hh).prodMk continuous_const)))
  exact ((continuous_mt B).comp (continuous_subtype_val.comp continuous_fst).inv).matrix_mul
    (hX.matrix_mul ((continuous_bl hn).comp hy))

end Integ

open Integ in

theorem integrable_core : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  intro hIk hDom hOrb _ hIkL hFub hJn D n t B W d hn I θ hθ μ hμ x₀ hx₀ Φ hΦ η hη
  obtain ⟨M, hM, hM0, hMd⟩ := hDom D θ hθ B.rank n n id Function.injective_id Φ hΦ
  have hΨ : ikp I M ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ M hM).2
  obtain ⟨N, hN, -, hNd⟩ := hDom D θ hθ W.rank n W.rank (fun j => finCongr hn (Fin.castAdd t j))
    (fun a b h => by simpa using h) (ikp I M) hΨ

  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hBG : BorelSpace (GA D W) := ⟨rfl⟩
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hcΦ : Continuous Φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hcη : Continuous η := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hpt := continuous_pt (d := d) hn I x₀
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hcore : Continuous (core hn I x₀ Φ η) :=
    (hcΦ.comp hpt).mul (Complex.continuous_conj.comp (hcη.comp hy))
  refine ⟨hcore.measurable.aestronglyMeasurable, ?_⟩

  set F : I.l.K × GA D W × Mx D t n × Mx D W.rank t → ℝ≥0∞ := fun p =>
    ‖M (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)))‖ₑ * ‖η p.2.2.2‖ₑ with hF
  have hFm : Measurable F :=
    (hcM.comp hpt).measurable.enorm.mul (hcη.comp hy).measurable.enorm
  have hle : ∀ p, ‖core hn I x₀ Φ η p‖ₑ ≤ F p := fun p => by
    simp only [core, hF, enorm_mul, RCLike.enorm_conj]
    gcongr
    rw [enorm_le_iff_norm_le]
    refine (hMd _).trans ?_
    simpa using Complex.re_le_norm _
  have hη' : ∫⁻ y, ‖η y‖ₑ ∂μ < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ W.rank t μ η hη).2
  have hN' : ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m < ⊤ := hOrb D θ hθ W I.m I.haar x₀ hx₀ N hN
  have hin : ∀ y h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ≤ ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ := fun y h => by
    simp only [hF]
    have e : ∀ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ * ‖η y‖ₑ ∂I.νK =
        (∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK) * ‖η y‖ₑ := fun U =>
      lintegral_mul_const' _ _ enorm_ne_top
    simp only [e]
    rw [lintegral_mul_const' _ _ enorm_ne_top, inner_eq hIkL hJn hn I hθ hM hM0 x₀ h y]
    gcongr
    rw [enorm_le_iff_norm_le]
    have h3 := hNd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
    rw [jn_first] at h3
    exact h3.trans (Complex.re_le_norm _)
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖core hn I x₀ Φ η p‖ₑ ∂(I.νK.prod (Q0 I μ))
      ≤ ∫⁻ p, F p ∂(I.νK.prod (Q0 I μ)) := lintegral_mono hle
    _ = ∫⁻ y, ∫⁻ h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ∂I.m ∂μ :=
        (hFub I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).2 F hFm
    _ ≤ ∫⁻ y, ∫⁻ h, ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ ∂I.m ∂μ :=
        lintegral_mono fun y => lintegral_mono fun h => hin y h
    _ = (∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m) * ∫⁻ y, ‖η y‖ₑ ∂μ := by
        simp only [lintegral_mul_const' _ _ enorm_ne_top]
        rw [lintegral_const_mul' _ _ hN'.ne]
    _ < ⊤ := ENNReal.mul_lt_top hN' hη'

end GlobalTheory.CompanionTheory.ColumnSplitting

end
