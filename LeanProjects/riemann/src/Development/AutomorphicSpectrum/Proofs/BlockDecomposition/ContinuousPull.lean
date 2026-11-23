import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSchwartzAOfIsMonoFock
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem npow_inv (x : ℝ≥0) (t : ℂ) : (((((x : ℝ))⁻¹ : ℝ)) : ℂ) ^ (-t) = npow x t := by
  have harg : Complex.arg ((x : ℝ) : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg x)]
    exact Real.pi_pos.ne
  unfold npow
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

theorem npow_add_of (x : ℝ≥0) (hx : x ≠ 0) (s t : ℂ) : npow x (s + t) = npow x s * npow x t := by
  unfold npow
  exact Complex.cpow_add _ _ (by exact_mod_cast hx)

theorem jtR_hermTo (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (φ : Mx D V.rank n → ℂ)
    (b : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
      (fun X => φ (tupOf X)) (hermTo b) = Jt ψ V μ φ b := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  haveI : IsTopologicalAddGroup (Mx D V.rank n) := k1
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  unfold PositivityTheory.PfSWUS.Loc.jtR Jt
  rw [integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hg : gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
    ext a c
    exact hR_tup V y y a c
  change φ y * ψ (PositivityTheory.PfSWUS.Loc.trPair _ b.1 (gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y))) = _
  rw [hg]
  rfl

theorem trace_pull (a : GL (Fin n) (AE D)) (B : Mx D n n) (b : hermA D n) :
    Matrix.trace (HMul.hMul (adj a.1 * B * a.1) (pull a b).1 : Mx D n n) = Matrix.trace (HMul.hMul B b.1 : Mx D n n) := by
  have h1 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul]
    have : a.1 * (a⁻¹).1 = 1 := by simp
    rw [this]
    simp [adj]
  have h2 : a.1 * (a⁻¹).1 = 1 := by simp
  show Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1)) = Matrix.trace (B * b.1)
  calc Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1))
      = Matrix.trace (adj a.1 * (B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1)) * adj a.1) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * b.1 * (adj (a⁻¹).1 * adj a.1)) := by
        rw [h2]
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = Matrix.trace (B * b.1) := by rw [h1, Matrix.mul_one]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem mono_mem (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ)
    (hθ : IsInfFam θ) (hl : ∀ τ, l τ ≠ 0) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hφ : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s ∧ φ ∈ schwartzA θ V.rank n := by
  refine ⟨?_, GlobalTheory.CompanionTheory.IfrAdd.mem_schwartzA_of_isMonoFock hθ hl hs hφ⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := hφ
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    have h1 := GlobalTheory.CompanionTheory.IfrAdd.mem_SB_of_isPureFin bs (Φf := fun X => g fun i j => X j i) (Φv := gv) hp
    have h2 := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) h1
    exact ⟨h2.1, h2.2⟩
  exact Submodule.subset_span ⟨_, g, hg, rfl⟩

theorem sect_w (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (hω : IsWeilSch ψ χ θ V μ ω) (nb : hermA D n → G D n) (hnb : IsNMap nb) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0)
    (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b * 1) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  rw [mul_one]
  unfold sect Jt
  congr 1
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, adj]
  show (ω (nb b) Φ).1 y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V 0 y))) = _
  rw [h0, hω.unip (nb b) b.1 (hnb b)]
  simp [mul_comm]

theorem jt_pull (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n))
    (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (φ : Mx D V.rank n → ℂ) (a : GL (Fin n) (AE D))
    (b : hermA D n) :
    Jt ψ V μ φ (pull a b) = npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) *
      Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b := by
  have hr0 : absA D (Matrix.GeneralLinearGroup.det a) ≠ 0 :=
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have key := GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a
    (fun x => φ x * ψ (halfTr (Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V x x) : Mx D n n))))
  have e : ∀ y : Mx D V.rank n, Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1)) : Mx D n n) =
      Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D n n) := by
    intro y
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    have hin : GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1) = adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1 := by
      unfold GlobalTheory.StdUnn.inner
      rw [adj_mul]
      simp only [Matrix.mul_assoc]
    rw [hin]
    show Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y)
    calc Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1))
        = Matrix.trace ((a⁻¹).1 * (b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1)) * (a⁻¹).1) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y * (a.1 * (a⁻¹).1)) := by
          rw [h1]
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y) := by rw [h2, Matrix.mul_one]
  unfold Jt
  simp only [e] at key
  rw [key, ← mul_assoc]
  have : npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) = 1 := by
    unfold npow
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hr0), add_neg_cancel, Complex.cpow_zero]
  rw [this, one_mul]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.ThetaGlue
variable {D : D7} {n : ℕ}

theorem ifrB_eq_meanC (D : D7) (r : ℕ) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (φ : Mx D V.rank r → ℂ) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (β : HermE D r) (hβ : β.1.det ≠ 0) :
    IfrB V ν φ β = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
      (HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) (fun X => φ (tupOf X))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig (HSpace.gram V) X = β.1}) := by
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  rw [hS]
  exact hI

def pullE (a : GL (Fin n) (AE D)) : hermA D n ≃+ hermA D n where
  toFun := pull a
  invFun := pull a⁻¹
  left_inv b := by
    apply Subtype.ext
    show (a⁻¹⁻¹).1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj (a⁻¹⁻¹).1 = b.1
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    rw [inv_inv]
    calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
        = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv b := by
    apply Subtype.ext
    show (a⁻¹).1 * ((a⁻¹⁻¹).1 * b.1 * adj (a⁻¹⁻¹).1) * adj (a⁻¹).1 = b.1
    have h1 : adj a.1 * adj (a⁻¹).1 = 1 := (astar a).inv_val
    have h2 : (a⁻¹).1 * a.1 = 1 := by simp
    rw [inv_inv]
    calc (a⁻¹).1 * (a.1 * b.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * b.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    apply Subtype.ext
    show (a⁻¹).1 * (x.1 + y.1) * adj (a⁻¹).1 = (a⁻¹).1 * x.1 * adj (a⁻¹).1 + (a⁻¹).1 * y.1 * adj (a⁻¹).1
    rw [Matrix.mul_add, Matrix.add_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_pull (a : GL (Fin n) (AE D)) : Continuous (pull a) := by
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const)).subtype_mk _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) (hF : Integrable F lam) : Integrable (fun b => F (pull a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
  haveI := hl
  have hc : Continuous (pullE a) := continuous_pull a
  have hc' : Continuous (pullE a).symm := continuous_pull a⁻¹
  let M : hermA D n ≃ₜ hermA D n := { toEquiv := (pullE a).toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI hH : (lam.map (pullE a)).IsAddHaarMeasure := (pullE a).isAddHaarMeasure_map lam hc hc'
  have e := Measure.isAddLeftInvariant_eq_smul (lam.map (pullE a)) lam
  have h1 : Integrable F (lam.map (pullE a)) := by
    rw [e]
    exact hF.smul_measure ENNReal.coe_ne_top
  have hemb : MeasurableEmbedding (pullE a) := M.measurableEmbedding
  exact hemb.integrable_map_iff.1 h1

end GlobalTheory.CompanionTheory.MM
