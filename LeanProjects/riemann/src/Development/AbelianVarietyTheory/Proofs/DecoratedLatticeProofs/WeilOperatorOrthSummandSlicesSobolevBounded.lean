import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def slA (o : OrthDec S A B) (f : WO S T → ℂ) : WO A T → ℂ := fun u => f ((o.resS T).symm (u, 0))

def extA (o : OrthDec S A B) (T : HSp D) : WO A T →+ WO S T :=
  (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extA_apply (o : OrthDec S A B) (u : WO A T) : extA o T u = (o.resS T).symm (u, 0) := rfl

theorem symm_left (o : OrthDec S A B) (u : WO A T) : (o.resS T).symm (u, 0) = u ⬝ o.pA := by
  rw [o.resS_symm_apply, Matrix.zero_mul, add_zero]

theorem symm_swap (o : OrthDec S A B) (v : WO B T) : (o.symm.resS T).symm (v, 0) = (o.resS T).symm (0, v) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]
  exact add_comm _ _

theorem compAt_pA {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau) :
    compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  unfold compAt OrthDec.pA GlobalTheory.MixModel.rat
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_slice {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (t : ℝ) :
    (o.resS T).symm (lineAt θ τ z t, 0) = lineAt θ τ (z * o.qA.map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T := (extA o T).comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * o.qA.map (tauE D τ)) L := by
    refine ⟨(o.continuous_resS_symm T).comp (hL.1.prodMk continuous_const), fun t => ?_, fun t τ' => ?_⟩
    · show ((o.resS T).symm (lineAt θ τ z t, 0)).map (finPart D) = 0
      rw [symm_left, Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' ((o.resS T).symm (lineAt θ τ z t, 0)) = _
      rw [symm_left, GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_pA hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem heisO_slice (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec S A B) (u : WO A T) (g : WO S T → ℂ) :
    heisO ψ A T u (slA o g) = slA o (heisO ψ S T ((o.resS T).symm (u, 0)) g) := by
  funext w
  simp only [slA, heisO]
  rw [o.symplOH_resS T, ← map_add, Prod.mk_add_mk, add_zero]
  simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, add_zero]

theorem dRho_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ A T) θ τ z (slA o g) =
      slA o (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z * o.qA.map (tauE D τ)) g) := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, heisO_slice, lineAt_slice hθ]
  rfl

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def dirA (o : OrthDec S A B) (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) : Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * o.qA.map (tauE D a.1)

def opA (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (o : OrthDec S A B)
    (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) (g : WO S T → ℂ) : WO S T → ℂ :=
  Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (dirA o a) g

theorem word_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) (g : WO S T → ℂ) :
    wordAct (heisDer ψ θ) l (slA o g) = slA o (wordAct (opA ψ θ o) l g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, ih]
    exact dRho_slice ψ hθ o a.1 _ _

abbrev supN (φ : WO S T → ℂ) : ℝ≥0∞ := ⨆ w, ‖φ w‖ₑ

theorem word_bound {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) :
    ∃ c : ℝ≥0, ∀ g, IsThetaFunO ψ S T g → ∀ k,
      wordSum (heisDer ψ θ) supN k (wordAct (opA ψ θ o) l g) ≤ c * wordSum (heisDer ψ θ) supN (k + l.length) g := by
  induction l with
  | nil => exact ⟨1, fun g _ k => by simp⟩
  | cons a l ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Real.toNNReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) * c, fun g hg k => ?_⟩
    have hg' : IsThetaFunO ψ S T (wordAct (opA ψ θ o) l g) :=
      wordAct_rel (B := opA ψ θ o) (R := fun x _ => IsThetaFunO ψ S T x) l
        (fun a _ _ _ h => theta_dRho hθ hψ a.1 _ h) (y := g) hg
    rw [wordAct_cons]
    calc _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          wordSum (heisDer ψ θ) supN (k + 1) (wordAct (opA ψ θ o) l g) :=
          GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ GlobalTheory.Size.SupWord.supN_add_le GlobalTheory.Size.SupWord.supN_smul hg' a.1 _ k
      _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          (c * wordSum (heisDer ψ θ) supN (k + 1 + l.length) g) := by gcongr; exact hc g hg (k + 1)
      _ = _ := by
        rw [List.length_cons, show k + (l.length + 1) = k + 1 + l.length by omega, ← mul_assoc, ENNReal.ofReal,
          ENNReal.coe_mul]

theorem l2O_le_supN_of_measure_eq_one {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1) (φ : WO S T → ℂ) :
    l2O μ 𝓕 φ ≤ supN φ := by
  have h : l2O μ 𝓕 φ ^ 2 ≤ supN φ ^ 2 := by
    rw [l2O_sq_eq_lintegral]
    calc ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ ≤ ∫⁻ _ in 𝓕, supN φ ^ 2 ∂μ :=
          lintegral_mono fun w => by gcongr; exact le_iSup (fun w => ‖φ w‖ₑ) w
      _ = supN φ ^ 2 := by rw [setLIntegral_const, h1, mul_one]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem supN_slice (o : OrthDec S A B) (φ : WO S T → ℂ) : supN (slA o φ) ≤ supN φ :=
  iSup_le fun _ => le_iSup (fun w => ‖φ w‖ₑ) _

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

theorem sobO_slice_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (d : ℕ) : ∃ K : ℝ≥0, ∀ (μ : Measure (WO A T)) (𝓕 : Set (WO A T)), μ 𝓕 = 1 →
      ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (slA o f) ≤ K * supSob ψ θ d f := by
  choose c hc using word_bound (T := T) hψ hθ o
  refine ⟨∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → D.what₂.Tau × Fin T.rank × Fin A.rank × Bool, c (List.ofFn a),
    fun μ 𝓕 h1 f hf => ?_⟩
  unfold sobO supSob wordSum
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [word_slice ψ hθ o]
  calc l2O μ 𝓕 (slA o (wordAct (opA ψ θ o) (List.ofFn a) f)) ≤ supN (wordAct (opA ψ θ o) (List.ofFn a) f) :=
        (l2O_le_supN_of_measure_eq_one h1 _).trans (supN_slice o _)
    _ = wordSum (heisDer ψ θ) supN 0 (wordAct (opA ψ θ o) (List.ofFn a) f) := (wordSum_zero _ _ _).symm
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN (0 + (List.ofFn a).length) f := hc _ f hf 0
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN d f := by
        gcongr
        exact wordSum_mono (by rw [List.length_ofFn]; omega) f
    _ = _ := rfl

theorem isSobForm_slice {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    {χ χ' : (AE D)ˣ →* Circle} {om : Om A T} (hom : IsWeilDatumO ψ A T χ χ' om) (p : GA D A × GA D T) :
    IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0 where
  add f g _ _ := by
    show om p (slA o f + slA o g) 0 = _
    rw [map_add]; rfl
  smul c f _ := by
    show om p (c • slA o f) 0 = _
    rw [map_smul]; rfl
  bound U hU := by
    have hψ := hom.std
    let U' : AddSubgroup (WO A T) := U.comap (extA o T)
    have hU' : IsOpen (U' : Set (WO A T)) :=
      hU.preimage ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
    obtain ⟨e, d, hK⟩ := GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D A.rank T.rank
    obtain ⟨C, hC⟩ := hK A T rfl rfl ψ θ hθ U' hU'
    obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne A T
    obtain ⟨K, hKs⟩ := sobO_slice_le (T := T) hψ hθ o d
    refine ⟨d, C * (ENNReal.ofReal ((height A p.1 * height T p.2) ^ e)).toNNReal * K, fun f hf => ?_⟩
    have hsl : slA o f ∈ thetaLevel ψ A T U' := by
      refine ⟨((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf.1).1 0, fun u hu h0 => ?_⟩
      rw [heisO_slice, ← extA_apply, hf.2 _ hu]
      rw [extA_apply, symm_left, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := hC χ χ' om hom μ 𝓕 hμ (slA o f) hsl p.1 p.2
    have h2 := hKs μ 𝓕 hμ.2.2 f hf.1
    have hfin : ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ‖om p (fun u => f ((o.resS T).symm (u, 0))) 0‖ₑ = ‖thetaKO om p.1 p.2 (slA o f)‖ₑ := rfl
      _ ≤ C * sobO ψ θ μ 𝓕 d (slA o f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := h
      _ ≤ C * (K * supSob ψ θ d f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := by gcongr
      _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hfin]
        ring

theorem weil_slice_isSobForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (S A B T : HSp D) (o : OrthDec S A B),
      (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) ∧
      ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun v => f ((o.resS T).symm (0, v))) 0 := by
  intro D ψ θ hθ S A B T o
  refine ⟨fun χ χ' om hom p => isSobForm_slice hθ o hom p, fun χ χ' om hom p => ?_⟩
  have e : (fun f : WO S T → ℂ => om p (fun v => f ((o.resS T).symm (0, v))) 0) =
      fun f => om p (fun v => f ((o.symm.resS T).symm (v, 0))) 0 := by
    funext f
    simp only [symm_swap]
  rw [e]
  exact isSobForm_slice hθ o.symm hom p

end GlobalTheory.SliceForm
