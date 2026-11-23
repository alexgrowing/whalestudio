import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSizeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpaceStatement

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev GlobalTheory.SmVec NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepSmooth

variable {D : D7} {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {Φ : MMap M}

def IsEquiv (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (Φ : MMap M) : Prop :=
  ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (u : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ a (u τ) → Φ (Function.update u τ w) = rTr V (atTau θ V τ a) (Φ u)

def IsSob (Φ : MMap M) : Prop :=
  ∀ τ (u : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Φ (Function.update u τ w) x

def der (u : M.Vec) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : M.sm τ :=
  ⟨dRep (trRep (M.σ τ) (M.fr τ)) X (u τ), (MultGelf.mem_sm M τ).2
    (dRep_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (MultGelf.isURep M τ) ((MultGelf.mem_sm M τ).1 (u τ).2) hX)⟩

theorem hasDerivAt_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (x : GA D V) :
    HasDerivAt (fun t : ℝ => Φ u (x * oneP θ V τ X t)) (Φ (Function.update u τ (der u τ hX)) x) 0 := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  obtain ⟨ℓ, hℓ, hℓT⟩ := hs τ u x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (MultGelf.mem_sm M τ).1 (u τ).2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ) ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (MultGelf.isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => Φ u (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i)
        (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ))⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := he τ _ (exp_mem_UH hG hX t) u ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩ rfl
    have h3 := hℓT ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  rw [h1, ← hℓT, show ((der u τ hX : M.sm τ) : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X (u τ) from rfl,
    ha _ (dRep_mem hG (MultGelf.isURep M τ) hu hX)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
    (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
  simpa using h5

theorem rder_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (Φ u) = Φ (Function.update u τ (der u τ hX)) :=
  funext fun x => (hasDerivAt_apply he hs τ u hX x).deriv

theorem rderC_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (Φ (Function.update v τ u)) = Φ (Function.update v τ w) := by
  have hp := parts_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ)) Z
  have h1 := rder_apply he hs τ (Function.update v τ u) hp.1
  have h2 := rder_apply he hs τ (Function.update v τ u) hp.2
  rw [Function.update_idem] at h1 h2
  have h3 : w = der (Function.update v τ u) τ hp.1 + Complex.I • der (Function.update v τ u) τ hp.2 :=
    Subtype.ext (by rw [hw]; simp only [der, Function.update_self]; rfl)
  rw [h3, Φ.map_update_add, Φ.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (Φ (Function.update v τ u)) =
        Φ (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (MultGelf.mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (MultGelf.isURep M τ) Z ((MultGelf.mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply he hs τ v Z w _ rfl

theorem gelf_scalar (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (k : ℕ) :
    ∃ c : ℂ, ∀ v : M.Vec, gelf θ V τ k (Φ v) = c • Φ v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GlobalTheory.SmVec.GelfScalar.gelfH_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    (M.ds τ).2.2.2.1 k
  refine ⟨c, fun v => ?_⟩
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply he hs τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : c • v τ = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, ← hc _ ((MultGelf.mem_sm M τ).1 (v τ).2), Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  have h2 : c • Φ v = Φ (Function.update v τ (c • v τ)) := by
    rw [Φ.map_update_smul, Function.update_eq_self]
  rw [h2, h1]
  refine Eq.trans ?_ (map_sum (Φ.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem zfin (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ Φ u ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {Φ u}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_scalar he hs τ k
  have h2 : a • Φ u = Φ (Function.update u τ (a • u τ)) := by
    rw [Φ.map_update_smul, Function.update_eq_self]
  rw [h2, hc, ← h2]
  exact Submodule.smul_mem _ _ hf

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem smooth (hθ : IsInfFam θ) (he : IsEquiv θ Φ) (hs : IsSob Φ) (hc : ∀ u, Continuous (Φ u)) (u : M.Vec)
    (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (g : GA D V) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ u (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  refine GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space D θ V hθ (Set.range Φ) ?_ _ ⟨u, rfl⟩ k τs Xs hX g
  rintro _ ⟨v, rfl⟩
  refine ⟨hc v, fun τ => ⟨fun X => Rder θ V τ X (Φ v), fun X hX => ?_, fun a X hX Y hY => ?_⟩⟩
  · simp only [rder_apply he hs τ v hX]
    exact ⟨⟨_, rfl⟩, hasDerivAt_apply he hs τ v hX⟩
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1
    obtain ⟨h1, h2⟩ := GlobalTheory.SmVecLinear.dRep_linear _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 _
      ((MultGelf.mem_sm M τ).1 (v τ).2)
    have haX : a • X ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem' a hX
    have hXY : a • X + Y ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem' haX hY
    have h3 : der v τ hXY = (a : ℂ) • der v τ hX + der v τ hY :=
      Subtype.ext ((h1 _ haX _ hY).trans (by rw [h2 a X hX]; rfl))
    simp only [rder_apply he hs τ v hX, rder_apply he hs τ v hY, rder_apply he hs τ v hXY]
    rw [h3, Φ.map_update_add, Φ.map_update_smul]

theorem foldr_rder (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∃ v, l.foldr (fun p f => Rder θ V p.1 p.2 f) (Φ u) = Φ v := by
  induction l with
  | nil => exact ⟨u, rfl⟩
  | cons p l ih =>
    obtain ⟨v, hv⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact ⟨_, by rw [List.foldr_cons, hv, rder_apply he hs p.1 v (hl p List.mem_cons_self)]⟩

section Inst

variable {pl : InfinitePlace D.host.F ≃ D.what₂.Tau} {X : ModInst D V M pl} {T : GA D V ≃* X.inst.GA}

theorem conj_lie (τ : D.what₂.Tau) {E : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hE : Formalism.REAL.inG (M.ε τ) E) :
    (M.fr τ)⁻¹ * E * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hk : Eᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * E = 0 := hE
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change ((M.fr τ)⁻¹ * E * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * E * M.fr τ) = 0
  calc _ = (M.fr τ)ᴴ * (Eᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) +
        Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * E) * M.fr τ := by
        rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk]; simp

@[reducible] def bundle (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] (hC : ∀ v, CompleteSpace (H v))
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (Hs : Type)
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (hF : I.IsFundDom (I.muA μf) fund) (hR : I.IsRightReg μf fund R)
    (hH : I.IsHilbTensor σ σs tens) (g : ℕ) : RowsAut where
  I := I
  μf := μf
  fund := fund
  fund_spec := hF
  lam := fun _ _ => 0
  H := H
  hC := hC
  σ := σ
  w := fun _ => 0
  Hs := Hs
  σs := σs
  tens := tens
  tens_spec := hH
  R := R
  R_spec := hR
  g := g
  g₀ := 0
  e := fun _ => 0
  e_adm := ⟨IsLocallyConstant.const _, by funext x; simp [AutInst.convF], fun _ => by simp,
    fun _ _ _ => by simp, fun _ h => absurd rfl h, fun _ _ _ _ _ => rfl, fun _ h => absurd rfl h⟩
  Re := 0
  Re_spec := ⟨integrable_zero _ _ _, fun _ _ => by simp⟩

theorem isContRep_of_ae (B : RowsAut) {y : B.I.L2 B.μf B.fund} {f : B.I.GA → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ B.I.GFset, ∀ x, f (γ * x) = f x) (h : ∀ᵐ x ∂(B.I.muA B.μf), f x = B.I.ext y x) :
    GlobalTheory.Dec.IsContRep B y f := by
  refine ⟨hc, hl, ?_⟩
  have h1 := B.R_spec 1 y
  rw [(GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1] at h1
  filter_upwards [h1, ae_restrict_of_ae (s := B.fund) h] with x a b
  rw [b]
  simpa using a

theorem eq_of_ae (B : RowsAut) {f f' : B.I.GA → ℂ} (hc : Continuous f) (hc' : Continuous f')
    (h : f =ᵐ[B.I.muA B.μf] f') : f = f' := by
  obtain ⟨-, -, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hc hc').1 h

theorem eq_onePar (B : RowsAut) (w : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε w)) (t : ℝ) {h : B.I.GA}
    (h2 : h.2 = 1) (hw : uMat (h.1 w) = NormedSpace.exp (t • E.1)) (hv : ∀ v, v ≠ w → uMat (h.1 v) = 1) :
    h = GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E) t := by
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) h2
  change uMat (h.1 v) = NormedSpace.exp (t • (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E v).1)
  by_cases c : v = w
  · subst c
    rw [hw, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_same]
  · rw [hv v c, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_of_ne c]
    simp

theorem hasDerivAt_switch (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) {G : Type} [Group G] (T : GA D V ≃* G) (c : ℝ → G)
    (hc : ∀ t, T (oneP θ V τ Y t) = c t) (y : G) :
    HasDerivAt (fun t : ℝ => Φ u (T.symm (y * c t))) (Φ (Function.update u τ (der u τ hY)) (T.symm y)) 0 := by
  simp only [← hc, map_mul, T.symm_apply_apply]
  exact hasDerivAt_apply he hs τ u hY (T.symm y)

end Inst

end GlobalTheory.RepSmooth

end
