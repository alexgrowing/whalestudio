import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AtMostOneHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelLast

open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' Z : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z]

theorem flCol_one [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
    (Φ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) (x : Matrix n (n' ⊕ Unit) k) :
    GlobalTheory.LocFlat.flCol ψ ν 1 Φ x = Φ (withCol x.toCols₁ fun r => x r (Sum.inr ())) := by
  classical
  haveI hE : IsEmpty {rs : (n ⊕ Fin 0) × (n' ⊕ Fin (0 + 1)) // Free 1 rs} := ⟨by
    rintro ⟨⟨r | r, s | s⟩, h⟩
    · exact h
    · have := s.2
      simp only [Free] at h
      omega
    · exact r.elim0
    · exact r.elim0⟩
  have hnf : ∀ rs : (n ⊕ Fin 0) × (n' ⊕ Fin (0 + 1)), ¬ Free 1 rs := fun rs h => hE.false ⟨rs, h⟩
  have hpt : ∀ e, affPt (c := 0) (n' := n') 1 x.toCols₁ e + GlobalTheory.LocFlat.colAt n' 0 1 (fun r => x r (Sum.inr ())) =
      withCol x.toCols₁ fun r => x r (Sum.inr ()) := by
    intro e
    ext (r | r) (s | s)
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, withCol, hnf]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, withCol, hnf]
    · exact r.elim0
    · exact r.elim0
  unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
  simp only [hpt, ch, Finset.univ_eq_empty, Finset.sum_empty, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  rw [Measure.pi_of_empty]
  simp

theorem complex_units_mul_eq_one_of_mul_eq_one {K a b c z : Type} [Field K] [Fintype b] [DecidableEq b] [Fintype c] [Fintype z] (B : Matrix a z K)
    (M : Matrix z b K) (β : Matrix b c K) (γ : Matrix c b K) (h : β * γ = 1) : B * (M * β) * γ = B * M := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]

variable {D : D7} (p : Place D k)

theorem iota_mul (x : k) (b : AE D) : p.ι x * b = p.ι (x * p.π b) := by
  have h1 : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]
  conv_rhs => rw [← p.π_ι x, ← RingHom.map_mul, p.ι_π, ← mul_assoc, h1]

theorem splitLocalPlace_up_wittExtendByZero_rankZero {S S₀ T : HSp D} (d : HypDec S S₀ 0) (F₀ : GlobalTheory.LocMod.Frame k S₀.rank n) (F : GlobalTheory.LocMod.Frame k S.rank (n ⊕ Fin 0))
    (FT : GlobalTheory.LocMod.Frame k T.rank Z) (hF : ∀ r a, F.β r (Sum.inl a) = (d.i₀.map p.pr * F₀.β) r a) (x : Matrix Z n k) :
    d.ext0 T (p.up F₀ FT x) = p.up F FT (fromCols x 0) := by
  have h1 : d.q0.map p.pr * d.i₀.map p.pr = 1 := by
    have := congrArg (fun M : Matrix (Fin S₀.rank) (Fin S₀.rank) (AE D) => M.map p.π) d.p0_j0
    simp only [Matrix.map_mul] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have h2 : F.β = fromCols (d.i₀.map p.pr * F₀.β) 0 := by
    ext r (a | a)
    · simpa using hF r a
    · exact a.elim0
  have h3 : x * F₀.γ * d.q0.map p.pr * F.β = fromCols x 0 := by
    rw [h2, Matrix.mul_fromCols, Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc (d.q0.map p.pr), h1, Matrix.one_mul,
      Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have h4 : FT.β * fromCols x 0 * F.γ = FT.β * x * F₀.γ * d.q0.map p.pr := by
    rw [← h3]
    exact (complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ F.βγ).trans (by simp only [Matrix.mul_assoc])
  unfold Place.up
  refine Eq.trans ?_ (congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) k => M.map p.ι) h4.symm)
  ext i j
  show ((FT.β * x * F₀.γ).map p.ι * (d.q0.map (incA D)) : Matrix _ _ (AE D)) i j = _
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun l _ => iota_mul p _ _

theorem splitLocalPlace_isModel_wittExtendByZero_rankZero (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} (d : HypDec S S₀ 0) (F₀ : GlobalTheory.LocMod.Frame k S₀.rank n)
    (F : GlobalTheory.LocMod.Frame k S.rank (n ⊕ Fin 0)) (FT : GlobalTheory.LocMod.Frame k T.rank Z)
    (hF : ∀ r a, F.β r (Sum.inl a) = (d.i₀.map p.pr * F₀.β) r a) (Tm) (hT : p.IsModel ψ F FT Tm) :
    ∃ T₀, p.IsModel ψ F₀ FT T₀ ∧ (∀ Φ : SB (Matrix Z (n ⊕ Fin 0) k), ∃ Ψ : SB (Matrix Z n k), ∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) ∧
      ∀ Φ Ψ, (∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) → (fun w => Tm Φ (d.ext0 T w)) = T₀ Ψ := by
  haveI := t2Space k
  have c1 : Continuous fun z : Matrix Z (n ⊕ Fin 0) k => z.toCols₁ := by
    refine continuous_matrix fun i j => ?_
    exact continuous_id.matrix_elem i (Sum.inl j)
  have c2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k) := by
    refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_id.matrix_elem i j
    · exact j.elim0
  have e1 : ∀ z : Matrix Z (n ⊕ Fin 0) k, fromCols z.toCols₁ 0 = z := fun z => by
    ext i (j | j)
    · rfl
    · exact j.elim0
  let E : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix Z (n ⊕ Fin 0) k) :=
    { toFun := fun Ψ => ⟨fun z => Ψ.1 z.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 c1 c2 e1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearMap.funLeft ℂ ℂ (d.ext0 T) ∘ₗ Tm ∘ₗ E, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩,
    fun Φ => ⟨⟨fun x => Φ.1 (fromCols x 0), GlobalTheory.FinPl.Comm.comp_mem_SB Φ.2 c2 c1 fun _ => rfl⟩, fun _ => rfl⟩, fun Φ Ψ h => ?_⟩
  · exact GlobalTheory.WeilSrc.Zero.theta_eqv d (hT.theta (E Ψ))
  · have := hT.trans (fromCols x 0) (E Ψ) (E Ψ') fun t => h t.toCols₁
    show (fun w => Tm (E Ψ') (d.ext0 T w)) = heisO ψ S₀ T _ fun w => Tm (E Ψ) (d.ext0 T w)
    rw [this, ← splitLocalPlace_up_wittExtendByZero_rankZero p d F₀ F FT hF]
    exact GlobalTheory.WeilSrc.Zero.heisO_eqv d _ _
  · have hs : ∀ a b : WO S₀ T, symplO S T (d.ext0 T a) (d.ext0 T b) = symplO S₀ T a b := fun a b => by
      have h2 : algebraMap D.host.F (AF D.host.F) 2 * algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
        rw [← map_mul]; norm_num
      have h3 := congrArg (algebraMap D.host.F (AF D.host.F) 2 * ·) (d.wittDecomp_sympl_extAnisotropic_extAnisotropic T a b)
      simpa only [symplOH, ← mul_assoc, h2, one_mul] using h3
    have := hT.modul (d.ext0 T y) (fun i j => GlobalTheory.WeilSrc.entries_fix_right _ hy d.p0 i j) (E Ψ) (E Ψ') fun t => by
      show Ψ'.1 t.toCols₁ = _ * Ψ.1 t.toCols₁
      rw [h, ← hs, splitLocalPlace_up_wittExtendByZero_rankZero p d F₀ F FT hF, e1]
    show (fun w => Tm (E Ψ') (d.ext0 T w)) = heisO ψ S₀ T _ fun w => Tm (E Ψ) (d.ext0 T w)
    rw [this]
    exact GlobalTheory.WeilSrc.Zero.heisO_eqv d _ _
  · have : Φ = E Ψ := Subtype.ext (funext fun z => by
      show Φ.1 z = Ψ.1 z.toCols₁
      rw [h, e1])
    rw [this]
    rfl

end Local

variable {D : D7} {c : Comm D} {v : VCom c}

theorem lst_theta (hc : c.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (hτ : (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram)
    (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) {X₁ X₂} (h₁ : IsThetaFunO c.ψ _ _ X₁) (h₂ : IsThetaFunO c.ψ _ _ X₂) :
    (∀ y, IsThetaFunO c.ψ _ _ fun u => c.lst j h (v.τ j h) s₁ X₁ X₂ u y) ∧
      ∀ u, IsThetaFunO c.ψ _ _ (c.lst j h (v.τ j h) s₁ X₁ X₂ u) := by
  have hΞ := ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).1 0 _ _ s₁).Heisenberg₂.theta X₁ h₁
  have hΦ := GlobalTheory.WeilSrc.Zero.theta_eqv (c.jac j 0 h).d h₂
  refine ⟨fun y => ?_, fun u => ?_⟩
  · exact GlobalTheory.LastSeeSaw.isThetaFunO_const_mul _ (GlobalTheory.BoxSlice.isThetaFunO_slice_left (c.bes j 0 h).o hΞ
      (kap (v.τ j h) (c.X (j + 1)) ((c.oT (j + 1 + 1) h).resT (c.X (j + 1)) y).2))
  · exact OrthDec.isThetaFunO_boxT (c.oT (j + 1 + 1) h) hΦ
      (GlobalTheory.LastSeeSaw.isThetaFunO_kap (v.τ j h) hτ (c.X (j + 1)) (GlobalTheory.BoxSlice.isThetaFunO_slice_right (c.bes j 0 h).o hΞ u))

set_option maxHeartbeats 1000000 in

theorem one_place (hc : c.Is) (hv : v.Is) (G : GLoc v) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (hr : c.Lz.rank = 1)
    (hτ : (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram)
    (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) (e : WO (c.V (j + 1)) c.T →₀ ℂ) (he : HEq e G.egT) {X₁ X₂}
    (h₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) X₁) (h₂ : Vac c.ψ _ _ (v.N (j + 1)) v.NT (· = G.q.v) X₂) :
    c.lst j h (v.τ j h) s₁ (comb c.ψ _ _ (G.eg j) X₁) (comb c.ψ _ _ e X₂) =
      biComb c.ψ _ _ _ (G.cg j) (G.cg (j + 1)) (c.lst j h (v.τ j h) s₁ X₁ X₂) := by
  obtain rfl : j = G.s := by have := G.hs; omega
  obtain rfl : e = G.egT := eq_of_heq he
  have hs := G.hs
  have hsc : G.sc G.s ≠ 0 := fun h0 => by simpa [h0] using G.sc_unit G.s
  have hreg : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  obtain ⟨T₁, hT₁, hX₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY G.s (0 + 1) (by omega)) (G.FY (G.s + 1) 0 rfl) c.ψ G.S.ψ
    hc.std G.char G.S.cond _ _ (hv.sd G.s (by omega)) (hv.sd (G.s + 1) (by omega)) (G.latY _ _ _) (G.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY (G.s + 1) 0 rfl) G.FT c.ψ G.S.ψ
    hc.std G.char G.S.cond _ _ (hv.sd (G.s + 1) (by omega)) hv.sdT (G.latY _ _ _) G.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D G.k (ofSplit G.q) _ 0 (G.sc G.s) hsc).1 (c.B G.s 0 h)
    (G.FX G.s (by omega))).1
  have hjac := G.jac G.s 0 h 0 rfl
  obtain ⟨U₁, hU₁, hfl⟩ := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D) G.k (ofSplit G.q) G.ν G.unitVol.1
    c.ψ G.S.ψ G.char 0 (c.B G.s 0 h) (c.J G.s 0 h) s₁ (G.sc G.s) hsc _ _ 0 (G.FX G.s (by omega)) F₀
    (G.FY G.s (0 + 1) (by omega)) (G.FX (G.s + 1) le_rfl) (G.FY (G.s + 1) 0 rfl) hF₀ (G.bes G.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, hres, hext⟩ := splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit G.q) c.ψ (c.jac G.s 0 h).d (G.FX (G.s + 1) le_rfl) (G.FY (G.s + 1) 0 rfl)
    G.FT hjac.2.1 T₂ hT₂
  let Φ₁ : SB _ := ⟨_, hreg.1 G.s 0 rfl⟩
  let Φ₂ : SB _ := ⟨_, hreg.2.1⟩
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := G.k) (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0)
    (XIx (Fin D.R.k) (Fin D.R.t) G.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := G.k) (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := G.k) (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1))
    (XIx (Fin D.R.k) (Fin D.R.t) G.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := G.k) (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2))
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1))⟩
  let Ψ₁ : SB _ := ⟨_, ((GlobalTheory.LocFlat.flat_SB_onto G.k G.S.ψ G.ν G.S.cond.continuous G.unitVol.1 _ _ 0 (0 + 1) le_rfl).1
    le_rfl).1 _ Φ₁.2⟩
  obtain ⟨Ψ₂, hΨ₂⟩ := hres Φ₂
  have a₁ : comb c.ψ _ _ (G.eg G.s) X₁ = T₁ Φ₁ := by
    rw [← hX₁ O₁ rfl]
    exact ((G.eg_is G.s 0 rfl).2 T₁ hT₁ O₁ Φ₁ rfl rfl).symm
  have a₂ : comb c.ψ _ _ G.egT X₂ = T₂ Φ₂ := by
    rw [← hX₂ O₂ rfl]
    exact (G.egT_is.2 T₂ hT₂ O₂ Φ₂ rfl rfl).symm
  have b₁ : flatBF s₁ (T₁ Φ₁) = U₁ Ψ₁ := hfl Φ₁ Ψ₁ rfl
  have b₁' : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator G.k G.S.ψ G.ν G.S.cond G.unitVol (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1))
      (XIx (Fin D.R.k) (Fin D.R.t) G.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext Φ₂ Ψ₂ hΨ₂
  have b₂' := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[G.k]) ↔
        ∀ r (q : XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[G.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    classical
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  have key := GlobalTheory.LastTwoSteps.gLast D (GlobalTheory.T.splitPlace_doubleStep_kernel_localModels D) GlobalTheory.SymChain.atMostOne_holds G.k G.ν G.unitVol (ofSplit G.q) G.s D.R.k G.S
    (Fin D.R.t) c.ψ hc.std G.char 0 (c.B G.s 0 h) (c.X (G.s + 1)) (c.X (G.s + 1 + 1)) c.T c.Lz (c.oT (G.s + 1 + 1) h) (v.τ G.s h)
    hr hτ (G.sc G.s) G.z₀ hsc (G.tau h) (G.FX G.s (by omega)) F₀ (G.FX (G.s + 1) le_rfl) G.FT G.FM hF₀ G.last
    (G.cg G.s) (G.cg (G.s + 1)) G.cg_pen G.cg_top U₁ U₂ hU₁ hU₂ Ψ₁ Ψ₂ O₁' O₂'
    (fun x => by
      rw [Chain.Psi, GlobalTheory.SplitWeil.Model.om_one]
      exact flCol_one _ _ _ x) hΨ₂ rfl rfl
  rw [a₁, a₂, ← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
  unfold Comm.lst
  rw [b₁, b₁', b₂, b₂']
  exact key

theorem vac_foldr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (pl : ι → Pl D)
    (e : ι → WO S T →₀ ℂ) (he : ∀ i, CombAt (· = pl i) (e i)) (LS LT) (a : ι) (l : List ι) (hl : ∀ i ∈ l, pl i ≠ pl a) (f)
    (hf : Vac ψ S T LS LT (· = pl a) f) : Vac ψ S T LS LT (· = pl a) (l.foldr (fun i f' => comb ψ S T (e i) f') f) := by
  induction l with
  | nil => exact hf
  | cons b l ih =>
    exact ((GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T (· = pl b) (· = pl a) fun p h1 h2 => hl b (by simp) (h1.symm.trans h2)).2.1 (e b)
      (he b)).2 _ _ _ (ih fun i hi => hl i (by simp [hi]))

theorem vac_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS LT} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {P : Pl D → Prop} {w : Pl D} (hw : P w) {f} (hf : Vac ψ S T LS LT P f) :
    Vac ψ S T LS LT (· = w) f := by
  have e : (fun p => p = w ∨ (P p ∧ p ≠ w)) = P := funext fun p => propext
    ⟨fun h => h.elim (fun h => h ▸ hw) And.left, fun h => (em (p = w)).imp id fun h' => ⟨h, h'⟩⟩
  have := (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T (· = w) (fun p => P p ∧ p ≠ w) fun p h1 h2 => h2.2 h1).2.2.2.2 LS LT f hS hT
  rw [e] at this
  exact (this.1 hf).1

theorem last_value : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 →
    (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) Ψ₂ →
    c.lst j h (v.τ j h) s₁ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eGT j h) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.lst j h (v.τ j h) s₁ Ψ₁ Ψ₂) := by
  intro D c v n G hc hv hG j h hr hτ
  refine ⟨1, one_ne_zero, fun s₁ Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
  obtain ⟨e, he, hE⟩ := hG.eGT j h
  have c₁ : ∀ i, CombAt (· = (G i).q.v) ((G i).eg j) := fun i u hu =>
    GlobalTheory.T.matrixSupportedAtPlace_of_isHalf_splitPoint D _ (G i).q _ _ u (((G i).eg_is j 0 (by have := (G i).hs; omega)).1 u hu)
  have c₂ : ∀ i, CombAt (· = (G i).q.v) (e i) := fun i => by
    obtain rfl : j = (G i).s := by have := (G i).hs; omega
    rw [eq_of_heq (he i)]
    exact fun u hu => GlobalTheory.T.matrixSupportedAtPlace_of_isHalf_splitPoint D _ (G i).q _ _ u ((G i).egT_is.1 u hu)
  have v₁ := fun i => vac_at hc.std (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) ((hG.places (G i).q.v).2 ⟨i, rfl⟩) h₁
  have v₂ := fun i => vac_at hc.std (hv.sd (j + 1) (by omega)) hv.sdT ((hG.places (G i).q.v).2 ⟨i, rfl⟩) h₂
  have key : ∀ l : List (Fin n), l.Nodup →
      c.lst j h (v.τ j h) s₁ (l.foldr (fun i f' => comb c.ψ _ _ ((G i).eg j) f') Ψ₁)
        (l.foldr (fun i f' => comb c.ψ _ _ (e i) f') Ψ₂) =
      l.foldr (fun i C => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C) (c.lst j h (v.τ j h) s₁ Ψ₁ Ψ₂) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      have hne : ∀ i ∈ l, (G i).q.v ≠ (G a).q.v := fun i hi h0 => ha (hG.inj h0 ▸ hi)
      rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ← ih hl']
      exact one_place hc hv (G a) j h hr hτ s₁ (e a) (he a)
        (vac_foldr hc.std (fun i => (G i).q.v) _ c₁ _ _ a l hne _ (v₁ a))
        (vac_foldr hc.std (fun i => (G i).q.v) _ c₂ _ _ a l hne _ (v₂ a))
  have hθ := lst_theta hc j h hτ s₁ h₁.1 h₂.1
  rw [one_smul, hG.eG j (by omega) _ h₁.1, hE _ h₂.1, key _ (List.nodup_finRange n),
    biComb_eq_foldr D c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) ((List.finRange n).map fun i => ((G i).cg j, (G i).cg (j + 1)))
      (fun f hf => by rw [hG.dG j (by omega) f hf, List.foldr_map])
      (fun f hf => by rw [hG.dG (j + 1) (by omega) f hf, List.foldr_map]) _ hθ.1 hθ.2, List.foldr_map]

end GlobalTheory.LevelLast
end
