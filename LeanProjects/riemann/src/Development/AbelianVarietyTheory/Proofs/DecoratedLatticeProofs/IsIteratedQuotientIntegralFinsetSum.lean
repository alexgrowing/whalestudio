import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Vac Moves InK Lat Pl latV idAt idOff intAt grpAt grpOff MxAt hand0 SplitPt extS extT)

noncomputable section
namespace GlobalTheory.QLawPf

section Iter
variable {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
    [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂}
    {μ₂ : Measure G₂}

theorem isIteratedQuotientIntegral_finset_sum {ι : Type} (s : Finset ι) (F : ι → G₁ → G₂ → ℂ) (z : ι → ℂ)
    (hF : ∀ i ∈ s, Iter2 ρ₁ μ₁ ρ₂ μ₂ (F i) (z i)) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => ∑ i ∈ s, F i x y) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨0, IsQuotIntL1.zero, fun q => IsQuotIntL1.zero⟩
  | insert a s ha ih =>
    obtain ⟨g, hg, hq⟩ := hF a (Finset.mem_insert_self a s)
    obtain ⟨g', hg', hq'⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact ⟨g + g', hg.add hg', fun q => (hq q).add (hq' q)⟩

theorem isIteratedQuotientIntegral_const_mul {F : G₁ → G₂ → ℂ} {z : ℂ} (a : ℂ) (hF : Iter2 ρ₁ μ₁ ρ₂ μ₂ F z) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => a * F x y) (a * z) := by
  obtain ⟨g, hg, hq⟩ := hF
  exact ⟨a • g, hg.smul a, fun q => (hq q).smul a⟩

end Iter

variable {D : D7}

theorem moves_iff_forall {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) (P : Pl D → Prop) (g : GA D S) :
    Moves S g L L P ↔ ∀ v, P v → Moves S g L L (· = v) := by
  have hP := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L z hL.1
  have hmv := fun (R : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D R) =>
    GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S R g hy
  constructor
  · intro h v hv y hy
    have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (z ∈ latV S L P ↔ z ∈ latV S L (· = v)) := by
      intro z hz
      rw [hP, ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L z hL.1]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨hz, fun w hw e he => h w (hw ▸ hv) e he⟩
      · rintro ⟨_, h⟩
        refine ⟨fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hz i), fun w _ e he => ?_⟩
        by_cases hwv : w = v
        · exact h w hwv e he
        · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
          have hzero : e • z = 0 := by
            funext i
            have h1 : ε * e = e := (hAt e).1 he.1
            have h2 : ε * z i = 0 := (hOff (z i)).1 (GlobalTheory.FinPl.PlacesAdeles.idAt_le_idOff hwv (hz i))
            show e * z i = 0
            rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
          rw [hzero]
          exact (latV S L (· = w)).zero_mem
    rw [← key y hy, ← key _ (hmv _ y hy)]
    exact h y fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hy i)
  · intro h y hy
    rw [hP y, hP (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w hw (e • y) hey).1 (hy' w hw e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w hw (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w hw e he

theorem intAt_iff_moves {V : HSp D} {L : Lat V} {k Y : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Fintype Y] [DecidableEq Y] (v : Pl D) (gl : GL Y k →* GA D V)
    (hr : gl.range = grpAt V (· = v)) (hx : ∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ grpOff V (· = v))
    (hK : ∀ g, g ∈ KO k Y ↔ InK V L (· = v) (gl g)) (x : GA D V) : IntAt v gl x ↔ Moves V x L L (· = v) := by
  constructor
  · rintro ⟨κ, hκ, hy⟩
    have := GlobalTheory.FinPl.PlacesAdeles.moves_mul (GlobalTheory.FinPl.PlacesAdeles.moves_off (L := L) hy) ((hK κ).1 hκ).2
    simpa using this
  · intro h
    obtain ⟨g, hg, -⟩ := hx x
    refine ⟨g, (hK g).2 ⟨hr ▸ ⟨g, rfl⟩, ?_⟩, hg⟩
    have := GlobalTheory.FinPl.PlacesAdeles.moves_mul (GlobalTheory.FinPl.PlacesAdeles.moves_off (L := L) (inv_mem hg)) h
    simpa using this

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem vac_single (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {P : Pl D → Prop} {v : Pl D} (hv : P v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) :
    Vac ψ S T LS LT (· = v) f := by
  have key := (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T (· = v) (fun p => P p ∧ p ≠ v) (fun p hp hn => hn.2 hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => p = v ∨ (P p ∧ p ≠ v)) = P := funext fun p => propext
    ⟨fun h => h.elim (fun h => h ▸ hv) (·.1), fun h => (em (p = v)).imp id fun h' => ⟨h, h'⟩⟩
  rw [e] at key
  exact (key.1 hf).1

theorem isFinComb_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, IsHalf (q.e + cA D q.e) u) : IsFinComb c := by
  intro u hu
  ext i j
  exact (RingHom.mem_ker).1 (Ideal.mem_inf.1 (GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q _ _ u (hc u hu) i j)).1

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ c ∈ l, IsFinComb c) : IsFinComb (aconv l) := by
  induction l with
  | nil =>
    intro u hu
    have : u = 0 := by simpa [aconv] using hu
    subst this
    ext i j
    simp
  | cons c l ih =>
    intro u hu
    have e1 : aconv [aconv l] = aconv l := by
      show (aconv l).sum (fun g a => (Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) = aconv l
      have : ∀ (g : WO S T) (a : ℂ), ((Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) =
          Finsupp.single g a := fun g a => by rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
      simp only [this, Finsupp.sum_single]
    have e2 : aconv (c :: l) = aconv [c, aconv l] := by
      show _ = c.sum fun g a => (aconv [aconv l]).sum fun h b => Finsupp.single (g + h) (a * b)
      rw [e1]; rfl
    rw [e2] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    have h1 := hl c List.mem_cons_self a ha
    have h2 := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) b hb
    ext i j
    have h3 : infPart D (a i j) = 0 := congrFun (congrFun h1 i) j
    have h4 : infPart D (b i j) = 0 := congrFun (congrFun h2 i) j
    show infPart D (a i j + b i j) = 0
    rw [RingHom.map_add, h3, h4, add_zero]

theorem aconv_single_cons {G : Type} [AddMonoid G] (l : List (G →₀ ℂ)) : aconv (Finsupp.single 0 1 :: l) = aconv l := by
  show (Finsupp.single (0 : G) (1 : ℂ)).sum (fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)) = aconv l
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem comb_single_zero (S T : HSp D) (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb, Finsupp.support_single_ne_zero, GlobalTheory.BoxSlice.heisO_zero']

theorem biComb_single_zero (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (Finsupp.single 0 1) (Finsupp.single 0 1) C = C := by
  funext u v
  simp only [biComb, comb_single_zero]

theorem sum_support_smul {G M : Type} [AddCommMonoid M] [Module ℂ M] (a : ℂ) (e : G →₀ ℂ) (F : G → M) :
    ∑ g ∈ (a • e).support, (a • e) g • F g = a • ∑ g ∈ e.support, e g • F g := by
  show (a • e).sum (fun g b => b • F g) = _
  rw [Finsupp.sum_smul_index' (h := fun g b => b • F g) (fun _ => zero_smul _ _), Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by simp [mul_smul]

theorem comb_smul_left (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : comb ψ S T (a • c) f = a • comb ψ S T c f :=
  sum_support_smul a c fun u => heisO ψ S T u f

theorem trc_smul_left {V : HSp D} (a : ℂ) (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (a • e) f = a • trc e f :=
  sum_support_smul a e fun g => rTrans g f

theorem biComb_smul_left (A S A' : HSp D) (a b : ℂ) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (a • c) (b • c') C = (a * b) • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, comb_smul_left]
  have : (fun u' => (b • comb ψ S A' c' (C u')) v) = b • fun u' => comb ψ S A' c' (C u') v := rfl
  rw [this, GlobalTheory.AvgMid.comb_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, biComb]

theorem isFinComb_extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ} (hc : IsFinComb c) :
    IsFinComb (extS o T c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  change (w ⬝ o.pA + (0 : WO L T) ⬝ o.pB).map (infPart D) = 0
  rw [Matrix.zero_mul, add_zero, Matrix.map_mul, hc w hw, Matrix.zero_mul]

theorem isFinComb_extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ} (hc : IsFinComb c) :
    IsFinComb (extT o S c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  change (o.jA ⬝ w + o.jB ⬝ (0 : WO S L)).map (infPart D) = 0
  rw [Matrix.mul_zero, add_zero, Matrix.map_mul, hc w hw, Matrix.mul_zero]

theorem per_sum (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {f : GA D B.V → ℂ} (hf : IsContAut B.V f) {I : Type}
    [Fintype I] (φ : I → GA D B.A → ℂ) (hφ : ∀ i, IsContAut B.A (φ i)) : B.per ψ (∑ i, φ i) f = ∑ i, B.per ψ (φ i) f := by
  simpa using perSum_all D ψ hψ ρ B f hf I Finset.univ (fun _ => 1) φ fun i _ => hφ i

section Step
variable {σ : ℕ} (S : Dbl2 ψ σ)

def HandIsLift : Prop :=
  ∀ (φ : GA D S.B.A → ℂ) (Ξ₁ : WO S.B.V₀ S.J.W₀ → ℂ) (Ξ₂ : WO S.J.W₀ S.B'.V₀ → ℂ), IsContAut S.B.A φ →
    IsThetaFunO ψ _ _ Ξ₁ → IsThetaFunO ψ _ _ Ξ₂ →
      hand0 S.s₁ S.s₂ S.l S.vL φ Ξ₁ Ξ₂ = biLift S.oma S.omb S.B.vA S.J.v0 φ (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL Ξ₁ Ξ₂)

variable {S}

theorem theta_flatBF {f : WO S.B.V S.J.W → ℂ} (hf : IsThetaFunO ψ _ _ f) : IsThetaFunO ψ _ _ (flatBF S.s₁ f) :=
  (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ _ _ S.s₁ f hf

theorem theta_flatFB {f : WO S.J.W S.B'.V → ℂ} (hf : IsThetaFunO ψ _ _ f) : IsThetaFunO ψ _ _ (flatFB S.s₂ f) :=
  (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 _ _ _ S.s₂ f hf

theorem val_eq_hand (hS : HandIsLift S) {Φ₁ : WO S.B.V S.J.W → ℂ} {Φ₂ : WO S.J.W S.B'.V → ℂ} (h₁ : IsThetaFunO ψ _ _ Φ₁)
    (h₂ : IsThetaFunO ψ _ _ Φ₂) {φ : GA D S.B.A → ℂ} (hφ : IsContAut _ φ) (f : GA D S.B'.V → ℂ) (g x y) :
    S.val (Finsupp.single 0 1) (Finsupp.single 0 1) Φ₁ Φ₂ φ f g x y =
      S.B'.per ψ (Chain.hand S.s₁ S.s₂ S.l S.vL Φ₁ Φ₂ φ g x y) (rTrans y f) := by
  unfold Dbl2.val Dbl2.con
  rw [biComb_single_zero, ← hS φ _ _ hφ (theta_flatBF (S.s₁.weil.om_pres _ _ h₁)) (theta_flatFB (S.s₂.weil.om_pres _ _ h₂))]
  rfl

theorem val_one (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Φ₁ : WO S.B.V S.J.W → ℂ) (Φ₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) :
    S.val c₁ c₂ Φ₁ Φ₂ φ f 1 1 1 = S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂
      (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ Φ₁) (flatFB S.s₂ Φ₂)))) f := by
  unfold Dbl2.val Dbl2.con
  have e1 : S.s₁.om (1, 1) Φ₁ = Φ₁ := by rw [Prod.mk_one_one, map_one]; rfl
  have e2 : S.s₂.om (1, 1) Φ₂ = Φ₂ := by rw [Prod.mk_one_one, map_one]; rfl
  have e3 : rTrans 1 f = f := by funext z; simp [rTrans]
  rw [e1, e2, e3]

theorem contAut_lift (hψ : IsStdChar D ψ (-1)) (hS : HandIsLift S) {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ}
    (hc₁ : IsFinComb c₁) (hc₂ : IsFinComb c₂) {Φ₁ : WO S.B.V S.J.W → ℂ} {Φ₂ : WO S.J.W S.B'.V → ℂ} (h₁ : IsThetaFunO ψ _ _ Φ₁)
    (h₂ : IsThetaFunO ψ _ _ Φ₂) {φ : GA D S.B.A → ℂ} (hφ : IsContAut _ φ) :
    IsContAut S.B'.A (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂
      (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ Φ₁) (flatFB S.s₂ Φ₂)))) := by
  have t₁ := GlobalTheory.AvgMid.theta_comb hψ (isFinComb_extS S.B.o S.J.W₀ hc₁) (theta_flatBF h₁)
  have t₂ := GlobalTheory.AvgMid.theta_comb hψ (isFinComb_extT S.B'.o S.J.W₀ hc₂) (theta_flatFB h₂)
  rw [← (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hψ _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (theta_flatBF h₁) (theta_flatFB h₂)).2.1, ← hS φ _ _ hφ t₁ t₂]
  exact GlobalTheory.FinPl.Comm.contAut_hand0 _ _ _ _ hφ t₁ t₂

end Step

end GlobalTheory.QLawPf
end
