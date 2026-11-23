import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParamStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinDer

variable {D : D7}

theorem termBound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (hv : KDecay M v) (b : ∀ τ, M.H τ)
    (hb : ∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ :=
  GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay D θ hθ V S M K v hv b hb

theorem sumBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ →
    ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) →
    (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) →
    (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V,
    Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A :=
  GlobalTheory.T.coefficientPoincareSeries_summable_majorant

theorem termDeriv (hHC : GlobalTheory.Published.HarishChandraModules) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) (hb : b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : GA D V) :
    HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s))
      (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 :=
  GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam D hHC θ hθ V S M K v b τ hb X hX x

theorem onePDecay (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 →
      ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ :=
  GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul D θ hθ V τ X hX N

theorem finE_mul_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) (t : ℝ) :
    Lev.finE V (x * oneP θ V τ X t) = Lev.finE V x := by
  have h : finHom V (oneP θ V τ X t) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
  show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X t) = (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) x
  rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X t), h, map_one, mul_one]

theorem poin_smooth_growth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c a
  obtain ⟨C₀, A, hB⟩ := sumBound D θ hθ V Λ hΛ 𝔪 c
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK

  have hsum : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, ∀ g,
      Summable (fun γ : GQ V => ‖coef θ M K v b (c * (γ : GA D V) * g)‖) ∧
      ∑' γ : GQ V, ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * height V g ^ A := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := termBound θ hθ M K v hv b hb
    refine ⟨C * C₀, fun g => ?_⟩
    refine hB (fun x => ‖coef θ M K v b x‖) C (fun _ => norm_nonneg _) (fun x hx => ?_) hC g
    simp only [coef, if_neg hx, norm_zero]
  have grow : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ModGrowthExp V A (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC⟩ := hsum b hb
    exact ⟨C, fun g => (norm_tsum_le_tsum_norm (hC g).1).trans (hC g).2⟩

  have der : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ τ, ∀ X ∈ lieAt V τ, ∀ g,
      HasDerivAt (fun t : ℝ => poin θ M K v c b (g * oneP θ V τ X t))
        (poin θ M K v c (Function.update b τ (dRep (M.rep τ) X (b τ))) g) 0 := by
    intro b hb τ X hX g
    set b' := Function.update b τ (dRep (M.rep τ) X (b τ)) with hb'd
    have hb' : ∀ τ', b' τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ' := by
      intro τ'
      by_cases h : τ' = τ
      · subst h
        rw [hb'd, Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [hb'd, Function.update_of_ne h]
        exact hb τ'
    obtain ⟨C', hC'0, hC'⟩ := termBound θ hθ M K v hv b' hb'
    obtain ⟨L, hL0, hL⟩ := onePDecay θ hθ V τ hX (2 * V.rank ^ 2 + 1)
    set u : GA D V → ℝ := fun x => if Lev.finE V x ∈ K then C' * L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ else 0
      with hu
    have hprod : ∀ x : GA D V, 0 ≤ ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
      Finset.prod_nonneg fun τ' _ => inv_nonneg.2 (pow_nonneg (by unfold hsn; positivity) _)
    have hu0 : ∀ x, 0 ≤ u x := fun x => by
      simp only [hu]; split_ifs
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
      · exact le_rfl
    have huK : ∀ x, Lev.finE V x ∉ K → u x = 0 := fun x hx => by simp only [hu, if_neg hx]
    have huC : ∀ x, u x ≤ (C' * L) * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x => by
      simp only [hu]; split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
    have hbd : ∀ (x : GA D V) (y : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 → ‖coef θ M K v b' (x * oneP θ V τ X y)‖ ≤ u x := by
      intro x y hy
      by_cases hx : Lev.finE V x ∈ K
      · have h1 := hC' (x * oneP θ V τ X y)
        have h2 := hL x y (abs_lt.2 ⟨hy.1, hy.2⟩)
        simp only [hu, if_pos hx]
        calc _ ≤ _ := h1
          _ ≤ C' * (L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) := mul_le_mul_of_nonneg_left h2 hC'0
          _ = _ := by ring
      · have : coef θ M K v b' (x * oneP θ V τ X y) = 0 := by
          simp only [coef, finE_mul_oneP, if_neg hx]
        rw [this, norm_zero]
        exact hu0 x
    have hS := (hB u (C' * L) hu0 huK huC g).1
    obtain ⟨Cb, hCb⟩ := hsum b hb
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun (γ : GQ V) (s : ℝ) => coef θ M K v b (c * (γ : GA D V) * g * oneP θ V τ X s))
      (g' := fun (γ : GQ V) (s : ℝ) => coef θ M K v b' (c * (γ : GA D V) * g * oneP θ V τ X s)) (t := Set.Ioo (-1 : ℝ) 1)
      (y₀ := 0) (y := 0) hS isOpen_Ioo isPreconnected_Ioo
      (fun γ y _ => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun x => termDeriv hHC θ hθ M K v b τ (hb τ) hX x) _ y)
      (fun γ y hy => hbd _ y hy) (by norm_num)
      (by simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using (hCb g).1.of_norm) (by norm_num)
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [poin, mul_assoc]
  refine ⟨?_, ⟨A, fun l hl => ?_⟩, ?_⟩
  ·
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V
      {φ | ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧ φ = poin θ M K v c b} ?_ ?_ _ ⟨_, fun τ => (a τ).2, rfl⟩
    · rintro φ ⟨b, hb, rfl⟩
      exact (((GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c).1 fun τ => ⟨b τ, hb τ⟩).1).cont
    · rintro φ ⟨b, hb, rfl⟩ τ X hX
      refine ⟨_, ⟨Function.update b τ (dRep (M.rep τ) X (b τ)), fun τ' => ?_, rfl⟩, der b hb τ X hX⟩
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [Function.update_of_ne h]
        exact hb τ'
  ·
    have claim : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧
          l.foldr (fun p f => Rder θ V p.1 p.2 f) (poin θ M K v c fun τ => a τ) = poin θ M K v c b := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
      | cons p l ih =>
        intro hl'
        obtain ⟨b, hb, e⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        have hX : p.2 ∈ lieAt V p.1 := hl' p List.mem_cons_self
        refine ⟨Function.update b p.1 (dRep (M.rep p.1) p.2 (b p.1)), fun τ' => ?_, ?_⟩
        · by_cases h : τ' = p.1
          · rw [h, Function.update_self]
            exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M p.1 hX (hb p.1)
          · rw [Function.update_of_ne h]
            exact hb τ'
        · rw [List.foldr_cons, e]
          funext g
          exact (der b hb p.1 p.2 hX g).deriv
    obtain ⟨b, hb, e⟩ := claim l hl
    rw [e]
    exact grow b hb
  ·
    intro τ X hX w hw
    funext g
    have e : (fun τ' => (Function.update a τ w τ' : M.H τ')) =
        Function.update (fun τ' => (a τ' : M.H τ')) τ (dRep (M.rep τ) X (a τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        simp [hw]
      · simp [Function.update_of_ne h]
    rw [e]
    exact ((der (fun τ' => a τ') (fun τ' => (a τ').2) τ X hX g).deriv).symm

end GlobalTheory.PoinDer

end
