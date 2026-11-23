import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineGramCurvatureAllFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentsGeneratingDivisorAtPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology

namespace GlobalTheory.HodgeLocal

open scoped ComplexOrder

open Matrix GlobalTheory.HermFrame in

theorem isPosFrame_smul {ι : Type} [Fintype ι] {m : Type} [Fintype m] [DecidableEq m] {U : Set (ι → ℂ)}
    {H : (ι → ℂ) → Matrix m m ℂ} (h : IsPosFrame U H) {a : ℝ} (ha : 0 < a) :
    IsPosFrame U (fun x => (a : ℂ) • H x) := by
  refine ⟨h.isOpen, fun i k => ?_, fun z hz => ?_⟩
  · simpa [Matrix.smul_apply, smul_eq_mul] using (h.smooth i k).const_smul (a : ℂ)
  · exact (h.posDef z hz).smul (by exact_mod_cast ha)

open Matrix GlobalTheory.HermFrame in

theorem isPosFrame_hodge (ι : Type) [Fintype ι] (p q : ℕ) (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (a b : ℝ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U ψ) (ha : 0 < a) (hb : 0 < b) :
    IsPosFrame U (fun x => (a : ℂ) • quotGram (ψ x)) ∧ IsPosFrame U (fun x => (b : ℂ) • -subGram (ψ x)) := by
  have hu : ∀ z ∈ U, IsUnit (subGram (ψ z)).det := fun z hz => by
    have h1 : IsUnit (-subGram (ψ z)) := (hψ.neg_sub z hz).isUnit
    rw [← isUnit_iff_isUnit_det]
    simpa using h1.neg
  have hq : IsPosFrame U fun x => quotGram (ψ x) :=
    (hψ.isHermFrame.quot hu).isPosFrame hψ.pos_quot
  have hs : IsPosFrame U fun x => -subGram (ψ x) := by
    refine ⟨hψ.isHermFrame.isOpen, fun i k => ?_, hψ.neg_sub⟩
    simpa [subGram, Matrix.toBlocks₁₁] using (hψ.isHermFrame.smooth (Sum.inl i) (Sum.inl k)).neg
  exact ⟨isPosFrame_smul hq ha, isPosFrame_smul hs hb⟩

theorem weightNormSq_smooth (n : ℕ) (ι : Type) [Fintype ι] (m : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin m) (Fin m) ℂ) (Y : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → ι → ℂ)
    (A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ) (lam : Fin m → ℝ) (y : Fin n → ℂ)
    (hH : GlobalTheory.HermFrame.IsPosFrame U H) (hA : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y U π A) (hy : y ∈ Y) :
    ContDiffAt ℝ 2 (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq H π A lam) y ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq H π A lam y := by
  have hp := fun i => GlobalTheory.ChernWeight.lineGram_pos hH hA hy i
  have hfs := GlobalTheory.ChernWeight.lineGram_smooth hH hA hy
  refine ⟨?_, Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hp i).1 _⟩
  show ContDiffAt ℝ 2 (fun x => ∏ i, (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram H π A i x () ()).re ^ (-lam i)) y
  exact contDiffAt_prod fun i _ => (hfs i).rpow_const_of_ne (hp i).1.ne'

end GlobalTheory.HodgeLocal

namespace GlobalTheory.HodgeLocal

theorem log_norm_analytic {n : ℕ} {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} (hg : AnalyticAt ℂ g y)
    (h0 : g y ≠ 0) : ContDiffAt ℝ 2 (fun v => Real.log ‖g v‖) y ∧
      ∀ w, ReciprocityTheory.AnForm.levi (fun v => Real.log ‖g v‖) y w = 0 := by
  set G : (Fin n → ℂ) → ℂ := fun v => Complex.log (g v / g y) + (Real.log ‖g y‖ : ℂ) with hGdef
  have hh : AnalyticAt ℂ (fun v => g v / g y) y := hg.div analyticAt_const h0
  have h1 : (fun v => g v / g y) y ∈ Complex.slitPlane := by
    simp [div_self h0, Complex.one_mem_slitPlane]
  have hG : AnalyticAt ℂ G y := (hh.clog h1).add analyticAt_const
  have hev : (fun v => Real.log ‖g v‖) =ᶠ[𝓝 y] fun v => (G v).re := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with v hv
    simp only [hGdef, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 h0)]
    ring
  refine ⟨?_, fun w => ?_⟩
  · exact (Complex.reCLM.contDiff.contDiffAt.comp y
      (hG.restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq hev
  · rw [ReciprocityTheory.AnForm.levi_congr hev]
    exact ReciprocityTheory.AnForm.levi_re_analytic hG w

theorem levi_sum_eq_zero {n : ℕ} {κ : Type} (s : Finset κ) (c : κ → ℝ) (φ : κ → (Fin n → ℂ) → ℝ)
    {y : Fin n → ℂ} (h : ∀ i, ContDiffAt ℝ 2 (φ i) y ∧ ∀ w, ReciprocityTheory.AnForm.levi (φ i) y w = 0) :
    ContDiffAt ℝ 2 (fun v => ∑ i ∈ s, c i * φ i v) y ∧
      ∀ w, ReciprocityTheory.AnForm.levi (fun v => ∑ i ∈ s, c i * φ i v) y w = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (contDiffAt_const (c := (0 : ℝ))), fun w => ?_⟩
    simp [ReciprocityTheory.AnForm.levi]
  | insert a s ha ih =>
    have e : (fun v => ∑ i ∈ insert a s, c i * φ i v) = fun v => (∑ i ∈ s, c i * φ i v) + c a * φ a v := by
      funext v; rw [Finset.sum_insert ha, add_comm]
    rw [e]
    refine ⟨ih.1.add (contDiffAt_const.mul (h a).1), fun w => ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (h a).1 w, ih.2 w, (h a).2 w]
    ring

end GlobalTheory.HodgeLocal

namespace GlobalTheory.HodgeLocal

theorem pairWeightNormSq_smooth : ∀ (n : ℕ) (ι : Type) [Fintype ι] (T : Type) [Fintype T] (p q : T → ℕ) (U : Set (ι → ℂ))
    (ψ : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ) ⊕ Fin (p τ)) (Fin (q τ) ⊕ Fin (p τ)) ℂ) (a b : T → ℝ)
    (Y : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → ι → ℂ)
    (AW : ∀ τ, (Fin n → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, (Fin n → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (lam : ∀ τ, Fin (p τ + q τ) → ℝ) (y : Fin n → ℂ),
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U (ψ τ)) → (∀ τ, 0 < a τ) → (∀ τ, 0 < b τ) →
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y U π (AW τ)) → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y U π (Aω τ)) → y ∈ Y →
    ContDiffAt ℝ 2 (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x))
        (fun τ x => (b τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam) y ∧
      0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x))
        (fun τ x => (b τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam y := by
  intro n ι _ T _ p q U ψ a b Y π AW Aω lam y hψ ha hb hAW hAω hy
  have hW := fun τ => weightNormSq_smooth n ι (p τ) U _ Y π (AW τ) (fun i => lam τ (Fin.castAdd (q τ) i)) y
    (isPosFrame_hodge ι (p τ) (q τ) U (ψ τ) (a τ) (b τ) (hψ τ) (ha τ) (hb τ)).1 (hAW τ) hy
  have hω := fun τ => weightNormSq_smooth n ι (q τ) U _ Y π (Aω τ) (fun i => lam τ (Fin.natAdd (p τ) i)) y
    (isPosFrame_hodge ι (p τ) (q τ) U (ψ τ) (a τ) (b τ) (hψ τ) (ha τ) (hb τ)).2 (hAω τ) hy
  refine ⟨?_, Finset.prod_pos fun τ _ => mul_pos (hW τ).2 (hω τ).2⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq
  exact contDiffAt_prod fun τ _ => (hW τ).1.mul (hω τ).1

end GlobalTheory.HodgeLocal

theorem GlobalTheory.HodgeLocal.hodge_potential_local : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ u : D.what₂.Tau → Fin O.Y.N → ℝ, GlobalTheory.FlagPoly.Dom u → ∀ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) →
  ∃ (T' : Type) (_ : Fintype T') (p q : T' → ℕ) (ι : Type) (_ : Fintype ι) (U : Set (ι → ℂ))
    (ψ : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ) ⊕ Fin (p τ)) (Fin (q τ) ⊕ Fin (p τ)) ℂ) (a' b' : T' → ℝ)
    (Y' : Set (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ)) (π : (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ι → ℂ)
    (AW : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (lam : ∀ τ, Fin (p τ + q τ) → ℝ),
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U (ψ τ)) ∧ (∀ τ, 0 < a' τ) ∧ (∀ τ, 0 < b' τ) ∧
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (AW τ)) ∧ (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (Aω τ)) ∧
    (∀ τ, Antitone (lam τ)) ∧ y ∈ Y' ∧ ContDiffAt ℝ 2 (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam) y ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam y ∧
    ∀ w, ReciprocityTheory.AnForm.levi (fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 *
        GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v))) y w =
      -ReciprocityTheory.AnForm.levi (fun v => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam v)) y w / 2 := by
  intro hP hH D O hC hN A T H h c a j y hy hZ u hu f hf
  obtain ⟨p, q, hpq, ι, _, U, ψ, a', b', Y', π, AW, Aω, g, hψ, ha, hb, hAW, hAω, hy', hg, hg0, heq⟩ :=
    GlobalTheory.T.exists_exponents_generating_divisor_at_point hP hH D O hC hN A T H h c a j y hy hZ f hf
  obtain ⟨hF2, hFpos⟩ := GlobalTheory.HodgeLocal.pairWeightNormSq_smooth _ ι D.what₂.Tau p q U ψ a' b' Y' π AW Aω (fun τ k => u τ (Fin.cast (hpq τ) k)) y
    hψ ha hb hAW hAω hy'
  refine ⟨D.what₂.Tau, inferInstance, p, q, ι, inferInstance, U, ψ, a', b', Y', π, AW, Aω,
    fun τ k => u τ (Fin.cast (hpq τ) k), hψ, ha, hb, hAW, hAω, fun τ k l hkl => hu τ _ _ hkl, hy', hF2, hFpos,
    fun w => ?_⟩
  rw [ReciprocityTheory.AnForm.levi_congr (heq u) w]
  have hS := GlobalTheory.HodgeLocal.levi_sum_eq_zero Finset.univ (fun x : DV.Rt D.what₂.Tau O.N => u x.1 x.2)
    (fun x v => Real.log ‖g x v‖) (y := y) fun x => GlobalTheory.HodgeLocal.log_norm_analytic (hg x) (hg0 x)
  have key : ∀ F : (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ℝ, ContDiffAt ℝ 2 F y → 0 < F y →
      ReciprocityTheory.AnForm.levi (fun v => -Real.log (F v) / 2 +
        ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * Real.log ‖g x v‖) y w =
      -ReciprocityTheory.AnForm.levi (fun v => Real.log (F v)) y w / 2 := by
    intro F h2 hpos
    have hL : ContDiffAt ℝ 2 (fun v => Real.log (F v)) y := h2.log hpos.ne'
    have e : (fun v => -Real.log (F v) / 2 + ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * Real.log ‖g x v‖) =
        fun v => (∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * Real.log ‖g x v‖) + (-1 / 2) * Real.log (F v) := by
      funext v; ring
    rw [e, ReciprocityTheory.AnForm.levi_add_smul _ hS.1 hL w, hS.2 w]
    ring
  exact key _ hF2 hFpos
