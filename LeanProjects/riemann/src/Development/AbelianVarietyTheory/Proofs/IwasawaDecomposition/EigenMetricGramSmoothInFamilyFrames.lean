import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChartStatement

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LieBase.GramSmooth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts p σ}

theorem cInfAt_mul {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sub {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z - g z) y :=
  hf.comp₂ hg (G := fun x => x.1 - x.2) (contDiff_fst.sub contDiff_snd)

def CxInf (f : GlobalTheory.CxPts p σ → ℂ) (y : GlobalTheory.CxPts p σ) : Prop :=
  CInfAt (fun z => (f z).re) y ∧ CInfAt (fun z => (f z).im) y

variable {f g : GlobalTheory.CxPts p σ → ℂ}

theorem CxInf.mul (hf : CxInf f y) (hg : CxInf g y) : CxInf (fun z => f z * g z) y := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re]; exact cInfAt_sub (cInfAt_mul hf.1 hg.1) (cInfAt_mul hf.2 hg.2)
  · simp only [Complex.mul_im]; exact (cInfAt_mul hf.1 hg.2).add (cInfAt_mul hf.2 hg.1)

theorem CxInf.star (hf : CxInf f y) : CxInf (fun z => star (f z)) y := by
  refine ⟨?_, ?_⟩
  · simpa [Complex.star_def] using hf.1
  · simpa [Complex.star_def] using hf.2.neg

theorem CxInf.sum {κ : Type} (s : Finset κ) {f : κ → GlobalTheory.CxPts p σ → ℂ} (h : ∀ a ∈ s, CxInf (f a) y) :
    CxInf (fun z => ∑ a ∈ s, f a z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_⟩ <;> simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_insert ha, Complex.add_re]; exact h1.1.add h2.1
    · simp only [Finset.sum_insert ha, Complex.add_im]; exact h1.2.add h2.2

theorem cxInf_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : GlobalTheory.CxPts X.str σ} {f : X.Fn}
    (hf : RegAt (under y) f) : CxInf (fun z => ratVal f z) y :=
  ⟨GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
               (G := fun v => (v ()).re) (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ ())),
    GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
      (G := fun v => (v ()).im) (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ ()))⟩

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem cInfAt_comp {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'}
    {σ : k →+* ℂ} {σ' : k' →+* ℂ} {π : Y' ⟶ Y} {m : GlobalTheory.CxPts p' σ' → GlobalTheory.CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ π)
    {f : GlobalTheory.CxPts p σ → ℝ} {z : GlobalTheory.CxPts p' σ'} (h : CInfAt f (m z)) : CInfAt (fun w => f (m w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, (mem_ptsIn_preimage hm).2 h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_of_comp hm] using h₃
  · simp only [← ev_of_comp hm]
    exact (continuous_of_comp hm).continuousAt.eventually h₅

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem eventually_mem : ∀ (F : Type) [Field F] (X : Var F) (σ : F →+* ℂ) (ι : Type) [Finite ι] (m : ι → ℕ) (S : Fr (ratOf X) m 0) (y : GlobalTheory.CxPts X.str σ) (A : Mat m X.Fn), A ∈ S.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  intro F _ X σ ι _ m S y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem gram_entry_cInfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ (τ : E →+* ℂ) (p q : Fin (Dw.mult τ)) (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) → cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 → ∃ h : GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → ℂ, CInfAt (fun z => (h z).re) y ∧ CInfAt (fun z => (h z).im) y ∧ ∀ᶠ z in 𝓝 y, ∀ (hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z)), Φ.IsMap (evHom hz) f → G.gram (cxOf e σ hj z) f τ p q = h z := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j hj V φ Φ hφ τ p q y hy hyV
  obtain ⟨g, hre, him, hg⟩ := hG V φ Φ τ p q hφ
  have hT : IsOpen ({y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1) := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hm : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), (cxOf e σ hj z).1 = z.1 ≫ j := fun _ => rfl
  have hyT : cxOf e σ hj y ∈ {y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1 :=
    ⟨mem_ptsIn.1 ((mem_ptsIn_preimage hm).1 hy), hyV⟩
  have cre := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 hre _ hyT
  have cim := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 him _ hyT
  refine ⟨fun z => g (cxOf e σ hj z), GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cre,
    GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cim, ?_⟩
  filter_upwards [(continuous_of_comp hm).continuousAt.preimage_mem_nhds (hT.mem_nhds hyT)] with z hz hz' f hf
  exact hg _ hz.1 hz' f hf

end GlobalTheory.LieBase.GramSmooth

theorem GlobalTheory.LieBase.cInfAt_gramOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j f₀ S A₀ hj hoi hT y hy A hA τ a b
  obtain ⟨U, hU, φ, Φ, hzU, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 := mem_ptsIn.2 hzU
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β Z σ F e X j f₀ S A₀ hj hoi hT V φ Φ hφ' A
  choose h hre him hev using fun p q => GlobalTheory.LieBase.GramSmooth.gram_entry_cInfAt E H Dw l Xo c O β Z σ G hG F e X j hj V φ Φ hφ' τ p q y hy hyV
  have hS := GlobalTheory.LieBase.GramSmooth.eventually_mem F X (σ.comp e.toRingHom) (E →+* ℂ) Dw.mult S y A hA
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have hall := Filter.eventually_all.2 fun pq : Fin (Dw.mult τ) × Fin (Dw.mult τ) => hev pq.1 pq.2
  have hreg := (hM y hA hyV).1 τ
  have key : ∀ᶠ z in 𝓝 y, gramOf e G hj f₀ A₀ A z τ a b =
      ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z := by
    filter_upwards [hS, hVn, hall] with z hzS hzV hzall
    obtain ⟨-, hex, hco⟩ := hM z hzS hzV
    have hov : σ = (evHom hzV).comp φ := GlobalTheory.ShFam.EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [gramOf, dif_pos hex]
    show (G.gram (cxOf e σ hj z) hex.choose τ)ᵀ a b = _
    rw [Matrix.transpose_apply, G.change (cxOf e σ hj z) f, hco _ hex.choose_spec f hf τ]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hzall (p, q) hzV f hf]
  open GlobalTheory.LieBase.GramSmooth in
  have hC : CxInf (fun z => ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z) y :=
    CxInf.sum _ fun q _ => (CxInf.sum _ fun p _ => (cxInf_ratVal (hreg p b)).star.mul ⟨hre p q, him p q⟩).mul
      (cxInf_ratVal (hreg q a))
  exact ⟨hC.1.congr (key.mono fun z hz => congrArg Complex.re hz), hC.2.congr (key.mono fun z hz => congrArg Complex.im hz)⟩

end
