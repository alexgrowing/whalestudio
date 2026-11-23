import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameChartOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

section Free

open Matrix Filter NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder Topology

namespace GlobalTheory.HodgeFlagModelConj

private theorem analyticAt_conj_comp {d : ℕ} {h : (Fin d → ℂ) → ℂ} {v : Fin d → ℂ} (hh : AnalyticAt ℂ h (star v)) :
    AnalyticAt ℂ (fun w => starRingEnd ℂ (h (star w))) v := by
  have h1 : ∀ᶠ w in 𝓝 v, DifferentiableAt ℂ (fun w => starRingEnd ℂ (h (star w))) w := by
    filter_upwards [(continuous_star.tendsto v).eventually hh.eventually_analyticAt] with w hw
    have h2 := hw.differentiableAt.star_star
    rw [star_star] at h2
    exact h2
  obtain ⟨S, hS, hSo, hv⟩ := eventually_nhds_iff.1 h1
  exact (SCV.analyticOnNhd_iff_differentiableOn hSo).2 (fun w hw => (hS w hw).differentiableWithinAt) v hv

private theorem inv_map_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    (M.map (starRingEnd ℂ))⁻¹ = M⁻¹.map (starRingEnd ℂ) := by
  rw [GlobalTheory.ShFam.ConjMet.map_conj_eq, GlobalTheory.ShFam.ConjMet.map_conj_eq, ← transpose_nonsing_inv,
    ← conjTranspose_nonsing_inv]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

private theorem inDom_conj {z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ} (hz : GlobalTheory.PointChern.InDom z) :
    GlobalTheory.PointChern.InDom fun τ => (z τ).map (starRingEnd ℂ) := by
  intro τ
  have h := (hz τ).transpose
  have e : (1 - (z τ)ᴴ * z τ)ᵀ = 1 - ((z τ).map (starRingEnd ℂ))ᴴ * (z τ).map (starRingEnd ℂ) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm]
  exact e ▸ h

private theorem modelGram_conj (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (τ : E →+* ℂ) :
    GlobalTheory.PointChern.modelGram H Dw (fun τ => (z τ).map (starRingEnd ℂ)) τ =
      (GlobalTheory.PointChern.modelGram H Dw z τ).map (starRingEnd ℂ) := by
  unfold GlobalTheory.PointChern.modelGram
  split_ifs with h h'
  · have e : 1 - ((z ⟨τ, h⟩).map (starRingEnd ℂ)).map (starRingEnd ℂ) * ((z ⟨τ, h⟩).map (starRingEnd ℂ))ᵀ =
        (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ).map (starRingEnd ℂ) := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, apply_ite]
    rw [e, inv_map_conj]
    rfl
  · have e : 1 - ((z ⟨_, h'⟩).map (starRingEnd ℂ))ᴴ * (z ⟨_, h'⟩).map (starRingEnd ℂ) =
        (1 - (z ⟨_, h'⟩)ᴴ * z ⟨_, h'⟩).map (starRingEnd ℂ) := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, apply_ite]
    rw [e, inv_map_conj]
    rfl
  · simp

private theorem conj_rel {m : ℕ} {M G N : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    (h : (M.map (starRingEnd ℂ))ᵀ = (c : ℂ) • (G * N * Gᴴ)) :
    Mᵀ = (c : ℂ) • (G.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) * (G.map (starRingEnd ℂ))ᴴ) := by
  ext a b
  have := congrArg (starRingEnd ℂ) (congrFun (congrFun h a) b)
  simpa [Matrix.mul_apply, map_sum] using this

open AlgebraicGeometry CategoryTheory Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam in

private theorem isMap_trans {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : Model Xo c β} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ψ : R →+* R'} {ψ' : R' →+* R''} {χ : R →+* R''}
    (h : f.IsMap ψ f') (h' : f'.IsMap ψ' f'') (e : χ = ψ'.comp ψ) : f.IsMap χ f'' := fun τ i => by
  rw [h' τ i, h τ i, e, GlobalTheory.GradedPieces.dual_comp]

open AlgebraicGeometry CategoryTheory GlobalTheory.CxPts in

private theorem evHom_conj {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {y : CxPts p σ}
    {y' : CxPts p σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) {U : Y.Opens} (h : y ∈ ptsIn p σ U)
    (h' : y' ∈ ptsIn p σ' U) : evHom h' = (starRingEnd ℂ).comp (evHom h) := RingHom.ext fun t => by
  rw [RingHom.comp_apply, ← ev_eq h, ← ev_eq h']
  exact CxPts.ev_conj e h t

end GlobalTheory.HodgeFlagModelConj

end Free

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

theorem _root_.GlobalTheory.T.eigen_frame_chart_off_boundary_second : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ), ¬ Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ) → ∀ (d : ℕ) (c' : AlgChart (Φ.C k).Y.str σ d) (p0 : (Φ.C k).Y.pts σ), p0 ∈ c'.finChart.source → (Φ.C k).π (under p0) ∉ genBd s.T.Z →
    ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (Fr : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)),
    LogKS.chart V ≫ genStr s.T.Z = spMap φ → (Φ.C k).down p0 ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1 →
    ∃ (G : (Fin d → ℂ) → GlobalTheory.FlagBundle.Mat S.Dw.mult ℂ) (z : (Fin d → ℂ) → GlobalTheory.AllWt.Psi A.H → Matrix (Fin S.Dw.p) (Fin S.Dw.q) ℂ)
      (cc : (D.host.E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => G w τ a b) v) ∧
        (∀ τ a b, AnalyticAt ℂ (fun w => z w τ a b) v) ∧ (∀ τ, IsUnit (G v τ).det) ∧ GlobalTheory.PointChern.InDom (z v) ∧
        ∃ hv : (Φ.C k).down (c'.finChart.symm v) ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1,
          ∀ f : (Φ.C k).FrameAt (c'.finChart.symm v), Fr.IsMap (evHom hv) f → ∀ τ,
            ((x.hodge (embOf κ.e σ)).gram ((Φ.C k).down (c'.finChart.symm v)) f τ)ᵀ =
              (cc τ : ℂ) • (G v τ * GlobalTheory.PointChern.modelGram A.H S.Dw (z v) τ * (G v τ)ᴴ) := by
  intro D A N j S κ s x Φ k σ hσ d c' p0 hp0 hb W φ Fr hW h0
  let σ' : D.what₂.LL →+* ℂ := (starRingEnd ℂ).comp σ
  let J := GlobalTheory.ConjChart.conjPts (Φ.C k).Y.str (σ := σ') (σ' := σ) rfl
  let c'' : AlgChart (Φ.C k).Y.str σ' d := GlobalTheory.ConjChart.conjChart rfl c'
  have hJ : ∀ y, (J y).1 = spMap (starRingEnd ℂ) ≫ y.1 := fun _ => rfl
  have hemb : embOf κ.e σ' = (starRingEnd ℂ).comp (embOf κ.e σ) := rfl
  have hσ' : Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ') := by
    have := Formalism.L2.PjFree.goodEmb_goodOf κ.c (embOf κ.e σ)
    unfold Formalism.L2.PjFree.goodOf at this
    rwa [if_neg hσ] at this
  have hp0' : J p0 ∈ c''.finChart.source := by
    change J.symm (J p0) ∈ c'.e.source
    rw [Homeomorph.symm_apply_apply]
    exact hp0
  have hb' : (Φ.C k).π (under (J p0)) ∉ genBd s.T.Z := by
    have e : under (J p0) = under p0 := GlobalTheory.ShFam.ConjMet.base_conj (Y := Φ.C k) (hJ p0)
    rw [e]
    exact hb
  have h0' : (Φ.C k).down (J p0) ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ') W.1 :=
    GlobalTheory.ConjChart.mem_ptsIn_of_conj (GlobalTheory.ShFam.ConjMet.down_conj (Y := Φ.C k) (hJ p0)) h0
  obtain ⟨G, z, cc, hcc, h⟩ := GlobalTheory.T.eigen_frame_chart_off_boundary D A N j S κ s x Φ k σ' hσ' d c'' (J p0) hp0' hb' W φ Fr hW h0'
  have hc0 : c''.finChart (J p0) = star (c'.finChart p0) := by
    funext a
    change starRingEnd ℂ (c'.e (J.symm (J p0)) a) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  rw [hc0] at h
  refine ⟨fun v τ => (G (star v) τ).map (starRingEnd ℂ), fun v τ => (z (star v) τ).map (starRingEnd ℂ), cc, hcc, ?_⟩
  filter_upwards [(continuous_star.tendsto _).eventually h] with v ⟨h1, h2, h3, h4, hv', h5⟩
  have e' : (c''.finChart.symm (star v)).1 = spMap (starRingEnd ℂ) ≫ (c'.finChart.symm v).1 := by
    change (J (c'.finChart.symm (star (star v)))).1 = _
    rw [star_star, hJ]
  have ed := GlobalTheory.ShFam.ConjMet.down_conj (Y := Φ.C k) e'
  have hv : (Φ.C k).down (c'.finChart.symm v) ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) W.1 :=
    GlobalTheory.ConjChart.mem_ptsIn_of_conj (by
      rw [ed, ← Category.assoc, GlobalTheory.ShFam.ConjMet.spMap_conj_conj, Category.id_comp]) hv'
  refine ⟨fun τ a b => GlobalTheory.HodgeFlagModelConj.analyticAt_conj_comp (h1 τ a b),
    fun τ a b => GlobalTheory.HodgeFlagModelConj.analyticAt_conj_comp (h2 τ a b), fun τ => ?_,
    GlobalTheory.HodgeFlagModelConj.inDom_conj h4, hv, fun f hf τ => ?_⟩
  · have := (h3 τ).map (starRingEnd ℂ)
    rwa [RingHom.map_det] at this
  · obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) hemb (GlobalTheory.ShFam.ConjMet.gen_eq ed)
    have hev := GlobalTheory.HodgeFlagModelConj.evHom_conj ed hv hv'
    have h6 := h5 f' (GlobalTheory.HodgeFlagModelConj.isMap_trans hf hf' hev) τ
    rw [GlobalTheory.ShFam.ConjMet.hodge_conj x hemb ed hf' τ] at h6
    rw [GlobalTheory.HodgeFlagModelConj.modelGram_conj]
    exact GlobalTheory.HodgeFlagModelConj.conj_rel h6
