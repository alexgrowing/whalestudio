import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts

set_option autoImplicit false

noncomputable section

open Matrix Filter Topology Asymptotics
open scoped ComplexOrder

namespace GlobalTheory.CurvInterp.HodgeConj

section Pure

theorem differentiableOn_star_star {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E]
    [StarModule ℂ E] [ContinuousStar E] [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
    [ContinuousStar F] {f : E → F} {S T : Set E} (hf : DifferentiableOn ℂ f S) (hT : ∀ z ∈ T, star z ∈ S) :
    DifferentiableOn ℂ (fun z => star (f (star z))) T := by
  intro z hz
  obtain ⟨f', h⟩ := hf _ (hT z hz)
  let L := (starL ℂ (A := F)).toContinuousLinearMap
  let R := (starL ℂ (A := E)).toContinuousLinearMap
  refine ⟨L.comp (f'.comp R), ?_⟩
  rw [hasFDerivWithinAt_iff_isLittleO] at h ⊢
  have ht : Tendsto (fun w : E => star w) (𝓝[T] z) (𝓝[S] (star z)) :=
    continuous_star.continuousWithinAt.tendsto_nhdsWithin hT
  have h1 := (L.isBigO_comp _ _).trans_isLittleO (h.comp_tendsto ht)
  have h2 : (fun w : E => star w - star z) =O[𝓝[T] z] fun w => w - z := by
    simpa [R, star_sub] using R.isBigO_comp (fun w : E => w - z) (𝓝[T] z)
  refine (h1.trans_isBigO h2).congr_left fun w => ?_
  simp [L, R, star_sub]

theorem star_mem_ball {e : ℕ} {ρ : ℝ} {z : Fin e → ℂ} (hz : z ∈ Metric.ball (0 : Fin e → ℂ) ρ) :
    star z ∈ Metric.ball (0 : Fin e → ℂ) ρ := by
  simpa using hz

theorem star_mem_polydisc {n : ℕ} {ρ : ℝ} {z : Fin n → ℂ} (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n ρ) :
    star z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n ρ := fun k => by
  simpa using hz k

theorem inv_map_conj {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) :
    (M⁻¹).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ X : Matrix (Fin g) (Fin g) ℂ, X.map (starRingEnd ℂ) = Xᵀᴴ := fun X => by
    ext i j; simp
  rw [h, h, transpose_nonsing_inv, conjTranspose_nonsing_inv]

theorem block_map_conj {a b g : ℕ} (Q : Matrix (Fin a) (Fin g) ℂ) (Q' : Matrix (Fin b) (Fin g) ℂ)
    (Y : Matrix (Fin g) (Fin g) ℝ) :
    (Q * (Y.map Complex.ofReal)⁻¹ * Q'ᴴ).map (starRingEnd ℂ) =
      Q.map (starRingEnd ℂ) * (Y.map Complex.ofReal)⁻¹ * (Q'.map (starRingEnd ℂ))ᴴ := by
  have h : (Y.map Complex.ofReal).map (starRingEnd ℂ) = Y.map Complex.ofReal := by
    ext i j; simp
  rw [Matrix.map_mul, Matrix.map_mul, inv_map_conj, h]
  rfl

theorem isBlockModel_conj {e : ℕ} {ι : Type} [Fintype ι] {μ : ι → ℕ} {ρ : ℝ} {U U' : Set (Fin e → ℂ)}
    {H H' : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} (h : IsBlockModel ρ U' H')
    (hU : ∀ z ∈ U, star z ∈ U') (hH : ∀ τ z, H τ z = (H' τ (star z)).map (starRingEnd ℂ)) :
    IsBlockModel ρ U H := by
  obtain ⟨n, k, hk, g, rk, τ₀, B, φ, Q, κ, hP, hφ, hφ0, hφp, hQ, hc, hli, hκ, hz⟩ := h
  have him : ∀ M : Matrix (Fin g) (Fin g) ℂ, (-M.map (starRingEnd ℂ)).map Complex.im = M.map Complex.im := fun M => by
    ext i j; simp
  have hY : ∀ v, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod hk (fun v => -(τ₀ (star v)).map (starRingEnd ℂ)) B (star v) =
      GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod hk τ₀ B v := fun v => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, him, star_star, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Pi.star_apply, norm_star]
  refine ⟨n, k, hk, g, rk, fun v => -(τ₀ (star v)).map (starRingEnd ℂ), B, fun z => star (φ (star z)),
    fun τ z => (Q τ (star z)).map (starRingEnd ℂ), κ,
    ⟨hP.rk_le, fun j k => ?_, fun z hz => ?_, hP.psd, hP.supp, hP.toric, fun z hz => ?_⟩,
    differentiableOn_star_star hφ fun _ => star_mem_ball, by simp [hφ0],
    fun z hz => star_mem_polydisc (hφp _ (star_mem_ball hz)),
    fun τ i l => differentiableOn_star_star (hQ τ i l) fun _ => star_mem_ball, hc, ?_, hκ, fun z hzb hzU => ?_⟩
  · exact (differentiableOn_star_star (hP.holo j k) fun _ => star_mem_polydisc).neg
  · exact ((hP.symm _ (star_mem_polydisc hz)).map _).neg
  · rw [him]; exact hP.abelian _ (star_mem_polydisc hz)
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc0 p
    have h1 := hli (fun p => star (c p)) (by
      funext l
      have := congrArg star (congrFun hc0 l)
      simpa [Finset.sum_apply] using this) p
    simpa using h1
  · obtain ⟨h1, h2, h3⟩ := hz _ (star_mem_ball hzb) (hU z hzU)
    refine ⟨⟨star_mem_polydisc h1.1, fun i => by simpa using h1.2 i⟩, fun τ => ?_, fun τ τ' hne => ?_⟩
    · rw [hH, h2, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram, hY, ← block_map_conj]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    · have h4 := h3 τ τ' hne
      rw [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram] at h4 ⊢
      rw [hY, ← block_map_conj, h4]
      simp

end Pure

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp

theorem le_spMap_iff {R : Type} [CommRing R] {X : Scheme.{0}} (ψ : R →+* R) (hψ : spMap ψ ≫ spMap ψ = 𝟙 _)
    (x : Sp R ⟶ X) (U : X.Opens) : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  refine ⟨fun h => ?_, fun h => (GlobalTheory.ZH.CrdCalc.valR_spMap ψ x U h).1⟩
  have := (GlobalTheory.ZH.CrdCalc.valR_spMap ψ _ U h).1
  rwa [← Category.assoc, hψ, Category.id_comp] at this

theorem isHolTo_conj {e : ℕ} {X : Scheme.{0}} {B : Set (Fin e → ℂ)} {y : (Fin e → ℂ) → (Sp ℂ ⟶ X)} (h : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) fun w => spMap (starRingEnd ℂ) ≫ y (star w) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have e1 : {b | b ∈ star ⁻¹' B ∧ ⊤ ≤ (spMap (starRingEnd ℂ) ≫ y (star b)) ⁻¹ᵁ U} =
      star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, le_spMap_iff _ GlobalTheory.ShFam.HodgeConj.spMap_conj_conj']
  refine ⟨e1 ▸ h1.preimage continuous_star, ?_⟩
  rw [e1]
  exact (differentiableOn_star_star h2 fun _ hz => hz).congr fun b hb =>
    (GlobalTheory.ZH.CrdCalc.valR_spMap (starRingEnd ℂ) _ U hb.2).2 f

theorem holTan_conj {e : ℕ} {X : Scheme.{0}} {B : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Sp (DualNumber ℂ) ⟶ X)}
    (h : HolTan B v) : HolTan (star ⁻¹' B) fun w => spMap (dualMap (starRingEnd ℂ)) ≫ v (star w) := by
  intro U f
  have k : ∀ b : Fin e → ℂ, ⊤ ≤ (spMap (dualMap (starRingEnd ℂ)) ≫ v (star b)) ⁻¹ᵁ U → ⊤ ≤ v (star b) ⁻¹ᵁ U :=
    fun b => (le_spMap_iff _ GlobalTheory.ShFam.HodgeConj.spMap_dual_conj_conj' _ _).1
  refine (differentiableOn_star_star (h U f) fun z hz => ⟨hz.1, k z hz.2⟩).congr fun b hb => ?_
  rw [(GlobalTheory.ZH.CrdCalc.valR_spMap (dualMap (starRingEnd ℂ)) _ U (k b hb.2)).2 f]
  simp [dualMap]

theorem hodge_gram_conj {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {σ : κ.c.F →+* ℂ} {y : CxPts (genStr s.T.Z) σ} {y' : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ)}
    (hy' : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) {g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)}
    {g' : EigFrame s.T.Z ((starRingEnd ℂ).comp σ) (y'.1 ≫ genι s.T.Z)} (hg : g.IsMap (starRingEnd ℂ) g')
    (τ : D.host.E →+* ℂ) : (x.hodge _).gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  have hL : LiesIn y' (genBd s.T.Z) ↔ LiesIn y (genBd s.T.Z) := liesIn_iff_of_comp hy' _
  have hx : y'.1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z := by rw [hy', Category.assoc]
  by_cases hy : LiesIn y (genBd s.T.Z)
  · rw [x.hodge_gram_of_liesIn hy, x.hodge_gram_of_liesIn (hL.2 hy), x.gram_conj hy' g g' τ (hg τ)]
  · obtain ⟨f, hf⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hy
    obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) rfl hx
    have hH : IsHodgeFrame s.U y' f' := hf.conj (RingHom.ext fun a => (Complex.conj_conj (σ a)).symm)
      (by rw [hy', ← Category.assoc, GlobalTheory.ShFam.HodgeConj.spMap_conj_conj', Category.id_comp])
      (fun τ i => by rw [hf' τ i, ← Category.assoc, GlobalTheory.ShFam.HodgeConj.spMap_dual_conj_conj', Category.id_comp])
    rw [x.hodge_gram hH, x.hodge_gram hf, hf'.co τ hg hx]
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
      smul_eq_mul, RCLike.star_def, Complex.conj_conj, Complex.conj_ofReal]

theorem hodgeLocal_of_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), ¬ Formalism.L2.PjFree.GoodEmb κ.c σ → HodgeLocal x ((starRingEnd ℂ).comp σ) → HodgeLocal x σ := by
  intro D A N j S κ s x σ _ h e B a hB h0 ha hc
  let jm : CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ) := fun y =>
    ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩
  have hj : IsConjMap jm := fun _ => rfl
  have hjc : Continuous jm := (GlobalTheory.ConjChart.continuous_and_exists_conj_chart _ _ (genStr s.T.Z) S.Dw.dim _ _ jm rfl hj).1
  have hex : ∀ w : Fin e → ℂ, ∃ g' : EigFrame s.T.Z ((starRingEnd ℂ).comp σ) ((jm (a (star w)).1).1 ≫ genι s.T.Z),
      (a (star w)).2.IsMap (starRingEnd ℂ) g' := fun w =>
    (a (star w)).2.exists_isMap (starRingEnd ℂ) rfl (Category.assoc _ _ _)
  choose g' hg' using hex
  let a' : (Fin e → ℂ) → CxFr s.T.Z ((starRingEnd ℂ).comp σ) := fun w => ⟨jm (a (star w)).1, g' w⟩
  have h1 : IsHolTo (star ⁻¹' B) fun w => (a' w).1.1 := by
    have e1 : (fun w => (a' w).1.1) = fun w => spMap (starRingEnd ℂ) ≫ (a (star w)).1.1 := rfl
    rw [e1]
    exact isHolTo_conj (y := fun b => (a b).1.1) ha.1
  have h2 : ∀ τ i, HolTan (star ⁻¹' B) fun w => (a' w).2.v τ i := fun τ i => by
    have e1 : (fun w => (a' w).2.v τ i) = fun w => spMap (dualMap (starRingEnd ℂ)) ≫ (a (star w)).2.v τ i :=
      funext fun w => hg' w τ i
    rw [e1]
    exact holTan_conj (v := fun b => (a b).2.v τ i) (ha.2 τ i)
  have h3 : ContinuousOn (fun w => (a' w).1) (star ⁻¹' B) :=
    hjc.comp_continuousOn (hc.comp continuous_star.continuousOn fun _ hw => hw)
  have h4 : ∀ w, Inner (a (star w)).1 → Inner (a' w).1 := fun w hw hL =>
    hw ((liesIn_iff_of_comp (y := (a (star w)).1) (y' := jm (a (star w)).1) rfl _).1 hL)
  have h5 : ∀ τ w, (x.hodge ((starRingEnd ℂ).comp σ)).gram (a' w).1 (a' w).2 τ =
      ((x.hodge σ).gram (a (star w)).1 (a (star w)).2 τ).map (starRingEnd ℂ) := fun τ w =>
    hodge_gram_conj x (y := (a (star w)).1) (y' := jm (a (star w)).1) (g := (a (star w)).2) (g' := g' w)
      (hj _) (hg' w) τ
  obtain ⟨ρ, hρ, hsub, hm⟩ := h e (star ⁻¹' B) a' (hB.preimage continuous_star) (by simpa using h0) ⟨h1, h2⟩ h3
  clear_value a'
  refine ⟨ρ, hρ, fun z hz => by simpa using hsub (star_mem_ball hz), isBlockModel_conj hm (fun z hz => ?_) fun τ z => ?_⟩
  · exact h4 _ (by rw [star_star]; exact hz)
  · rw [h5, star_star]
    ext i l
    simp only [Matrix.map_apply, Matrix.transpose_apply, Complex.conj_conj]

end GlobalTheory.CurvInterp.HodgeConj
