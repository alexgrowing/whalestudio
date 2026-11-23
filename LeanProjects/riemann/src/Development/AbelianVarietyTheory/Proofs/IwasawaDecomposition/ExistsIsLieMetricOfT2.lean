import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightFamilyExistsOfWeightsT2

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open scoped ContDiff Manifold

namespace GlobalTheory.LieMetExist

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Z : Scheme.{0}}
  {t : SAB H X} {k : Type} [CommRing k] {p : Z ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

abbrev Forms (t : SAB H X) (f : Z ⟶ X) (p : Z ⟶ Sp k) (σ : k →+* ℂ) : Type :=
  ∀ y : CxPts p σ, TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ

open Classical in

def pairFn {f : Z ⟶ X} (h : Forms t f p σ) {W : Z.affineOpens} (v w : TanM (LogKS.chart W ≫ f) t.G)
    (y : CxPts p σ) : ℂ :=
  if hy : y ∈ ptsIn p σ W.1 then h y (LieMet.valAt f v hy) (LieMet.valAt f w hy) else 0

theorem pairFn_eq {f : Z ⟶ X} (h : Forms t f p σ) {W : Z.affineOpens} (v w : TanM (LogKS.chart W ≫ f) t.G)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W.1) :
    pairFn h v w y = h y (LieMet.valAt f v hy) (LieMet.valAt f w hy) := dif_pos hy

def SmC (R : AnRead p σ D) (S : Set (CxPts p σ)) (g : CxPts p σ → ℂ) : Prop :=
  letI := R.chartedSpace; ContMDiffOn 𝓘(ℝ, ReciprocityTheory.L2DbarEstimates.V D) 𝓘(ℝ, ℂ) ∞ g S

theorem smC_of_holoOn {R : AnRead p σ D} {S : Set (CxPts p σ)} (hS : IsOpen S) {g : CxPts p σ → ℂ}
    (h : R.HoloOn S g) : SmC R S g := by
  let := R.chartedSpace
  have := R.isManifold
  rw [SmC, contMDiffOn_iff]
  refine ⟨h.continuousOn hS, fun x w => ?_⟩
  simp only [mfld_simps, chartAt_self_eq]
  exact GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over _ hS) (h (R.cover x).choose)

theorem exists_local (R : AnRead p σ D) (t : SAB H X) (f : Z ⟶ X) (y₀ : CxPts p σ) :
    ∃ (V : Z.affineOpens) (g : Forms t f p σ), y₀ ∈ ptsIn p σ V.1 ∧
      (∀ y ∈ ptsIn p σ V.1, (∀ v w, g y w v = starRingEnd ℂ (g y v w)) ∧ ∀ v, v ≠ 0 → 0 < (g y v v).re) ∧
      ∀ (W : Z.affineOpens) (v w : TanM (LogKS.chart W ≫ f) t.G),
        SmC R (ptsIn p σ V.1 ∩ ptsIn p σ W.1) (pairFn g v w) := by
  classical
  obtain ⟨V, n, u, h₀, hb, hc⟩ := LieLocFrame.exists_local_basis E H X Z t f k p σ y₀
  let b : ∀ (y : CxPts p σ) (hy : y ∈ ptsIn p σ V.1), Module.Basis (Fin n) ℂ (TanM (y.1 ≫ f) t.G) :=
    fun y hy => Module.Basis.mk (hb y hy).1 (hb y hy).2.ge
  let g : Forms t f p σ := fun y => if hy : y ∈ ptsIn p σ V.1 then diagForm (b y hy) (fun _ => 1) else 0
  have hg : ∀ y (hy : y ∈ ptsIn p σ V.1), g y = diagForm (b y hy) (fun _ => 1) := fun y hy => dif_pos hy
  refine ⟨V, g, h₀, fun y hy => ?_, fun W v w y₁ hy₁ => ?_⟩
  · rw [hg y hy]
    exact ⟨diagForm_symm _ _, fun v hv => diagForm_pos _ (fun _ => one_pos) hv⟩
  · let := R.chartedSpace
    obtain ⟨O, a, hO, ha⟩ := hc W v y₁ hy₁
    obtain ⟨O', a', hO', ha'⟩ := hc W w y₁ hy₁
    have h1 : ∀ i, ContMDiffAt 𝓘(ℝ, ReciprocityTheory.L2DbarEstimates.V D) 𝓘(ℝ, ℂ) ∞ (ev p σ O (a i)) y₁ := fun i =>
      ContMDiffOn.contMDiffAt (smC_of_holoOn (isOpen_ptsIn _) (R.holoOn_ev O (a i))) ((isOpen_ptsIn _).mem_nhds hO)
    have h2 : ∀ i, ContMDiffAt 𝓘(ℝ, ReciprocityTheory.L2DbarEstimates.V D) 𝓘(ℝ, ℂ) ∞ (ev p σ O' (a' i)) y₁ := fun i =>
      ContMDiffOn.contMDiffAt (smC_of_holoOn (isOpen_ptsIn _) (R.holoOn_ev O' (a' i))) ((isOpen_ptsIn _).mem_nhds hO')
    have h3 : ContMDiffAt 𝓘(ℝ, ReciprocityTheory.L2DbarEstimates.V D) 𝓘(ℝ, ℂ) ∞
        (fun y => ∑ i, ev p σ O (a i) y * starRingEnd ℂ (ev p σ O' (a' i) y)) y₁ :=
      contMDiffAt_finsetSum fun i _ => (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).comp_contMDiffAt ((h1 i).prodMk_space
        (Complex.conjCLE.contDiff.contMDiff.contMDiffAt.comp y₁ (h2 i)))
    refine h3.contMDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ hy₁
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((isOpen_ptsIn _).mem_nhds hO),
      mem_nhdsWithin_of_mem_nhds ((isOpen_ptsIn _).mem_nhds hO')] with y hy hyO hyO'
    have e : ∀ c : Fin n → ℂ, ∀ i, (b y hy.1).repr (∑ j, c j • LieMet.valAt f (u j) hy.1) i = c i := fun c i => by
      have : ∀ j, LieMet.valAt f (u j) hy.1 = b y hy.1 j := fun j =>
        (Module.Basis.mk_apply (hb y hy.1).1 (hb y hy.1).2.ge j).symm
      simp only [this]
      exact congrFun ((b y hy.1).repr_sum_self c) i
    rw [pairFn_eq _ _ _ hy.2, hg y hy.1, ha y hyO hy.1 hy.2, ha' y hyO' hy.1 hy.2, diagForm_apply]
    simp only [e, Complex.ofReal_one, _root_.one_mul]

theorem exists_smooth [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (R : AnRead p σ D) (t : SAB H X)
    (f : Z ⟶ X) : ∃ g : Forms t f p σ,
      (∀ y, (∀ v w, g y w v = starRingEnd ℂ (g y v w)) ∧ ∀ v, v ≠ 0 → 0 < (g y v v).re) ∧
      ∀ (W : Z.affineOpens) (v w : TanM (LogKS.chart W ≫ f) t.G), SmC R (ptsIn p σ W.1) (pairFn g v w) := by
  let := R.chartedSpace
  have := R.isManifold
  have : LocallyCompactSpace (CxPts p σ) := ChartedSpace.locallyCompactSpace (ReciprocityTheory.L2DbarEstimates.V D) _
  choose V g h₀ hg hs using exists_local R t f
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ReciprocityTheory.L2DbarEstimates.V D) isClosed_univ
    (fun i => ptsIn p σ (V i).1) (fun _ => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨_, h₀ y⟩
  let G : Forms t f p σ := fun y => ∑ i ∈ χ.finsupport y, (χ i y : ℂ) • g i y
  have hG : ∀ y v w, G y v w = ∑ i ∈ χ.finsupport y, χ i y • g i y v w := fun y v w => by
    simp [G, LinearMap.sum_apply]
  have hm : ∀ y, ∀ i ∈ χ.finsupport y, y ∈ ptsIn p σ (V i).1 := fun y i hi =>
    hχ i (subset_tsupport _ ((χ.mem_finsupport y).1 hi))
  refine ⟨G, fun y => ⟨fun v w => ?_, fun v hv => ?_⟩, fun W v w y hy => ?_⟩
  · rw [hG, hG, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hg i y (hm y i hi)).1 v w]
    simp
  · rw [hG, Complex.re_sum]
    refine Finset.sum_pos (fun i hi => ?_) ?_
    · rw [Complex.smul_re, smul_eq_mul]
      exact mul_pos (lt_of_le_of_ne (χ.nonneg i y) (Ne.symm ((χ.mem_finsupport y).1 hi)))
        ((hg i y (hm y i hi)).2 v hv)
    · refine Finset.nonempty_of_sum_ne_zero (f := fun i => χ i y) ?_
      rw [χ.sum_finsupport y (Set.mem_univ y)]
      exact one_ne_zero
  · refine (χ.contMDiffAt_finsum (n := (⊤ : ℕ∞)) (g := fun i => pairFn (g i) v w)
      fun i hi => ?_).contMDiffWithinAt.congr_of_mem (fun z hz => ?_) hy
    · exact ContMDiffOn.contMDiffAt (hs i W v w) (((isOpen_ptsIn _).inter (isOpen_ptsIn _)).mem_nhds ⟨hχ i hi, hy⟩)
    · rw [← χ.sum_finsupport_smul_eq_finsum z fun i => pairFn (g i) v w, pairFn_eq _ _ _ hz, hG]
      simp only [pairFn_eq _ _ _ hz]

theorem valAt_act (f : Z ⟶ X) {W : Z.affineOpens} (a : 𝓞 E) (v : TanM (LogKS.chart W ≫ f) t.G) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ W.1) : LieMet.valAt f (actR t.act a v) hy = actR t.act a (LieMet.valAt f v hy) :=
  tan_ext (Category.assoc _ _ _).symm

theorem exists_isLieMetric_of_t2 [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (R : AnRead p σ D)
    (t : SAB H X) (f : Z ⟶ X) : ∃ h, IsLieMetric t f R h := by
  classical
  let := R.chartedSpace
  obtain ⟨g, hg, hs⟩ := exists_smooth R t f
  let χ : (E →+* ℂ) → (𝓞 E →+* ℂ) := fun τ => τ.comp (algebraMap (𝓞 E) E)
  obtain ⟨α, hα, -⟩ := exists_sepElt (RingHom.id ℂ) χ fun _ _ => rfl
  let e := fun y : CxPts p σ => proj (actR (x0 := y.1 ≫ f) t.act) χ α
  have he : ∀ y ρ v, IsEig ρ v → ∀ τ, τ ≠ ρ → e y τ v = 0 := fun y ρ v hv τ hτ => by
    have := proj_sum_eig (actR (x0 := y.1 ≫ f) t.act) χ α hα (Pi.single ρ v) (fun τ' a => by
      by_cases h : τ' = ρ
      · subst h; rw [Pi.single_eq_same]; exact hv a
      · simp [Pi.single_eq_of_ne h]) τ
    rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_of_ne hτ] at this
  let G : Forms t f p σ := fun y => ∑ τ, ((g y).compl₂ (e y τ)).comp (e y τ)
  have hf : ∀ y v w, G y v w = ∑ τ, g y (e y τ v) (e y τ w) := fun y v w => by
    simp [G, LinearMap.sum_apply]
  obtain ⟨N, c, hc⟩ : ∃ (N : (E →+* ℂ) → ℕ) (c : (E →+* ℂ) → ℕ → ℂ), ∀ y τ v,
      e y τ v = ∑ j ∈ Finset.range (N τ), c τ j • actR t.act (α ^ j) v :=
    ⟨_, _, fun y τ v => by
      simp only [e, proj]
      rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, map_pow]
      rfl⟩
  refine ⟨G, fun y => ⟨fun v w => ?_, fun v hv => ?_, fun ρ ρ' v w h hv hw => ?_⟩, fun W v w => ?_⟩
  · rw [hf, hf, map_sum]
    exact Finset.sum_congr rfl fun τ _ => (hg y).1 _ _
  · obtain ⟨τ, hτ⟩ : ∃ τ, e y τ v ≠ 0 := by
      by_contra! h
      have := LinearMap.congr_fun (sum_proj (actR (x0 := y.1 ≫ f) t.act) χ α hα) v
      rw [LinearMap.sum_apply, Finset.sum_eq_zero fun τ _ => h τ] at this
      exact hv this.symm
    rw [hf, Complex.re_sum]
    refine Finset.sum_pos' (fun τ' _ => ?_) ⟨τ, Finset.mem_univ _, (hg y).2 _ hτ⟩
    by_cases h : e y τ' v = 0
    · simp [h]
    · exact ((hg y).2 _ h).le
  · rw [hf]
    refine Finset.sum_eq_zero fun τ _ => ?_
    by_cases h1 : τ = ρ
    · rw [he y ρ' w hw τ (h1 ▸ h), map_zero]
    · rw [he y ρ v hv τ h1, map_zero, LinearMap.zero_apply]
  · have key : SmC R (ptsIn p σ W.1) (pairFn G v w) := by
      refine ContMDiffOn.congr (f := fun y => ∑ τ, ∑ l ∈ Finset.range (N τ), ∑ j ∈ Finset.range (N τ),
        (starRingEnd ℂ (c τ l) * c τ j) * pairFn g (actR t.act (α ^ j) v) (actR t.act (α ^ l) w) y)
        (contMDiffOn_finsetSum fun τ _ => contMDiffOn_finsetSum fun l _ => contMDiffOn_finsetSum fun j _ =>
          (contDiff_const.mul contDiff_id).contMDiff.comp_contMDiffOn (hs W _ _)) fun y hy => ?_
      simp only [pairFn_eq _ _ _ hy, hf, hc, valAt_act, map_sum, map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum, _root_.mul_assoc]
    exact ⟨pairFn G v w,
      (AnRead.smoothOn_iff_contMDiffOn (isOpen_ptsIn _)).2 (Complex.reCLM.contDiff.contMDiff.comp_contMDiffOn key),
      (AnRead.smoothOn_iff_contMDiffOn (isOpen_ptsIn _)).2 (Complex.imCLM.contDiff.contMDiff.comp_contMDiffOn key),
      fun y hy => pairFn_eq _ _ _ hy⟩

theorem exists_isLieMetric : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ : k →+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (f : Y ⟶ X), IsProjOver p → ∃ h, IsLieMetric t f (AnRead.all p σ d) h := by
  intro k _ Y p d _ σ E _ _ _ H X t f hp
  have := t2Space_cxPts_of_isProjOver σ hp
  have := secondCountableTopology_of_isProjOver σ hp
  exact exists_isLieMetric_of_t2 _ t f

end GlobalTheory.LieMetExist
