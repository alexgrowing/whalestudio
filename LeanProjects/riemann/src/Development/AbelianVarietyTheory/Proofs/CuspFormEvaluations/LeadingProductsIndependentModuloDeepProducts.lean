import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadMCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumMultiLtSucc
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

open ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.L2DbarEstimates Topology Filter Asymptotics

namespace GlobalTheory.Shares.LeadDeep

private theorem isBigO_norm_pow_of_mem_span_monomial_mul {Y : Type} {D : ℕ} (a : ℕ) (x : Y) (s : Fin D → Y → ℂ) (H : Set (Y → ℂ))
    (φ : V D → Y) (U : Set (V D)) (hU : IsOpen U) (h0U : (0 : V D) ∈ U) (hφ0 : φ 0 = x)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s k (φ z)) U)
    (hH : ∀ f ∈ H, DifferentiableOn ℂ (fun z => f (φ z)) U) (hs0 : ∀ k, s k x = 0) (g : Y → ℂ)
    (hg : g ∈ Submodule.span ℂ
      {g | ∃ (α : Fin D → ℕ) (f : Y → ℂ), ∑ i, α i = a ∧ f ∈ H ∧ g = (∏ i, s i ^ α i) * f}) :
    (fun z => g (φ z)) =O[𝓝 0] fun z : V D => ‖z‖ ^ a := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, f, hα, hf, rfl⟩ := hg
    have h1 := GlobalTheory.JetsPure.monomial_isBigO (fun k z => s k (φ z))
      (fun k => (hs k).differentiableAt (hU.mem_nhds h0U)) (fun k => by simp only [hφ0, hs0]) α
    have h2 : (fun z => f (φ z)) =O[𝓝 (0 : V D)] (fun _ => (1 : ℝ)) :=
      Filter.Tendsto.isBigO_one ℝ (((hH f hf).differentiableAt (hU.mem_nhds h0U)).continuousAt)
    have h3 := h1.mul h2
    rw [hα] at h3
    simpa [Finset.prod_apply] using h3
  | zero => simpa using Asymptotics.isBigO_zero (fun z : V D => ‖z‖ ^ a) (𝓝 (0 : V D))
  | add x y _ _ hx hy => simpa using hx.add hy
  | smul r x _ hx => simpa using hx.const_mul_left r

private theorem coeff_lemma_3 {D : ℕ} (M : Finset (Fin D → ℕ)) (A : (Fin D → ℕ) → ℂ)
    (h : ∀ y : Fin D → ℂ, ∑ α ∈ M, A α * ∏ q, y q ^ α q = 0) : ∀ α ∈ M, A α = 0 := by
  classical
  let p : MvPolynomial (Fin D) ℂ :=
    ∑ α ∈ M, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (A α)
  have hp : p = 0 := by
    apply MvPolynomial.funext
    intro y
    simp only [p, map_sum, MvPolynomial.eval_monomial, map_zero]
    rw [← h y]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  intro α hα
  have h1 := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α)) hp
  simp only [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at h1
  rw [Finset.sum_eq_single α] at h1
  · simpa using h1
  · intro β _ hβα
    rw [if_neg]
    intro h'
    exact hβα (Finsupp.equivFunOnFinite.symm.injective h')
  · intro h'
    exact absurd hα h'

private theorem gs_id_linComb_eq_trF_mul_sval {Y : Type} {D m : ℕ} (T a d : ℕ) (x : Y) (s : Fin D → Y → ℂ) (w0 : Y → ℂ)
    (θ : Fin m → Y → ℂ) (H : Set (Y → ℂ)) (φ : V D → Y) (U : Set (V D)) (hU : IsOpen U)
    (h0U : (0 : V D) ∈ U) (hφ0 : φ 0 = x)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s k (φ z)) U)
    (hw : DifferentiableOn ℂ (fun z => w0 (φ z)) U)
    (hθ : ∀ i, DifferentiableOn ℂ (fun z => θ i (φ z)) U)
    (hH : ∀ f ∈ H, DifferentiableOn ℂ (fun z => f (φ z)) U) (hs0 : ∀ k, s k x = 0) (hw0 : w0 x ≠ 0)
    (hdet : (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s k (φ z) / w0 (φ z) : V D)) 0).det ≠ 0)
    (c : (Fin D → ℕ) → Fin m → ℂ) (hlow : ∀ α ∈ multiLt D a, ∀ k, c α k ≠ 0 → d ≤ ∑ q, α q)
    (hda : d < a)
    (hmem : (fun y => ∑ α ∈ multiLt D a, ∑ k, c α k * (∏ q, s q y ^ α q) * w0 y ^ (T - ∑ q, α q) * θ k y) ∈
      Submodule.span ℂ {g | ∃ (α : Fin D → ℕ) (f : Y → ℂ), ∑ i, α i = a ∧ f ∈ H ∧ g = (∏ i, s i ^ α i) * f}) :
    ∀ α ∈ multiLt D a, ∑ q, α q = d → ∑ k, c α k * θ k x = 0 := by
  obtain ⟨C, hC⟩ := (isBigO_norm_pow_of_mem_span_monomial_mul a x s H φ U hU h0U hφ0 hs hH hs0 _ hmem).bound
  have hb : ∃ C : ℝ, ∀ᶠ v in 𝓝 (0 : V D), ‖∑ α ∈ multiLt D a, ∑ k,
      c α k * (∏ q, s q (φ v) ^ α q) * w0 (φ v) ^ (T - ∑ q, α q) * θ k (φ v)‖ ≤ C * ‖v - 0‖ ^ a :=
    ⟨C, by filter_upwards [hC] with v hv; simpa only [sub_zero, norm_pow, norm_norm] using hv⟩
  have hL := GlobalTheory.LeadIndep.lowest_degree U hU 0 h0U (fun k z => s k (φ z)) (fun z => w0 (φ z))
    (fun k z => θ k (φ z)) (multiLt D a) T a d c hs hw hθ (fun k => by simp only [hφ0, hs0])
    (by simpa only [hφ0] using hw0) hlow hda hb
  simp only [hφ0] at hL
  have hsurj : Function.Surjective
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s k (φ z) / w0 (φ z) : V D)) 0) := by
    have hu : IsUnit ((fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s k (φ z) / w0 (φ z) : V D)) 0 :
        V D →L[ℂ] V D) : V D →ₗ[ℂ] V D) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    exact ((Module.End.isUnit_iff _).mp hu).2
  have hpoly : ∀ y : Fin D → ℂ, ∑ α ∈ multiLt D a,
      ((∑ k, c α k * θ k x) * 0 ^ (∑ q, α q - d) * w0 x ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, y q ^ α q = 0 := by
    intro y
    obtain ⟨h0, hh0⟩ := hsurj (WithLp.toLp 2 y)
    have h1 := hL h0
    rw [hh0] at h1
    simpa only [PiLp.toLp_apply] using h1
  have hA := coeff_lemma_3 _ _ hpoly
  intro α hα hαd
  have h2 := hA α hα
  rw [hαd, Nat.sub_self, pow_zero, mul_one] at h2
  exact (mul_eq_zero.mp h2).resolve_right (pow_ne_zero _ hw0)

theorem coeff_eq_zero {Y : Type} {δ D m : ℕ} (T a : ℕ) (xs : Fin δ → Y) (s : Fin D → Y → ℂ) (w0 : Y → ℂ)
    (θ : Fin m → Y → ℂ) (H : Set (Y → ℂ))
    (hch : ∀ q, ∃ (n : ℕ) (hn : n = D) (φ : V n → Y) (U : Set (V n)), IsOpen U ∧ 0 ∈ U ∧ φ 0 = xs q ∧
      (∀ k, DifferentiableOn ℂ (fun z => s k (φ z)) U) ∧ DifferentiableOn ℂ (fun z => w0 (φ z)) U ∧
      (∀ i, DifferentiableOn ℂ (fun z => θ i (φ z)) U) ∧ (∀ f ∈ H, DifferentiableOn ℂ (fun z => f (φ z)) U) ∧
      (∀ k, s k (xs q) = 0) ∧ w0 (xs q) ≠ 0 ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s (Fin.cast hn k) (φ z) / w0 (φ z) : V n)) 0).det ≠ 0)
    (hθ : LinearIndependent ℂ (vals xs θ)) (c : (Fin D → ℕ) → Fin m → ℂ)
    (hmem : (fun y => ∑ α ∈ multiLt D a, ∑ k, c α k * (∏ q, s q y ^ α q) * w0 y ^ (T - ∑ q, α q) * θ k y) ∈
      Submodule.span ℂ {g | ∃ (α : Fin D → ℕ) (f : Y → ℂ), ∑ i, α i = a ∧ f ∈ H ∧ g = (∏ i, s i ^ α i) * f}) :
    ∀ α ∈ multiLt D a, ∀ k, c α k = 0 := by
  classical
  have key : ∀ d, ∀ α ∈ multiLt D a, ∑ q, α q = d → ∀ k, c α k = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro α hα hαd
      have hda : d < a := by rw [← hαd]; exact GlobalTheory.LeadIndep.mem_multiLt.mp hα
      have hlow : ∀ β ∈ multiLt D a, ∀ k, c β k ≠ 0 → d ≤ ∑ q, β q := by
        intro β hβ k hc
        by_contra hlt
        exact hc (ih _ (not_le.mp hlt) β hβ rfl k)
      have hz : ∀ q, ∑ k, c α k * θ k (xs q) = 0 := by
        intro q
        obtain ⟨n, hn, φ, U, hU, h0U, hφ0, hs, hw, hθ', hH', hs0, hw0, hdet⟩ := hch q
        subst hn
        exact gs_id_linComb_eq_trF_mul_sval T a d (xs q) s w0 θ H φ U hU h0U hφ0 hs hw hθ' hH' hs0 hw0
          (by simpa only [Fin.cast_eq_self] using hdet) c hlow hda hmem α hα hαd
      have hsum : ∑ k, c α k • vals xs θ k = 0 := by
        funext q
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vals, Pi.zero_apply]
        exact hz q
      exact Fintype.linearIndependent_iff.mp hθ (c α) hsum
  intro α hα k
  exact key _ α hα rfl k

theorem indep_disjoint {Y : Type} {δ D m : ℕ} (T a : ℕ) (xs : Fin δ → Y) (s : Fin D → Y → ℂ) (w0 : Y → ℂ)
    (θ : Fin m → Y → ℂ) (H : Set (Y → ℂ))
    (hch : ∀ q, ∃ (n : ℕ) (hn : n = D) (φ : V n → Y) (U : Set (V n)), IsOpen U ∧ 0 ∈ U ∧ φ 0 = xs q ∧
      (∀ k, DifferentiableOn ℂ (fun z => s k (φ z)) U) ∧ DifferentiableOn ℂ (fun z => w0 (φ z)) U ∧
      (∀ i, DifferentiableOn ℂ (fun z => θ i (φ z)) U) ∧ (∀ f ∈ H, DifferentiableOn ℂ (fun z => f (φ z)) U) ∧
      (∀ k, s k (xs q) = 0) ∧ w0 (xs q) ≠ 0 ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s (Fin.cast hn k) (φ z) / w0 (φ z) : V n)) 0).det ≠ 0)
    (hθ : LinearIndependent ℂ (vals xs θ)) :
    LinearIndependent ℂ (fun p : {α : Fin D → ℕ // ∑ i, α i < a} × Fin m =>
      (∏ i, s i ^ p.1.1 i) * w0 ^ (T - ∑ i, p.1.1 i) * θ p.2) ∧
    Disjoint (Submodule.span ℂ (Set.range fun p : {α : Fin D → ℕ // ∑ i, α i < a} × Fin m =>
      (∏ i, s i ^ p.1.1 i) * w0 ^ (T - ∑ i, p.1.1 i) * θ p.2))
      (Submodule.span ℂ {g | ∃ (α : Fin D → ℕ) (f : Y → ℂ), ∑ i, α i = a ∧ f ∈ H ∧ g = (∏ i, s i ^ α i) * f}) := by
  classical
  haveI : Fintype {α : Fin D → ℕ // ∑ i, α i < a} :=
    Fintype.subtype (multiLt D a) (fun α => GlobalTheory.LeadIndep.mem_multiLt)
  have key : ∀ g : {α : Fin D → ℕ // ∑ i, α i < a} × Fin m → ℂ,
      (∑ p, g p • ((∏ i, s i ^ p.1.1 i) * w0 ^ (T - ∑ i, p.1.1 i) * θ p.2)) ∈
        Submodule.span ℂ {g | ∃ (α : Fin D → ℕ) (f : Y → ℂ), ∑ i, α i = a ∧ f ∈ H ∧
          g = (∏ i, s i ^ α i) * f} →
      ∀ p, g p = 0 := by
    intro g hg p
    have h1 := coeff_eq_zero T a xs s w0 θ H hch hθ
      (fun α k => if h : ∑ i, α i < a then g (⟨α, h⟩, k) else 0) (by
        convert hg using 1
        funext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Finset.prod_apply,
          Pi.pow_apply]
        rw [Finset.sum_subtype (multiLt D a) (fun α => GlobalTheory.LeadIndep.mem_multiLt),
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [dif_pos i.2]
        ring)
      p.1.1 (GlobalTheory.LeadIndep.mem_multiLt.mpr p.1.2) p.2
    simpa [p.1.2] using h1
  refine ⟨Fintype.linearIndependent_iff.mpr fun g hg => key g (hg ▸ Submodule.zero_mem _), ?_⟩
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have h2 := key g hx'
  simp [h2]

theorem main : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → LinearIndependent ℂ (vals xs θ) → LinearIndependent ℂ (R.lead w t Tn (a0 D j Tn) θ) ∧ Disjoint (Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ))) (R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn)) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs m θ hθ hli
  have hSS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) la c
      (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → DifferentiableOn ℂ P X.dom := by
    intro E _ _ _ r X la c P hP
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.SSgt, ReciprocityTheory.ChartRestriction.G.FD.Data.SS,
      ReciprocityTheory.ChartRestriction.G.FD.Data.IsBddSec, ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec, Set.mem_ofPred_eq] at hP
    exact hP.1.1.1.1
  have hspan := span_readings_components D T h j hj n R e hR
  have hRs : ∀ i' y, R.s w t i' y = ∑ l, t (i', l) * rdR h j (w l) (e y).1 (e y).2.1 := by
    intro i' y
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hsmem : ∀ i', R.s w t i' ∈ R.sp wL Set.univ := by
    intro i'
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨w l, Set.mem_univ _, rfl⟩)
  refine indep_disjoint Tn (a0 D j Tn) xs (fun i => R.s w t i.succ) (R.s w t 0) θ (R.sp _ Set.univ)
    (fun q => ?_) hli
  rcases hq : en q with ⟨k, i⟩
  have hx := hxs q
  rw [hq] at hx
  have hx0 : (Fl.Fl k).xs i ∈ ((T.U j T.σ₀).X k).dom := (Fl.Fl k).xs_mem i
  let φ : V (nd ((T.U j T.σ₀).X k)) → R.Y := fun z =>
    if hz : cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z ∈ ((T.U j T.σ₀).X k).dom then
      e.symm ⟨k, ⟨cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z, hz⟩⟩ else xs q
  let U : Set (V (nd ((T.U j T.σ₀).X k))) :=
    cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) ⁻¹' ((T.U j T.σ₀).X k).dom
  have hU : IsOpen U := (FourierCoefficientDomain.isOpen_dom _).preimage (IW.cpt_diff _ _).continuous
  have h0U : (0 : V (nd ((T.U j T.σ₀).X k))) ∈ U := by
    simp only [U, Set.mem_preimage, IW.cpt_zero]
    exact hx0
  have heφ : ∀ z (hz : z ∈ U), e (φ z) = ⟨k, ⟨cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z, hz⟩⟩ := by
    intro z hz
    simp only [φ, dif_pos (show cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z ∈ ((T.U j T.σ₀).X k).dom from hz),
      Equiv.apply_symm_apply]
  have hφ0 : φ 0 = xs q := by
    have h0 : cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) 0 ∈ ((T.U j T.σ₀).X k).dom := h0U
    simp only [φ, dif_pos h0]
    rw [Equiv.symm_apply_eq, hx]
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (IW.cpt_zero _ _)))
  have hdg : ∀ u (g : R.Y → ℂ), g ∈ R.sp u Set.univ → DifferentiableOn ℂ (fun z => g (φ z)) U := by
    intro u g hg
    obtain ⟨f, hf, hgf⟩ := (hspan u).1 g hg
    refine ((hSS _ _ _ _ _ _ (hf k)).comp (IW.cpt_diff _ _).differentiableOn (fun z hz => hz)).congr ?_
    intro z hz
    show g (φ z) = f k (cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z)
    rw [hgf, heφ z hz]
  have hseq : ∀ z ∈ U, ∀ a, R.s w t (Fin.cast (A.dim k) a).succ (φ z) =
      (Fl.Fl k).s a (cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z) := by
    intro z hz a
    rw [hRs, heφ z hz, Fl.hs]
  have hw0eq : ∀ z ∈ U, R.s w t 0 (φ z) = (Fl.Fl k).w0 (cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z) := by
    intro z hz
    rw [hRs, heφ z hz, Fl.h0]
  refine ⟨nd ((T.U j T.σ₀).X k), A.dim k, φ, U, hU, h0U, hφ0, fun k' => hdg _ _ (hsmem _),
    hdg _ _ (hsmem 0), fun i' => hdg _ _ (hθ i'), fun f hf => hdg _ f hf, ?_, ?_, ?_⟩
  · intro k'
    have h1 := hseq 0 h0U (Fin.cast (A.dim k).symm k')
    simp only [Fin.cast_cast, Fin.cast_eq_self, hφ0, IW.cpt_zero] at h1
    rw [h1]
    exact DivLC.s_xs_zero ((T.U j T.σ₀).X k) (Fl.Fl k) i _
  · have h1 := hw0eq 0 h0U
    rw [hφ0, IW.cpt_zero] at h1
    rw [h1]
    exact (Fl.Fl k).w0_ne i
  · have hev : (fun z => (WithLp.toLp 2 fun a => (fun i => R.s w t i.succ) (Fin.cast (A.dim k) a) (φ z) /
          R.s w t 0 (φ z) : V (nd ((T.U j T.σ₀).X k)))) =ᶠ[𝓝 0]
        (fun z => (WithLp.toLp 2 fun a => (Fl.Fl k).s a (cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z) /
          (Fl.Fl k).w0 (cpt ((T.U j T.σ₀).X k) ((Fl.Fl k).xs i) z) : V (nd ((T.U j T.σ₀).X k)))) := by
      filter_upwards [hU.mem_nhds h0U] with z hz
      simp only [hseq z hz, hw0eq z hz]
    rw [hev.fderiv_eq]
    exact (Fl.Fl k).coord i

end GlobalTheory.Shares.LeadDeep
