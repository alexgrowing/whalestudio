import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem aeval_mul_block (v : (Σ k, ι k) → Ω) (c : K → Ω) (b : K → ℕ) (g : MvPolynomial (Σ k, ι k) S)
    (hg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g b) :
    aeval (fun p => v p * c p.1) g = aeval v g * ∏ k, c k ^ b k := by
  have hb : ∀ e ∈ g.support, ∀ k, ∑ i, e ⟨k, i⟩ = b k := by
    intro e he k
    rw [sum_block_eq_blockWeight, hg (mem_support_iff.mp he)]
  have h2 : ((MvPolynomial.aeval c : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars S).comp (mConeMapOver S v) =
      aeval fun p => v p * c p.1 := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver]
  rw [← h2, AlgHom.comp_apply, AlgHom.restrictScalars_apply, mConeMapOver_eq_of_block v hb, map_mul, map_prod,
    aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_pow, aeval_X]

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) S) :
    f ∈ mIdealOver S y ↔
      ∀ b : K → ℕ, aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0 := by
  constructor
  · intro hf b
    rw [← coeff_mConeMapOver, RingHom.mem_ker.mp hf, coeff_zero]
  · intro h
    refine RingHom.mem_ker.mpr (MvPolynomial.ext _ _ fun d => ?_)
    have := coeff_mConeMapOver (S := S) y (⇑d) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, h, coeff_zero]

end Homog

theorem CurveLift.full : CurveLift.Statement := by
  intro k _ N Ω _ _ x Q n m s _hx hgen pp e hW
  have hpp := hW.isPrime
  obtain ⟨i, hXi⟩ := hW.relevant
  have hi : x i ≠ 0 := fun h0 => hXi (hW.le (by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]))
  have hPt := Kleiman.PrimeFiltration.Point.proof k Ω N x pp hpp hW.homog hW.le i hi hXi

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra k K')
      (ψ : Kleiman.chartRing k x (Kleiman.singleChart hi) →ₐ[k] K'),
      RingHom.ker ψ = Kleiman.chartPrime pp hi := by
    have : (Kleiman.chartPrime pp hi).IsPrime := hPt.1
    refine ⟨FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi),
      inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k _ _).comp (Ideal.Quotient.mkₐ k (Kleiman.chartPrime pp hi)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi))
      (Ideal.Quotient.mk (Kleiman.chartPrime pp hi) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hy : Kleiman.primeOf (S := k) (fun a => ψ (Kleiman.ratio hi a)) = pp := hPt.2 K' ψ hker

  have hiI : i ∈ (Kleiman.singleChart hi).1 := Finset.mem_singleton_self i
  let g : Fin m → Ω := fun b => x i ^ (-n) * s b
  have hgQ : Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) =
      Q.sub (Kleiman.singleChart hi) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have hb : s b ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.singleChart hi) := by
        rw [← hgen]; exact Submodule.subset_span ⟨b, rfl⟩
      obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI (s b)).mp hb
      have : g b = y := by
        simp only [g, hyb, smul_eq_mul, zpow_neg]
        field_simp
      rw [SetLike.mem_coe, this]
      exact hy
    · intro y hy
      have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range s) := by
        rw [hgen]
        exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI _).mpr ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨a, ?_⟩
      simp only [g, Subalgebra.smul_def, smul_eq_mul] at ha ⊢
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp

  obtain ⟨Q', hQQ⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← hgQ] at hQQ
  have hone : (1 : Ω) ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  have hgA : ∀ a b, g a * w b ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := by
    intro a b
    have h := Submodule.mul_mem_mul
      (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi))
        (Set.range g)) (hwQ b)
    rw [hQQ, Submodule.mem_one] at h
    obtain ⟨z, hz⟩ := h
    rw [← hz]
    exact z.2

  obtain ⟨j0, hj0⟩ : ∃ j0, ψ ⟨g j0 * w j0, hgA j0 j0⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : Kleiman.chartRing k x (Kleiman.singleChart hi)) = ∑ j, ⟨g j * w j, hgA j j⟩ :=
      Subtype.ext (by simp [hsum])
    have h2 := congrArg ψ h1
    rw [map_one, map_sum] at h2
    simp [hcon] at h2
  let t : Fin m → K' := fun b => ψ ⟨g b * w j0, hgA b j0⟩
  refine ⟨mIdealOver k (graphVec (fun a => ψ (Kleiman.ratio hi a)) t),
    isMultiProjPrime_mIdealOver_graph _ _ ⟨i, ?_⟩ ⟨j0, hj0⟩, ?_, by rw [comap_mIdealOver_graph, hy]⟩
  · have : Kleiman.ratio (S := k) hi i = 1 := Subtype.ext (div_self hi)
    rw [this, map_one]
    exact one_ne_zero
  · intro f hf
    rw [mem_mIdealOver_iff] at hf ⊢
    intro b
    have hfb := weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight (graphIdx N m)) b f
    let u : (Σ c, graphIdx N m c) → Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p =>
      match p with
      | ⟨Sum.inl (), a⟩ => Kleiman.ratio hi a
      | ⟨Sum.inr (), c⟩ => ⟨g c * w j0, hgA c j0⟩
    have hu : (fun p => (u p : Ω)) = fun p => graphVec x s p *
        (Sum.elim (fun _ : Unit => (x i)⁻¹) (fun _ : Unit => x i ^ (-n) * w j0)) p.1 := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩
      · change x a / x i = x a * (x i)⁻¹
        rw [div_eq_mul_inv]
      · change x i ^ (-n) * s a * w j0 = s a * (x i ^ (-n) * w j0)
        ring
    have h0 : aeval u (weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) b f) = 0 := by
      apply Subtype.ext
      change (Kleiman.chartRing k x (Kleiman.singleChart hi)).val (aeval u _) = 0
      rw [comp_aeval_apply]
      change aeval (fun p => (u p : Ω)) _ = 0
      rw [hu, aeval_mul_block _ _ b _ hfb, hf b, zero_mul]
    have hψu : (fun p => ψ (u p)) = graphVec (fun a => ψ (Kleiman.ratio hi a)) t := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
    rw [← hψu, ← comp_aeval_apply, h0, map_zero]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
