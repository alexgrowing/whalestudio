import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLineBundleRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

universe u w

section Scale

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ} {y : Fin (N + 1) → K'}

def scaleBundle (P : Kleiman.LineBundle k y) (μ : K') (hμ : μ ≠ 0) : Kleiman.LineBundle k y where
  sub I := Submodule.span (Kleiman.chartRing k y I) {μ} * P.sub I
  mono I J h z hz := by
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨w, P.mono I J h w hw, rfl⟩
  mem_iff I J h z := by
    simp only [Submodule.mem_span_singleton_mul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, haw⟩ := (P.mem_iff I J h w).mp hw
      refine ⟨a, ha, (a : K') • w, haw, ?_⟩
      simp only [smul_eq_mul]; ring
    · rintro ⟨a, ha, w, hw, hwz⟩
      refine ⟨μ⁻¹ * z, (P.mem_iff I J h _).mpr ⟨a, ha, ?_⟩, by field_simp⟩
      rw [smul_eq_mul] at hwz ⊢
      rw [show (a : K') * (μ⁻¹ * z) = w by
        rw [mul_left_comm, ← hwz, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]]
      exact hw
  fg I := (Submodule.fg_span_singleton μ).mul (P.fg I)
  invertible I := by
    obtain ⟨M, hM⟩ := P.invertible I
    refine ⟨Submodule.span (Kleiman.chartRing k y I) {μ⁻¹} * M, ?_⟩
    rw [mul_mul_mul_comm, hM, Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hμ,
      mul_one, ← Submodule.one_eq_span]

theorem restrictData_scale {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {Q : Kleiman.SubSystem k x Ω} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {P : Kleiman.LineBundle k y} {r : Ω → K'}
    (hr : Kleiman.RestrictData Q hxy P.toSubSystem r) (μ : K') (hμ : μ ≠ 0) :
    Kleiman.RestrictData Q hxy (scaleBundle P μ hμ).toSubSystem (fun q => μ * r q) where
  mem I q hq := Submodule.mem_span_singleton_mul.mpr ⟨r q, hr.mem I q hq, rfl⟩
  add I q hq q' hq' := by simp only [hr.add I q hq q' hq', mul_add]
  smul I q hq f s e hs hf hse := by simp only [hr.smul I q hq f s e hs hf hse]; ring
  span I := by
    change _ = Submodule.span _ {μ} * P.sub I
    rw [← hr.span I, Submodule.span_mul_span, Set.singleton_mul, Set.image_image]

end Scale

section GraphEq

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N m : ℕ}

abbrev baseRename : Kleiman.Poly k N →ₐ[k] MvPolynomial (Σ c, graphIdx N m c) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

theorem mConeMapOver_baseRename (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {g : Kleiman.Poly k N} {e : ℕ}
    (hg : g.IsHomogeneous e) :
    mConeMapOver k (graphVec x s) (baseRename g) = C (aeval x g) * X baseBlock ^ e := by
  have h1 := DFunLike.congr_fun (mConeMapOver_graph_comp_base (S := k) x s) g
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, Kleiman.cone_of_isHomogeneous x hg, AlgHom.restrictScalars_apply, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq]

theorem mConeMapOver_graphEq (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m) :
    mConeMapOver k (graphVec x s) (X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f) =
      C (s b * aeval x h - s l * aeval x f) * (X (Sum.inr ()) * X baseBlock ^ e) := by
  rw [map_sub, map_mul, map_mul, mConeMapOver_baseRename x s hh, mConeMapOver_baseRename x s hf]
  simp only [mConeMapOver, aeval_X, graphVec_inr, map_sub, map_mul]
  ring

theorem graphEq_of_le {K' : Type} [Field K'] [Algebra k K'] {x : Fin (N + 1) → Ω} {s : Fin m → Ω}
    {x' : Fin (N + 1) → K'} {s' : Fin m → K'}
    (hle : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s')) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m)
    (hx : s b * aeval x h = s l * aeval x f) : s' b * aeval x' h = s' l * aeval x' f := by
  have hmem : X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f ∈
      mIdealOver k (graphVec x s) := by
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    rw [mConeMapOver_graphEq x s hf hh, hx, sub_self, map_zero, zero_mul]
  have h0 := hle hmem
  change _ ∈ RingHom.ker _ at h0
  rw [RingHom.mem_ker] at h0
  change mConeMapOver k (graphVec x' s') _ = 0 at h0
  rw [mConeMapOver_graphEq x' s' hf hh, mul_eq_zero, C_eq_zero, sub_eq_zero] at h0
  exact h0.resolve_right (mul_ne_zero (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)))

end GraphEq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
