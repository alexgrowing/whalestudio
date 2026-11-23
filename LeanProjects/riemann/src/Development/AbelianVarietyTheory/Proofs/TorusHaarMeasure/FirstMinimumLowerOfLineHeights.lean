import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajorantEqSumNormSqOrthonormalFrameStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LineHeight

theorem gramDet_column {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (A * Matrix.of fun k (_ : Unit) => u k) a default = A.mulVec u a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.conjTranspose_apply, h, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_min_le_of_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  by_cases hm0 : m ≤ 0
  · exact absurd ((min_le_right _ _).trans (hm0.trans (hf i0))) (not_le.mpr (hcon i0))
  · have h1 : ∀ i, f i ≤ 1 := fun i => ((hcon i).trans_le (min_le_left _ _)).le
    have hp : ∏ i, f i ≤ f i0 := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right (hf i0) (Finset.prod_le_one (fun i _ => hf i) fun i _ => h1 i)
    have h2 : f i0 < m := (hcon i0).trans_le (min_le_right _ _)
    linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nonempty_cmType {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).2 h)⟩⟩

theorem c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ :=
  mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero τ.1).mpr X.ξ0_ne))

theorem exists_la1_lower_bound_of_line_heights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  intro r X d hd hr m hm
  have := nonempty_cmType X
  obtain ⟨τ0, -, hτ0⟩ := (Finset.univ : Finset X.Ψ).exists_min_image X.c Finset.univ_nonempty
  have hmin : 0 < min 1 m := lt_min one_pos hm
  have hδ : 0 < X.c τ0 * min 1 m := mul_pos (c_pos X τ0) hmin
  refine ⟨Real.sqrt (X.c τ0 * min 1 m), Real.sqrt_pos.2 hδ, fun x hx hW => ?_⟩
  obtain ⟨hdet, hmaj⟩ := GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx
  have key : ∀ v ∈ X.Λ, v ≠ 0 →
      X.c τ0 * min 1 m ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have hli : LinearIndependent E (fun _ : Unit => v) := linearIndependent_unique_iff.mpr hv0
    have hfin : Module.finrank E (Submodule.span E (Set.range fun _ : Unit => v)) = 1 := by
      rw [Set.range_const]
      exact finrank_span_singleton hv0
    have hg : ∀ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))).det.re =
          X.maj x τ (Data.emb τ.1 v) :=
      fun τ => (gramDet_column _ _).trans (hmaj τ _).symm
    have hmaj0 : ∀ τ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ => by
      rw [hmaj]
      positivity
    have hidx := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli fun _ => hv
    have h1 := hW _ hfin
    rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
    simp only [hg] at h1
    have h2 : m ≤ ∏ τ, X.maj x τ (Data.emb τ.1 v) :=
      h1.trans (div_le_self (Finset.prod_nonneg fun τ _ => hmaj0 τ)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx))
    obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hmaj0 m h2
    calc X.c τ0 * min 1 m ≤ X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hτ0 τ (Finset.mem_univ _)) hτ hmin.le (c_pos X τ).le
      _ ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
            (fun τ _ => mul_nonneg (c_pos X τ).le (hmaj0 τ)) (Finset.mem_univ τ)
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun v hv => hcon v hv
    rw [X.Λ_span] at hbot
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot hbot
  obtain ⟨v0, hv0, hv00⟩ := hne
  unfold Data.la1
  refine Real.sqrt_le_sqrt ?_
  unfold Data.firstMinimumSq
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0', rfl⟩
  exact key v hv hv0'

end GlobalTheory.LineHeight
