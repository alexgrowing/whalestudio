import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem form_eq_zero_of_im {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → V → ℂ)
    (h1 : ∀ w, IsLinearMap ℂ (fun z => f z w)) (h2 : ∀ z, IsLinearMap ℝ (f z)) (S : Set V)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ u ∈ S, ∀ v ∈ S, (f u v).im = 0) (z w : V) : f z w = 0 := by
  have key : ∀ z w, (f z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu =>
      induction hw using Submodule.span_induction with
      | mem v hv => exact h u hu v hv
      | zero => rw [(h2 u).map_zero, zero_im]
      | add a b _ _ ha hb => rw [(h2 u).map_add, add_im, ha, hb, add_zero]
      | smul t a _ ha => rw [(h2 u).map_smul, smul_im, ha, smul_zero]
    | zero => rw [(h1 w).map_zero, zero_im]
    | add a b _ _ ha hb => rw [(h1 w).map_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [← Complex.coe_smul, (h1 w).map_smul, smul_eq_mul, im_ofReal_mul, ha, mul_zero]
  have h3 := key (I • z) w
  rw [(h1 w).map_smul, smul_eq_mul, I_mul_im] at h3
  exact Complex.ext h3 (key z w)

theorem hermForm_eq_of_im {g : ℕ} (M M' : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ u ∈ S, ∀ v ∈ S, (hermForm M (a * u) v).im = (hermForm M' u (b * v)).im) (z w : Fin g → ℂ) :
    hermForm M (a * z) w = hermForm M' z (b * w) := by
  refine sub_eq_zero.1 (form_eq_zero_of_im (fun z w => hermForm M (a * z) w - hermForm M' z (b * w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) S hS
    (fun u hu v hv => by rw [sub_im, h u hu v hv, sub_self]) z w)
  · simp only [hermForm, mul_add, add_dotProduct]; ring
  · simp only [hermForm, mul_smul_comm, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hermForm, mul_add, star_add, mulVec_add, dotProduct_add]; ring
  · simp only [hermForm, mul_smul_comm, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_eq_hermForm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas idx x z w = hermForm (ThFr.Hm X bas idx x) z w := (hermForm_Hm bas idx x z w).symm

theorem span_range_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range (pv X idx x)) = ⊤ := by
  have col (s : Fin g → Fin g ⊕ Fin g) (t : Fin g → ℝ) :
      perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) ∈ Submodule.span ℝ (Set.range (pv X idx x)) := by
    have : perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) =
        ∑ k, t k • pv X idx x (bas (Pi.single (s k) 1)) := by
      funext i
      simp [mulVec, dotProduct, pv, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine eq_top_iff.2 fun z _ => ?_
  have hu := isUnit_det_perMat idx hs hx
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  set τ := tauMat X bas idx x with hτ
  set y := hMat X bas idx x *ᵥ z with hy
  obtain ⟨t, ht⟩ : ∃ t : Fin g → ℝ, τ.map Complex.im *ᵥ t = fun k => (y k).im :=
    ⟨(τ.map Complex.im)⁻¹ *ᵥ _, by rw [mulVec_mulVec, mul_nonsing_inv _ hY, one_mulVec]⟩
  have h1 : y = (fun k => (((y - τ *ᵥ fun k => (t k : ℂ)) k).re : ℂ)) + τ *ᵥ fun k => (t k : ℂ) := by
    funext k
    apply Complex.ext
    · simp
    · have := congrFun ht k
      simp only [mulVec, dotProduct, map_apply] at this
      simp [mulVec, dotProduct, this]
  have hAB : perMat X bas idx Sum.inl x * τ = perMat X bas idx Sum.inr x :=
    mul_nonsing_inv_cancel_left _ _ hu
  have h2 : z = perMat X bas idx Sum.inl x *ᵥ y := by
    rw [hy, mulVec_mulVec, hMat, mul_nonsing_inv _ hu, one_mulVec]
  rw [h2, h1, mulVec_add, mulVec_mulVec, hAB]
  exact add_mem (col _ _) (col _ _)

theorem span_image_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L : Lt E r)
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ := by
  rw [eq_top_iff, ← span_range_pv idx hs hx, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem L hL v
  have : pv X idx x v = (k : ℝ)⁻¹ • pv X idx x (k • v) := by
    funext i
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [pv, pv, per_zsmul]
    simp only [Function.comp_apply, Pi.smul_apply, zsmul_eq_mul, real_smul, ofReal_inv, Pi.mul_apply, Pi.intCast_apply,
      ofReal_intCast]
    rw [inv_mul_cancel_left₀ hk']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv, rfl⟩)

theorem pv_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) :
    pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
  funext fun _ => per_smul X x a v _

theorem EF_smul_left (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  have h (b : E) : IsCMField.complexConj E (IsCMField.complexConj E a * b) = a * IsCMField.complexConj E b := by
    rw [map_mul, IsCMField.complexConj_apply_apply]
  simp only [EF_def, herm, cc, Pi.smul_apply, smul_eq_mul, h]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hx_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  intro E _ _ _ r X g bas idx n hs _ x hx
  have him {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v) :
      (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  simp only [hx_eq_hermForm]
  refine ⟨fun z w => ?_, fun z hz => hermForm_Hm_pos idx hs hx hz, him hx, fun a z w => ?_,
    pv_smul idx x, fun u v h => ?_, fun L hL => ⟨span_image_pv idx hs hx L hL, fun M _ h z w => ?_⟩,
    fun ga hga => ⟨hga.lact_mem hx, fun v => ?_, fun h τ i => ?_, fun z w => ?_⟩⟩
  · have hH := Hm_isHermitian idx hs hx
    rw [hermForm, hermForm, ← RCLike.star_def, ← star_dotProduct_star, star_mulVec, star_star, hH.eq,
      dotProduct_mulVec]
  · refine hermForm_eq_of_im _ _ (fun j => rowType X (idx j) a) (fun j => rowType X (idx j) (cc a)) _
      (span_range_pv idx hs hx) ?_ z w
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have h1 := him hx (a • u) v
    have h2 := him hx u (cc a • v)
    rw [pv_smul] at h1 h2
    rw [EF_smul_left] at h1
    exact h1.trans h2.symm
  · obtain ⟨m, rfl⟩ := vecQ_surjective X bas u
    obtain ⟨m', rfl⟩ := vecQ_surjective X bas v
    have h' (t) : EF X (vecQ X bas m) (vecQ X bas t) = EF X (vecQ X bas m') (vecQ X bas t) := by
      have := (him hx (vecQ X bas m) (vecQ X bas t)).symm.trans (h ▸ him hx (vecQ X bas m') (vecQ X bas t))
      exact_mod_cast this
    simp only [EF_vecQ hs] at h'
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  · have := hermForm_eq_of_im M (ThFr.Hm X bas idx x) 1 1 _ (span_image_pv idx hs hx L hL) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [_root_.one_mul, _root_.one_mul, h u hu v hv, him hx]) z w
    rwa [_root_.one_mul, _root_.one_mul] at this
  · rw [pv, per_lact x hga, pv]
  · have e1 : mat (lact ga x) τ = (ga : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have e2 : FD.gram τ.1 X.Gm (mat (lact ga x) τ) = FD.gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hga]
    have h' := h τ i
    unfold dmin at h' ⊢
    rwa [e2]
  · have := hermForm_eq_of_im (ThFr.Hm X bas idx (lact ga x)) (ThFr.Hm X bas idx x) 1 1 _
      (span_range_pv idx hs hx) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      have h1 := him (hga.lact_mem hx) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v)
      rw [pv, pv, per_lact x hga, per_lact x hga, EF_def, hga, ← EF_def] at h1
      rw [_root_.one_mul, _root_.one_mul, him hx]
      exact h1) z w
    rwa [_root_.one_mul, _root_.one_mul] at this

end GlobalTheory.Dict
