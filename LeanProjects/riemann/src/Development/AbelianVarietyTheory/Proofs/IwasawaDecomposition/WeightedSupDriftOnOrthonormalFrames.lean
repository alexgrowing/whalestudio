import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesBoundedOfDefinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanMap
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTop
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumLowerOfLineHeights
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSubspaceHeightGramDeterminant
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedForms
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrame
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetReNonneg
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightRpowNegDistortionContraction
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionOrthonormalHermitianFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MixedSignature

open GlobalTheory.HeightInv (relIndex_span_map)
open GlobalTheory.HeightEnds (gramDet_square)
open GlobalTheory.LineHeight (gramDet_column exists_min_le_of_le_prod nonempty_cmType c_pos)
open GlobalTheory.FiniteCovolume (nonneg_of_isLUB_image)
open GlobalTheory.DriftUnitary (continuous_orbit)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def MinGe {r : ℕ} (X : Data E r) (ε : ℝ) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.Λ, v ≠ 0 → ε ≤ QuadraticLatticeForms.Qy X (mat x) v

theorem height_lact : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X G d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]

theorem height_sup_lact_invariant : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X G d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hinv⟩ := height_lact r X d hd γ hγ x hx
  let e : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.GeneralLinearGroup.toLin γ |>.toLinearEquiv
  have he : (e : (Fin r → E) →ₗ[E] (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVecLin := by
    ext1 j
    rfl
  rw [← he] at hinv
  refine (hα i hi _ hx').unique ?_
  suffices hs : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} by
    rw [hs]
    exact hα i hi x hx
  ext t
  constructor
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e.symm : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d x _ ^ (-δ) = d (lact γ x) W ^ (-δ)
      rw [← hinv, ← Submodule.map_comp]
      simp
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d (lact γ x) _ ^ (-δ) = d x W ^ (-δ)
      rw [hinv]

theorem norm_det_orth {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (x : Frame X.Ψ r) (hx : Orth X G p x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 G.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [GlobalTheory.HeightEnds.gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn (p τ) (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring

theorem exists_pos_le_bot_top : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, Orth X G p x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X G p hG d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 G.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hG)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2

theorem minGe_of_lines : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → MinGe X ε x) := by
  intro r X d hd m hm
  have := nonempty_cmType X
  obtain ⟨τ0, hτ0⟩ := Finite.exists_min X.c
  have hmin : 0 < min 1 m := lt_min one_pos hm
  refine ⟨X.c τ0 * min 1 m, mul_pos (c_pos X τ0) hmin, ?_⟩
  intro x hdet hW v hv hv0
  unfold QuadraticLatticeForms.Qy
  have hli : LinearIndependent E (fun _ : Unit => v) := by
    rw [linearIndependent_unique_iff]; exact hv0
  have hrank : Module.finrank E (Submodule.span E (Set.range (fun _ : Unit => v))) = 1 := by
    rw [finrank_span_eq_card hli]; simp
  have h1 := hW _ hrank
  rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli (fun _ => hv)
  have hnn : ∀ τ : X.Ψ, 0 ≤ (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := fun τ => by
    positivity
  have hprod : (∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))ᴴ *
      ((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))).det.re))
      = ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
    Finset.prod_congr rfl fun τ _ => by
      exact gramDet_column _ (Data.emb τ.1 v)
  have h2 : m ≤ ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := by
    refine h1.trans ?_
    rw [← hprod]
    refine div_le_self ?_ ?_
    · rw [hprod]; exact Finset.prod_nonneg fun τ _ => hnn τ
    · exact_mod_cast Nat.one_le_iff_ne_zero.2 hind
  obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hnn m h2
  calc X.c τ0 * min 1 m ≤ X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
        mul_le_mul (hτ0 τ) hτ hmin.le (c_pos X τ).le
    _ ≤ _ := Finset.single_le_sum (f := fun τ => X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2))
        (fun τ _ => mul_nonneg (c_pos X τ).le (hnn τ)) (Finset.mem_univ τ)

theorem weighted_sup_drift_on_orthonormal_frames :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, Orth X G p x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  intro r X G p hG d hd τ0 S hS hirr hU
  obtain ⟨δ, c, Ω, hδ, hc0, hc1, hΩ, hw⟩ := GlobalTheory.height_rpow_neg_distortion_contraction r X d hd τ0 S hS hirr
  refine ⟨δ, hδ, fun α hα => ?_⟩
  have hdet : ∀ y : {x // Orth X G p x}, ∀ τ : X.Ψ, (mat y.1 τ).det ≠ 0 :=
    fun y => det_ne_zero_of_isOrth X y.2
  have hpos : ∀ y : {x // Orth X G p x}, ∀ W, 0 < d y.1 W := fun y W => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd y.1 (hdet y)
    exact hm.trans_le (h W)
  let t : S → {x // Orth X G p x} → {x // Orth X G p x} := fun a y =>
    ⟨_, isOrth_update_mul_inv r X τ0 y.1 a.1 y.2 (hU a.1 a.2)⟩
  have hfr : Module.finrank E (Fin r → E) = r := by simp
  obtain ⟨C, hC, halt⟩ := GlobalTheory.subspace_sup_alternative E (Fin r → E) {x // Orth X G p x} S r t
    (fun y W => d y.1 W ^ (-δ)) (fun i y => α i y.1) c Ω hfr hΩ
    (fun y W => Real.rpow_pos_of_pos (hpos y W) _)
    (fun i hi y => hα i hi y.1 (hdet y))
    (fun y W₁ W₂ => by
      have h := GlobalTheory.HeightSubmodular.height_submodular r X d hd y.1 (hdet y) W₁ W₂
      rw [← Real.mul_rpow (hpos y _).le (hpos y _).le, ← Real.mul_rpow (hpos y _).le (hpos y _).le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos (hpos y _) (hpos y _)) h (by linarith))
    (fun s y W => (hw y.1 (hdet y) W).1 s.1 s.2)
    (fun y W h0 h1 => by
      have h := (hw y.1 (hdet y) W).2 h0 h1
      rw [← Finset.sum_coe_sort] at h
      rw [Fintype.card_coe]
      exact h)
  obtain ⟨m, hm, htop⟩ := exists_pos_le_bot_top r X G p hG d hd
  obtain ⟨e, c', b, he, hc'0, hc'1, hb, hdr⟩ := GlobalTheory.weighted_sum_drift_inequality
    {x // Orth X G p x} S r t (fun i y => α i y.1) c C (m ^ (-δ)) hc0 hc1 hC
    (fun i hi y => nonneg_of_isLUB_image (fun W => (Real.rpow_pos_of_pos (hpos y W) _).le)
      (hα i hi y.1 (hdet y)))
    (fun y => by
      constructor
      · refine (hα 0 (Nat.zero_le r) y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊥ := Submodule.finrank_eq_zero.1 hW
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).1 (by linarith)
      · refine (hα r le_rfl y.1 (hdet y)).2 ?_
        rintro _ ⟨W, hW, rfl⟩
        have hW' : W = ⊤ := Submodule.eq_top_of_finrank_eq (hW.trans hfr.symm)
        subst hW'
        exact Real.rpow_le_rpow_of_nonpos hm (htop y.1 y.2).2 (by linarith))
    halt
  refine ⟨e, c', b, he, hc'0, hc'1, hb, fun x hx => ?_⟩
  have h := hdr ⟨x, hx⟩
  rw [Fintype.card_coe] at h
  rw [← Finset.sum_coe_sort]
  exact h

theorem exists_drift_function_orthFrames : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (τ0 : X.Ψ), 0 < p τ0 → p τ0 < r → ∀ (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | Orth X G p x} ∧ (∀ x, Orth X G p x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x, Orth X G p x → f (lact γ x) = f x) ∧ (∀ x, Orth X G p x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, Orth X G p x → f x ≤ M → MinGe X ε x) := by
  intro r X G p hG τ0 hp0 hpr S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.SubspaceHeight.exists_height r X
  obtain ⟨δ, hδ, hdrift⟩ := weighted_sup_drift_on_orthonormal_frames r X G p hG d hd τ0 S hS hirr hU
  obtain ⟨α, hα, hlsc⟩ := GlobalTheory.exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hineq⟩ := hdrift α hα
  have hinv : ∀ x, Orth X G p x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 :=
    fun x hx => det_ne_zero_of_isOrth X hx
  have hdpos : ∀ x, Orth X G p x → ∀ W, 0 < d x W := by
    intro x hx W
    obtain ⟨m, hm, hW⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd x (hinv x hx)
    exact hm.trans_le (hW W)
  have hαnn : ∀ x, Orth X G p x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := E) (M := Fin r → E) (n := i)
      (by simpa using hi)
    have hW : Module.finrank E (Submodule.span E (Set.range v)) = i := by
      simpa using finrank_span_eq_card hv
    exact (Real.rpow_nonneg (hdpos x hx _).le _).trans
      ((hα i hi x (hinv x hx)).1 ⟨_, hW, rfl⟩)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hineq, ?_⟩
  · refine lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi => ?_
    exact (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hinv x hx
  · intro x hx
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [height_sup_lact_invariant r X d hd δ α hα γ hγ x (hinv x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have hM' : 0 < max 1 (M / e 1) := lt_max_of_lt_left one_pos
    obtain ⟨ε, hε, hla⟩ := minGe_of_lines r X d hd ((max 1 (M / e 1)) ^ (-δ)⁻¹)
      (Real.rpow_pos_of_pos hM' _)
    refine ⟨ε, hε, fun x hx hM => hla x (hinv x hx) fun W hW => ?_⟩
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨one_pos, by omega⟩
    have h2 : e 1 * α 1 x ≤ M :=
      (Finset.single_le_sum (f := fun i => e i * α i x) (fun i hi =>
        mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)) h1).trans hM
    have h3 : α 1 x ≤ M / e 1 := by
      rw [le_div_iff₀ (he 1), mul_comm]; exact h2
    have h4 : d x W ^ (-δ) ≤ max 1 (M / e 1) :=
      (((hα 1 (by omega) x (hinv x hx)).1 ⟨W, hW, rfl⟩).trans h3).trans (le_max_right _ _)
    exact (Real.rpow_inv_le_iff_of_neg hM' (hdpos x hx W) (by linarith)).2 h4

theorem exists_drift_function :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (τ0 : X.Ψ) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < p τ0 → p τ0 < r → ∀ x0, Orth X G p x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → MinGe X ε (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X G p hG τ0 H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := GlobalTheory.gramDet_closed_forms.2.2.2 r (p τ0) hp0 hpr
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hprop⟩ :=
    exists_drift_function_orthFrames r X G p hG τ0 hp0 hpr S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horth : ∀ g : H, Orth X G p (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  have hlift := fun a : S => (hS3 a a.2).2.elim fun s hs =>
    step_of_right_mul r X H hH x0 hx0 τ0 a s (hS3 a a.2).1 hs.1 hs.2
  choose h k hk hg using hlift
  refine ⟨S, inferInstance, hSne.coe_sort, h, fun g => f (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨k s, hk s⟩, ?_, fun g => hf0 _ (horth g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · apply LowerSemicontinuous.measurable
    rw [← lowerSemicontinuousOn_univ_iff]
    exact hlsc.comp (continuous_orbit X H x0).continuousOn (fun g _ => horth g)
  · rintro u ⟨γ, hγ, hu⟩ g
    refine Eq.trans (congrArg f ?_) (hfinv γ hγ _ (horth g))
    funext τ
    change ((((u : X.Ψ → GL (Fin r) ℂ) τ * (g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * mat x0 τ : Matrix (Fin r) (Fin r) ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ) :
        Matrix (Fin r) (Fin r) ℂ)
    rw [Units.val_mul, hu τ, Matrix.mul_assoc]
  · intro g
    have := hdrift _ (horth g)
    rw [← Finset.sum_coe_sort S] at this
    simp only [hg, Fintype.card_coe]
    exact this
  · intro M
    obtain ⟨ε, hε, hM⟩ := hprop M
    exact ⟨ε, hε, fun g hgM => hM _ (horth g) hgM⟩

end GlobalTheory.MixedSignature
