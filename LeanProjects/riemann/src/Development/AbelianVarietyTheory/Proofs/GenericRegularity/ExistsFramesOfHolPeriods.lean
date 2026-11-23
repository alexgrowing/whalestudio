import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq

noncomputable section

namespace GlobalTheory.HolChartLift

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
open GlobalTheory.TorsionHolomorphic
open scoped Matrix

section Matrices

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem differentiableOn_coord_of_pairing_of_span_eq_top {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (S : Set (Fin r → E))
    (hS : Submodule.span E S = ⊤) (B : Set W) (u : W → Fin r → ℂ)
    (hu : ∀ v ∈ S, DifferentiableOn ℂ (fun b => ∑ a, u b a * τ (v a)) B) (a : Fin r) :
    DifferentiableOn ℂ (fun b => u b a) B := by
  classical
  have key : ∀ v ∈ Submodule.span E S, DifferentiableOn ℂ (fun b => ∑ a, u b a * τ (v a)) B := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hu v hv
    | zero => simpa using differentiableOn_const (0 : ℂ)
    | add v w _ _ h1 h2 =>
      simpa only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib] using h1.fun_add h2
    | smul s v _ h1 =>
      refine (h1.const_mul (τ s)).congr fun b _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
  refine (key (Pi.single a 1) (hS ▸ Submodule.mem_top)).congr fun b _ => ?_
  simp [Pi.single_apply, apply_ite τ]

def mixRows {r : ℕ} (q : ℕ) (Y Z : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i a => if (i : ℕ) < q then Y i a else Z i a

def mixCols {r : ℕ} (q : ℕ) (Y Z : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => if (j : ℕ) < q then Y a j else Z a j

theorem mixRows_self {r : ℕ} (q : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ) : mixRows q Y Y = Y := by
  ext i a
  simp [mixRows]

theorem inv_mul_mix {r : ℕ} (q : ℕ) (X Y : Matrix (Fin r) (Fin r) ℂ) (hX : X.det ≠ 0)
    (hN : (mixRows q Y X⁻¹).det ≠ 0) (i j : Fin r) (hij : j ≤ i) :
    (X⁻¹ * mixCols q X (mixRows q Y X⁻¹)⁻¹) i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
  by_cases hj : (j : ℕ) < q
  · rw [← Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.2 hX)]
    simp only [Matrix.mul_apply, mixCols, Matrix.of_apply, if_pos hj]
  · have hi : ¬ (i : ℕ) < q := by
      have : (j : ℕ) ≤ i := hij
      omega
    rw [← Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hN)]
    simp only [Matrix.mul_apply, mixCols, Matrix.of_apply, if_neg hj]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    simp only [mixRows, Matrix.of_apply, if_neg hi]

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

theorem exists_hol_frame (Ψ : Finset (E →+* ℂ)) (q : ℕ) {B : Set W} (hB : IsOpen B) (x : W → Frame Ψ r)
    (hx : ∀ b ∈ B, ∀ τ, (mat (x b) τ).det ≠ 0)
    (hcol : ∀ τ a (j : Fin r), (j : ℕ) < q → DifferentiableOn ℂ (fun b => mat (x b) τ a j) B)
    (hrow : ∀ τ (i : Fin r) a, ¬ (i : ℕ) < q → DifferentiableOn ℂ (fun b => (mat (x b) τ)⁻¹ i a) B)
    {b₀ : W} (hb₀ : b₀ ∈ B) :
    ∃ (B₁ : Set W) (x' : W → Frame Ψ r), IsOpen B₁ ∧ b₀ ∈ B₁ ∧ B₁ ⊆ B ∧ DifferentiableOn ℂ x' B₁ ∧
      ∀ b ∈ B₁, ∃ β ∈ Bor Ψ r, x' b = rmul (x b) β := by
  let N : W → Ψ → Matrix (Fin r) (Fin r) ℂ := fun b τ => mixRows q (mat (x b₀) τ)⁻¹ (mat (x b) τ)⁻¹
  have hN : ∀ τ i a, DifferentiableOn ℂ (fun b => N b τ i a) B := by
    intro τ i a
    by_cases hi : (i : ℕ) < q
    · simp only [N, mixRows, Matrix.of_apply, if_pos hi]
      exact differentiableOn_const _
    · simp only [N, mixRows, Matrix.of_apply, if_neg hi]
      exact hrow τ i a hi
  have hD : DifferentiableOn ℂ (fun b => ∏ τ, (N b τ).det) B :=
    differentiableOn_finset_prod _ (fun τ b => (N b τ).det) B fun τ => differentiableOn_det _ B (hN τ)
  have hdet : ∀ b ∈ B ∩ (fun b => ∏ τ, (N b τ).det) ⁻¹' {0}ᶜ, ∀ τ, (N b τ).det ≠ 0 := fun b hb τ =>
    Finset.prod_ne_zero_iff.1 hb.2 τ (Finset.mem_univ _)
  refine ⟨B ∩ (fun b => ∏ τ, (N b τ).det) ⁻¹' {0}ᶜ, fun b τ => mixCols q (mat (x b) τ) (N b τ)⁻¹,
    hD.continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, ?_⟩, Set.inter_subset_left, ?_,
    fun b hb => ⟨fun τ => ((mat (x b) τ)⁻¹ * mixCols q (mat (x b) τ) (N b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ),
      fun τ => ?_, ?_⟩⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => ?_
    simp only [N, mixRows_self]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hx b₀ hb₀ τ))).ne_zero
  · refine differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun j => ?_
    by_cases hj : (j : ℕ) < q
    · simp only [mixCols, Matrix.of_apply, if_pos hj]
      exact (hcol τ a j hj).mono Set.inter_subset_left
    · simp only [mixCols, Matrix.of_apply, if_neg hj]
      exact differentiableOn_matrix_inv (fun b => N b τ) _ (fun i a => (hN τ i a).mono Set.inter_subset_left)
        (fun b hb => hdet b hb τ) a j
  · have h := inv_mul_mix q (mat (x b) τ) (mat (x b₀) τ)⁻¹ (hx b hb.1 τ) (hdet b hb τ)
    have hlow : ∀ a c : Fin r, c < a →
        ((mat (x b) τ)⁻¹ * mixCols q (mat (x b) τ) (N b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) a c = 0 :=
      fun a c hca => (h a c hca.le).trans (Matrix.one_apply_ne hca.ne')
    refine ⟨?_, hlow⟩
    change ((mat (x b) τ)⁻¹ * mixCols q (mat (x b) τ) (N b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    rw [Matrix.det_of_upperTriangular (fun a c hca => hlow a c hca)]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [h i i le_rfl, Matrix.one_apply_eq]
    exact one_ne_zero
  · funext τ
    change mixCols q (mat (x b) τ) (N b τ)⁻¹ =
      mat (x b) τ * ((mat (x b) τ)⁻¹ * mixCols q (mat (x b) τ) (N b τ)⁻¹)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hx b hb.1 τ))]

theorem exists_hol_chart (X : Data E r) {B : Set W} (hB : IsOpen B) (x : W → Frame X.Ψ r)
    (hx : ∀ b ∈ B, x b ∈ X.dom) (hd : DifferentiableOn ℂ x B) {b₀ : W} (hb₀ : b₀ ∈ B) :
    ∃ (B₁ : Set W) (z : W → V (nd X)), IsOpen B₁ ∧ b₀ ∈ B₁ ∧ B₁ ⊆ B ∧ DifferentiableOn ℂ z B₁ ∧ z b₀ = 0 ∧
      ∀ b ∈ B₁, cpt X (x b₀) (z b) ∈ X.dom ∧ ∃ β ∈ Bor X.Ψ r, x b = rmul (cpt X (x b₀) (z b)) β := by
  have h0 : ∀ τ, IsUnit (mat (x b₀) τ).det := fun τ => isUnit_iff_ne_zero.2 (hx b₀ hb₀ τ).1
  have hM : ∀ τ, LUPf.Mx X (x b₀) (x b₀) τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (h0 τ)
  have hl : ∀ k, lminor (1 : Matrix (Fin r) (Fin r) ℂ) k = 1 := by
    intro k
    unfold lminor
    rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 :=
    (LUPf.Lm_unique 1 1 (fun k => by rw [hl]; exact one_ne_zero) (fun i k h => Matrix.one_apply_ne h.ne)
      (fun i => Matrix.one_apply_eq i) fun i j h => by rw [mul_one]; exact Matrix.one_apply_ne h.ne').symm
  have hD : DifferentiableOn ℂ (fun b => LUPf.DeltaF X (x b₀) (x b)) B :=
    LUPf.Delta_diff.comp_differentiableOn hd
  refine ⟨B ∩ (fun b => LUPf.DeltaF X (x b₀) (x b)) ⁻¹' {0}ᶜ, fun b => LUPf.zF X (x b₀) (x b),
    hD.continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, ?_⟩, Set.inter_subset_left,
    LUPf.zF_diffOn.comp (hd.mono Set.inter_subset_left) fun b hb => ⟨hx b hb.1, hb.2⟩, ?_, fun b hb => ?_⟩
  · change LUPf.DeltaF X (x b₀) (x b₀) ≠ 0
    simp only [LUPf.DeltaF, hM, hl, Finset.prod_const_one]
    exact one_ne_zero
  · ext k
    change LUPf.nF X (x b₀) (x b₀) _ _ _ = 0
    simp only [LUPf.nF, hM, hL, inv_one]
    exact Matrix.one_apply_ne ((Fintype.equivFin (Ent X)).symm k).2.2.ne'
  · have hb' := LUPf.bF_mem (hx b hb.1) hb.2
    have hs : x b = rmul (cpt X (x b₀) (LUPf.zF X (x b₀) (x b))) (LUPf.bF X (x b₀) (x b)) := by
      funext τ
      change x b τ = (mat (x b₀) τ * mat (nmat X (LUPf.zF X (x b₀) (x b))) τ *
        (LUPf.Lm (LUPf.Mx X (x b₀) (x b) τ) * LUPf.Mx X (x b₀) (x b) τ) : Matrix (Fin r) (Fin r) ℂ)
      rw [LUPf.nmat_zF]
      change x b τ = (mat (x b₀) τ * (LUPf.Lm (LUPf.Mx X (x b₀) (x b) τ))⁻¹ *
        (LUPf.Lm (LUPf.Mx X (x b₀) (x b) τ) * ((mat (x b₀) τ)⁻¹ * mat (x b) τ)) : Matrix (Fin r) (Fin r) ℂ)
      have hLu : IsUnit (LUPf.Lm (LUPf.Mx X (x b₀) (x b) τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hLu,
        Matrix.mul_nonsing_inv_cancel_left _ _ (h0 τ)]
      rfl
    refine ⟨?_, _, hb', hs⟩
    have h := OrthogonalFrameDomain.rmul_mem_dom X (Set.mem_of_eq_of_mem hs.symm (hx b hb.1)) (ExtFPf.invF_mem X hb')
    rwa [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb', ExtFPf.rmul_oneF] at h

section Periods

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Frames GlobalTheory.FrameUnif

theorem exists_frames_of_holPeriods {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (X : Data E r)
    (φ : D.La ≃ₗ[𝓞 E] X.Λ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hp : D.p = Dw.p) (hq : D.q = Dw.q)
    (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (hneg : r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) {m : ℕ} {B : Set (Fin m → ℂ)} (hB : IsOpen B)
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ)))
    (hP : IsHolPeriods D (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B₁ : Set (Fin m → ℂ)) (x' : (Fin m → ℂ) → Frame X.Ψ r), IsOpen B₁ ∧ b₀ ∈ B₁ ∧ B₁ ⊆ B ∧
      DifferentiableOn ℂ x' B₁ ∧ ∀ b ∈ B₁, ∃ x ∈ X.dom, (∀ a j, P b a j =
        Formalism.L2.PjFree.perFr X x (φ a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) ∧
        ∃ β ∈ Bor X.Ψ r, x' b = rmul x β := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ X.Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    haveI : IsEmpty (Fin g) := idx.isEmpty
    obtain ⟨hx, -⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E 0 X.p0 X.Ψ X.Gm
      X.Gm_herm).2.1 (fun _ a => a.elim0) (fun τ => Subsingleton.elim _ _)
    exact ⟨B, fun _ _ a => a.elim0, hB, hb₀, subset_rfl, differentiableOn_const _, fun b _ =>
      ⟨_, hx, fun _ j => isEmptyElim j, _, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X _).symm⟩⟩
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    intro τ hτ
    have := hneg hr0 τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hty' : ∀ j, Formalism.L2.PjFree.relab c σ (e j).1 = if ((idx j).2 : ℕ) < D.q then
      ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1 := by
    intro j
    rw [hq]
    rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  have hper : ∀ (x : Frame X.Ψ r) (v : Fin r → E) j,
      Formalism.L2.PjFree.perFr X x v (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 =
      if ((idx j).2 : ℕ) < D.q then
        hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
    intro x v j
    have h := hi j
    rw [hq]
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg a, dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl
  let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
  have hφ' : Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧
      (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ' x) (φ' y)) := by
    refine ⟨fun a b hab => φ.injective (Subtype.ext hab), ?_, X.Gm_herm, X.Gm_det, hef⟩
    have hrange : Set.range φ' = X.Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
    rw [hrange]
    exact X.Λ_span
  choose! x hx hPx using fun b (hb : b ∈ B) => GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _
    hty' hξ hpos hφ' (by rw [hp, hq, hr]) (P b) (hP.1 b hb)
  have hPd : ∀ v (t : X.Ψ × Fin r), DifferentiableOn ℂ (fun b => P b v (idx.symm t)) B := fun v t =>
    differentiableOn_pi.1 (hP.2 v) _
  obtain ⟨B₁, x', h1, h2, h3, h4, h5⟩ := exists_hol_frame X.Ψ D.q hB x (fun b hb τ => (hx b hb τ).1)
    (fun τ a j hj => by
      have hu : ∀ k, DifferentiableOn ℂ (fun b => ∑ i, mat (x b) τ i j * τ.1 (X.Gm i k)) B := by
        refine differentiableOn_coord_of_pairing_of_span_eq_top (ComplexEmbedding.conjugate τ.1) _ hφ'.2.1 B _ ?_
        rintro _ ⟨v, rfl⟩
        refine (hPd v (τ, j)).congr fun b hb => ?_
        rw [hPx b hb, Equiv.apply_symm_apply, if_pos hj]
        simp only [hermC, col, Data.emb, Finset.sum_mul, ComplexEmbedding.conjugate_coe_eq]
        exact Finset.sum_comm
      have hG : IsUnit (X.Gm.map τ.1).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact isUnit_iff_ne_zero.2 ((map_ne_zero τ.1).2 X.Gm_det)
      refine (differentiableOn_finset_sum Finset.univ
        (fun k b => (∑ i, mat (x b) τ i j * τ.1 (X.Gm i k)) * (X.Gm.map τ.1)⁻¹ k a) B
        fun k => (hu k).mul_const _).congr fun b _ => ?_
      have := congrFun (congrFun (Matrix.mul_nonsing_inv_cancel_right (X.Gm.map τ.1) (mat (x b) τ)ᵀ hG) j) a
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using this.symm)
    (fun τ i a hi' => by
      refine differentiableOn_coord_of_pairing_of_span_eq_top τ.1 _ hφ'.2.1 B (fun b => (mat (x b) τ)⁻¹ i) ?_ a
      rintro _ ⟨v, rfl⟩
      refine (hPd v (τ, i)).congr fun b hb => ?_
      rw [hPx b hb, Equiv.apply_symm_apply, if_neg hi']
      rfl) hb₀
  refine ⟨B₁, x', h1, h2, h3, h4, fun b hb => ⟨x b, ?_, fun a j => ?_, h5 b hb⟩⟩
  · have := hx b (h3 hb)
    rwa [hq, ← hp0] at this
  · rw [hper, hPx b (h3 hb)]
    rfl

end Periods

end GlobalTheory.HolChartLift

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up in

theorem GlobalTheory.HolChartLift.exists_hol_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∀ (k : U.Comp) (x₀ : (U.X k).dom) (t₀ : Ix Dw → (CAt σ)ˣ), FrBor t₀ (U.un k x₀) (y b₀) → ∃ (B₁ : Set (Fin m → ℂ)) (z : (Fin m → ℂ) → V (nd (U.X k))), IsOpen B₁ ∧ b₀ ∈ B₁ ∧ B₁ ⊆ B ∧ DifferentiableOn ℂ z B₁ ∧ z b₀ = 0 ∧ ∀ b ∈ B₁, ∃ (hb : cpt (U.X k) x₀.1 (z b) ∈ (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k ⟨_, hb⟩) (y b) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU A _ _ yA m B φ y hB hφ hy b₀ hb₀ k x₀ t₀ ht₀
  obtain ⟨hr, hty, -, hfib, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  have hmove : ∀ (x x' : (U.X k).dom), ∀ γ ∈ (U.X k).Γ, ∀ β ∈ Bor (U.X k).Ψ r, x'.1 = rmul (lact γ x.1) β →
      ∃ t, FrBor t (U.un k x) (U.un k x') := fun x x' γ hγ β hβ h =>
    (hfib k k x x').2 ⟨γ, hγ, β, hβ, by rw [h]⟩
  obtain ⟨B₁, k', P, hB₁, hb₁, hs₁, hP, hyP⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k x₀
  obtain rfl : ik k = k' := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₀.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨B₂, x', hB₂, hb₂, hs₂, hx'd, hx'⟩ := GlobalTheory.HolChartLift.exists_frames_of_holPeriods c σ e _ (U.X k) (ψ k) hσ
    (F.sig _).1 (F.sig _).2 hr (hty k).1 (hty k).2 (hef k)
    (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr (hty k).1 (hty k).2 (hef k)
      x₀.1 x₀.2 P₁ hP₁ hP₁') hB₁ P hP hb₁
  have key : ∀ b ∈ B₂, ∃ (h : x' b ∈ (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k ⟨_, h⟩) (y b) := by
    intro b hb
    obtain ⟨x, hx, hper, β, hβ, hxβ⟩ := hx' b hb
    have hd : x' b ∈ (U.X k).dom := hxβ ▸ OrthogonalFrameDomain.rmul_mem_dom _ hx hβ
    obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k ⟨x, hx⟩
    have hPS : ∀ a, P₀ a = Matrix.mulVec 1 (P b a) := fun a => by
      rw [Matrix.one_mulVec]
      exact funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, -⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ 1 (y b)
      (U.un k ⟨x, hx⟩) (hP.1 b (hs₂ hb)) hP₀' hPS
      (fun j j' h => by
        obtain rfl : j = j' := by
          by_contra hne
          exact h (Matrix.one_apply_ne hne)
        exact ⟨rfl, le_rfl⟩)
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    obtain ⟨t', ht'⟩ := hmove ⟨x, hx⟩ ⟨_, hd⟩ 1 (one_mem _) β hβ (by rw [PairUnfoldPf.lact_one]; exact hxβ)
    exact ⟨hd, _, hmul _ _ _ _ _ (hinv _ _ _ ht') ht⟩
  obtain ⟨hd₀, t₁, ht₁⟩ := key b₀ hb₂
  obtain ⟨γ, hγ, β, hβ, hx₀⟩ := (hfib k k ⟨_, hd₀⟩ x₀).1 ⟨_, hmul _ _ _ _ _ ht₁ (hinv _ _ _ ht₀)⟩
  have hx₀' : x₀.1 = rmul (lact γ (x' b₀)) β := eq_of_heq (Sigma.mk.inj hx₀).2
  have hdom : ∀ b ∈ B₂, rmul (lact γ (x' b)) β ∈ (U.X k).dom := fun b hb =>
    OrthogonalFrameDomain.rmul_mem_dom _ ((PairUnfoldPf.lact_mem_dom_iff _ hγ _).2 (key b hb).1) hβ
  have hdiff : DifferentiableOn ℂ (fun b => rmul (lact γ (x' b)) β) B₂ := by
    refine differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun j => ?_
    exact GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul
      (fun b => (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (x' b) τ) (fun _ => mat β τ) B₂
      (GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul _ (fun b => mat (x' b) τ) B₂
        (fun _ _ => differentiableOn_const _)
        fun p q => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hx'd τ) p) q)
      (fun _ _ => differentiableOn_const _) a j
  obtain ⟨B₃, z, hB₃, hb₃, hs₃, hz, hz₀, hzc⟩ := GlobalTheory.HolChartLift.exists_hol_chart (U.X k) hB₂ _ hdom hdiff hb₂
  rw [← hx₀'] at hzc
  refine ⟨B₃, z, hB₃, hb₃, fun b hb => hs₁ (hs₂ (hs₃ hb)), hz, hz₀, fun b hb => ?_⟩
  obtain ⟨hc, β', hβ', hsplit⟩ := hzc b hb
  obtain ⟨hd, t, ht⟩ := key b (hs₃ hb)
  obtain ⟨s, hs⟩ := hmove ⟨_, hd⟩ ⟨_, hdom b (hs₃ hb)⟩ γ hγ β hβ rfl
  obtain ⟨s', hs'⟩ := hmove ⟨_, hc⟩ ⟨_, hdom b (hs₃ hb)⟩ 1 (one_mem _) β' hβ'
    (by rw [PairUnfoldPf.lact_one]; exact hsplit)
  exact ⟨hc, _, hmul _ _ _ _ _ (hmul _ _ _ _ _ hs' (hinv _ _ _ hs)) ht⟩
