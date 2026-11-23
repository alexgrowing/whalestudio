import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexConjugate ComplexOrder

namespace HermDatum

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
  (A : HermDatum Em Ψ N j)

omit [NumberField Em] [IsCMField Em] in
theorem conj_comp_conj_comp (σ : Em →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
  ext x
  simp

def embEquiv : Ψ ⊕ Ψ ≃ (Em →+* ℂ) :=
  Equiv.ofBijective (Sum.elim A.emb fun τ => (starRingEnd ℂ).comp (A.emb τ)) (by
    constructor
    · rintro (τ | τ) (τ' | τ') h
      · simp only [Sum.elim_inl] at h
        exact congrArg Sum.inl (A.emb_inj h)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        exact absurd ⟨τ, h⟩ ((A.cmType (A.emb τ')).1 ⟨τ', rfl⟩)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        exact absurd ⟨τ', h.symm⟩ ((A.cmType (A.emb τ)).1 ⟨τ, rfl⟩)
      · simp only [Sum.elim_inr] at h
        have h' : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (A.emb τ)) =
            (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (A.emb τ')) := by rw [h]
        rw [conj_comp_conj_comp, conj_comp_conj_comp] at h'
        exact congrArg Sum.inr (A.emb_inj h')
    · intro σ
      by_cases h : ∃ τ, A.emb τ = σ
      · obtain ⟨τ, rfl⟩ := h
        exact ⟨Sum.inl τ, rfl⟩
      · have h2 : ∃ τ, A.emb τ = (starRingEnd ℂ).comp σ := by
          by_contra h'
          exact h ((A.cmType σ).2 h')
        obtain ⟨τ, hτ⟩ := h2
        refine ⟨Sum.inr τ, ?_⟩
        show (starRingEnd ℂ).comp (A.emb τ) = σ
        rw [hτ, conj_comp_conj_comp])

@[simp] theorem embEquiv_inl (τ : Ψ) : A.embEquiv (Sum.inl τ) = A.emb τ := rfl

@[simp] theorem embEquiv_inr (τ : Ψ) : A.embEquiv (Sum.inr τ) = (starRingEnd ℂ).comp (A.emb τ) := rfl

include A in

theorem finrank_eq_two_mul_card_cm : Module.finrank ℚ Em = 2 * Fintype.card Ψ := by
  rw [← NumberField.Embeddings.card Em ℂ, ← Fintype.card_congr A.embEquiv, Fintype.card_sum]
  ring

theorem sum_coord_of_iso (hj : j ≤ N) {P : Matrix (Fin N) (Fin N) ℂ} (τ : Ψ)
    (hP : Pᴴ * A.H.map (A.emb τ) * P = signMat N j) {x y : Fin N → Em}
    (hxy : hermForm Em A.H x y = 0) :
    ∑ a, conj ((P⁻¹ *ᵥ fun b => A.emb τ (x b)) a) * (P⁻¹ *ᵥ fun b => A.emb τ (y b)) a =
      2 * ∑ c : Fin (N - j), conj ((P⁻¹ *ᵥ fun b => A.emb τ (x b)) (tailIdx hj c)) *
        (P⁻¹ *ᵥ fun b => A.emb τ (y b)) (tailIdx hj c) := by
  set X := P⁻¹ *ᵥ fun b => A.emb τ (x b) with hXdef
  set Y := P⁻¹ *ᵥ fun b => A.emb τ (y b) with hYdef
  have hdet : IsUnit P.det := by
    have h1 := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul] at h1
    have hS : (signMat N j).det ≠ 0 := by
      rw [signMat, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h1
    exact hS h1.symm
  have hx : (fun b => A.emb τ (x b)) = P *ᵥ X := by
    rw [hXdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hy : (fun b => A.emb τ (y b)) = P *ᵥ Y := by
    rw [hYdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hτ0 : A.emb τ (hermForm Em A.H x y) = star (fun b => A.emb τ (x b)) ⬝ᵥ
      (A.H.map (A.emb τ) *ᵥ fun b => A.emb τ (y b)) := by
    simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, map_sum, map_mul]
  have hτ : A.emb τ (hermForm Em A.H x y) = star X ⬝ᵥ (signMat N j *ᵥ Y) := by
    rw [hτ0, hx, hy, ← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star X) Pᴴ, Matrix.star_mulVec]
  have hτ' : ∑ a, conj (X a) * ((if (a : ℕ) < j then (1 : ℂ) else -1) * Y a) = 0 := by
    have h0 := hτ.symm
    rw [hxy, map_zero] at h0
    simpa [signMat, dotProduct, Matrix.mulVec_diagonal] using h0
  have hsplit : ∑ a, conj (X a) * Y a =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => ¬ (a : ℕ) < j), 2 * (conj (X a) * Y a) := by
    rw [Finset.sum_filter]
    have : ∑ a, conj (X a) * Y a =
        ∑ a, conj (X a) * Y a - ∑ a, conj (X a) * ((if (a : ℕ) < j then (1 : ℂ) else -1) * Y a) := by
      rw [hτ', sub_zero]
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [hsplit, Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun c _ => tailIdx hj c) ?_ ?_ ?_ ?_
  · intro c _
    simp [tailIdx]
  · intro c₁ _ c₂ _ h
    simp only [tailIdx, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha
    exact ⟨⟨a - j, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [tailIdx]; omega)⟩
  · intro c _
    rfl

theorem hodge_term_of_iso (hj : j ≤ N) {P : Matrix (Fin N) (Fin N) ℂ} (τ : Ψ)
    (hP : Pᴴ * A.H.map (A.emb τ) * P = signMat N j) {x y : Fin N → Em}
    (hxy : hermForm Em A.H x y = 0) :
    2 * ‖A.emb τ A.ξ‖ *
        (∑ a, conj ((P⁻¹ *ᵥ fun b => A.emb τ (x b)) a) * (P⁻¹ *ᵥ fun b => A.emb τ (y b)) a).re =
      2 * (∑ c, conj (A.lieComp hj P τ x c) * A.lieComp hj P τ y c).re := by
  rw [A.sum_coord_of_iso hj τ hP hxy]
  have hr : (Real.sqrt (2 * ‖A.emb τ A.ξ‖) : ℂ) * (Real.sqrt (2 * ‖A.emb τ A.ξ‖) : ℂ) =
      ((2 * ‖A.emb τ A.ξ‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hs : ∑ c, conj (A.lieComp hj P τ x c) * A.lieComp hj P τ y c =
      ((2 * ‖A.emb τ A.ξ‖ : ℝ) : ℂ) * ∑ c : Fin (N - j),
        conj ((P⁻¹ *ᵥ fun b => A.emb τ (x b)) (tailIdx hj c)) *
          (P⁻¹ *ᵥ fun b => A.emb τ (y b)) (tailIdx hj c) := by
    rw [Finset.mul_sum, ← hr]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [lieComp, map_mul, Complex.conj_ofReal]
    ring
  rw [hs, Complex.re_ofReal_mul]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  ring

theorem lieComp_smul (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (ω : 𝓞 Em)
    (v : Fin N → Em) (c : Fin (N - j)) :
    A.lieComp hj P τ (ω • v) c = A.emb τ (ω : Em) * A.lieComp hj P τ v c := by
  have h : (fun a => A.emb τ ((ω • v) a)) = A.emb τ (ω : Em) • fun a => A.emb τ (v a) := by
    ext a
    simp [Algebra.smul_def]
  unfold lieComp
  rw [h, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem gramLie_eq_conjTranspose_mul (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) {ρ : ℕ}
    (v : Fin ρ → Fin N → Em) :
    A.gramLie hj P τ v = (Matrix.of fun c a => A.lieComp hj P τ (v a) c)ᴴ *
      Matrix.of fun c a => A.lieComp hj P τ (v a) c := by
  ext a b
  simp [gramLie, Matrix.mul_apply]

theorem det_gramLie_nonneg (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) {ρ : ℕ}
    (v : Fin ρ → Fin N → Em) : 0 ≤ (A.gramLie hj P τ v).det := by
  rw [A.gramLie_eq_conjTranspose_mul hj P τ v]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg

theorem det_gramLie_eq_re (hj : j ≤ N) (P : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) {ρ : ℕ}
    (v : Fin ρ → Fin N → Em) :
    (A.gramLie hj P τ v).det = (((A.gramLie hj P τ v).det.re : ℝ) : ℂ) ∧
      0 ≤ (A.gramLie hj P τ v).det.re := by
  have h := Complex.nonneg_iff.1 (A.det_gramLie_nonneg hj P τ v)
  exact ⟨Complex.ext (by simp) (by simp [← h.2]), h.1⟩

end HermDatum

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

theorem hodgeInner_of_iso {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) {I : Submodule (𝓞 Em) (Fin D.N → Em)}
    (hI : D.herm.IsIso I) {x y : Fin D.N → Em} (hx : x ∈ I) (hy : y ∈ I) :
    D.hodgeInner z x y = ∑ τ, 2 * (∑ c, conj (D.herm.lieComp (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ x c) *
      D.herm.lieComp (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ y c).re := by
  unfold hodgeInner
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact D.herm.hodge_term_of_iso _ τ (D.per_witt z hz τ) (hI x hx y hy)

theorem hodgeInner_add_left (z : (Σ k, ι k) → ℂ) (v v' w : Fin D.N → Em) :
    D.hodgeInner z (v + v') w = D.hodgeInner z v w + D.hodgeInner z v' w := by
  have h : ∀ τ, (fun b => D.herm.emb τ (v b) + D.herm.emb τ (v' b)) =
      (fun b => D.herm.emb τ (v b)) + fun b => D.herm.emb τ (v' b) := by
    intro τ; rfl
  simp only [hodgeInner, Pi.add_apply, map_add, h, Matrix.mulVec_add, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib, Complex.add_re, mul_add]

theorem hodgeInner_add_right (z : (Σ k, ι k) → ℂ) (v w w' : Fin D.N → Em) :
    D.hodgeInner z v (w + w') = D.hodgeInner z v w + D.hodgeInner z v w' := by
  have h : ∀ τ, (fun b => D.herm.emb τ (w b) + D.herm.emb τ (w' b)) =
      (fun b => D.herm.emb τ (w b)) + fun b => D.herm.emb τ (w' b) := by
    intro τ; rfl
  simp only [hodgeInner, Pi.add_apply, map_add, h, Matrix.mulVec_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Complex.add_re]

def hodgeAdd (z : (Σ k, ι k) → ℂ) : (Fin D.N → Em) →+ (Fin D.N → Em) →+ ℝ :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (D.hodgeInner z v) (D.hodgeInner_add_right z v))
    (fun v v' => AddMonoidHom.ext fun w => D.hodgeInner_add_left z v v' w)

@[simp] theorem hodgeAdd_apply (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) :
    D.hodgeAdd z v w = D.hodgeInner z v w := rfl

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
