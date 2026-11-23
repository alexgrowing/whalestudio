import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Extend

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (a b : GL (Fin r) E) (L : Lt E r) : mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) (x b : Frame Ψ r) :
    lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) a) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro i
  rw [differentiable_pi]; intro j
  simp only [lact, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

variable {X : Data E r}

theorem gramE {a : GL (Fin r) E} (ha : IsUn X a) :
    (a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc = X.Gm := by
  ext i j
  have h := ha (Pi.single i 1) (Pi.single j 1)
  simp only [FD.herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, _root_.one_mul] at h
  have hL : ((a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc) i j =
      ∑ c, ∑ d, (a : Matrix (Fin r) (Fin r) E) c i * X.Gm c d * FD.cc ((a : Matrix (Fin r) (Fin r) E) d j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hL, h]
  simp [apply_ite FD.cc]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dmin_lact {a : GL (Fin r) E} (ha : IsUn X a) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact a x) τ i = dmin X.Gm x τ i := by
  have hc : ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((a : Matrix (Fin r) (Fin r) E).map FD.cc).map τ.1 := by
    ext i j
    simp only [Matrix.map_apply]
    exact (IsCMField.complexEmbedding_complexConj E τ.1 _).symm
  have key : ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, gramE ha]
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  unfold dmin
  congr 1
  rw [gram_eq, gram_eq, e1, Matrix.transpose_mul, Matrix.map_mul]
  calc (mat x τ).transpose * ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        (((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ))
      = (mat x τ).transpose * (((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) * (mat x τ).map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lact_mem {a : GL (Fin r) E} (ha : IsUn X a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a x ∈ X.dom := by
  intro τ
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (a.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · rw [dmin_lact ha]
    exact (hx τ).2 i

end GlobalTheory.Dict.Extend

theorem GlobalTheory.Dict.exists_form_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  intro E _ _ _ r X Δ 𝓛 mu la Jx _ L Q hun hmu hcoc hL hsep hst hQ
  let F : Lt E r → Frame X.Ψ r → ℂ := fun L' x =>
    if h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L' then
      (mu h.choose.2 (L h.choose.1))⁻¹ * Q h.choose.1 (lact h.choose.2⁻¹ x) else 0
  have key : ∀ k, ∀ a ∈ Δ, ∀ x ∈ X.dom,
      F (mapL a (L k)) x = (mu a (L k))⁻¹ * Q k (lact a⁻¹ x) := by
    intro k a ha x hx
    have h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = mapL a (L k) := ⟨(k, a), ha, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    generalize h.choose = p at h1 h2
    obtain ⟨k', b⟩ := p
    dsimp only at h1 h2 ⊢
    have hs : a⁻¹ * b ∈ Δ := Δ.mul_mem (Δ.inv_mem ha) h1
    have h3 : mapL (a⁻¹ * b) (L k') = L k := by
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
    obtain rfl := hsep k' k _ hs h3
    have h4 : mu b (L k') = mu a (L k') := by
      have := hcoc a ha _ hs _ (hL k')
      rwa [mul_inv_cancel_left, h3, hst _ _ hs h3, _root_.mul_one] at this
    have h5 := (hQ k').inv _ hs h3 _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx)
    rw [Extend.lact_lact, mul_inv_cancel_right] at h5
    rw [h4, h5]
  have zero : ∀ L', (¬ ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L') → ∀ x, F L' x = 0 :=
    fun L' h x => by simp only [F, dif_neg h]
  choose C hC using fun k => (hQ k).bdd
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine ⟨F, ⟨fun L' _ => ?_, fun L' _ x hx b hb => ?_, fun g hg L' hL' x hx => ?_,
    max B 0, fun L' _ x hx => ?_⟩, fun k x hx => ?_⟩
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      refine DifferentiableOn.congr ?_ (key k a ha)
      exact ((hQ k).hol.comp (Extend.differentiable_lact a⁻¹).differentiableOn
        fun x hx => Extend.lact_mem (hun _ (Δ.inv_mem ha)) hx).const_mul _
    · exact (differentiableOn_const 0).congr fun x _ => zero L' h x
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨h1, -⟩ := h.choose_spec
      simp only [F, dif_pos h]
      rw [Extend.lact_rmul, (hQ _).bor _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx) b hb]
      ring
    · rw [zero L' h, zero L' h, mul_zero]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      rw [← Extend.mapL_mul, key k _ (Δ.mul_mem hg ha) _ (Extend.lact_mem (hun g hg) hx), key k a ha x hx,
        hcoc g hg a ha _ (hL k), Extend.lact_lact, _root_.mul_inv_rev g a, inv_mul_cancel_right, mul_inv,
        _root_.mul_assoc]
    · rw [zero L' h, mul_zero]
      refine zero _ ?_ _
      rintro ⟨⟨k, a⟩, ha, h2⟩
      refine h ⟨(k, g⁻¹ * a), Δ.mul_mem (Δ.inv_mem hg) ha, ?_⟩
      dsimp only at h2 ⊢
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      have hu := hun _ (Δ.inv_mem ha)
      have h1 := hC k _ (Extend.lact_mem hu hx)
      refine le_trans (le_of_eq ?_) (h1.trans ((hB ⟨k, rfl⟩).trans (le_max_left _ _)))
      simp only [Data.pnorm, Extend.dmin_lact hu]
      rw [key k a ha x hx, norm_mul, norm_inv, (hmu a ha _ (hL k)).2, inv_one, _root_.one_mul]
    · simp only [Data.pnorm]
      rw [zero L' h, norm_zero, zero_mul]
      exact le_max_right _ _
  · have h := key k 1 Δ.one_mem x hx
    rw [hst k 1 Δ.one_mem (Extend.mapL_one _), Extend.mapL_one, inv_one, inv_one, _root_.one_mul,
      Extend.lact_one] at h
    exact h
