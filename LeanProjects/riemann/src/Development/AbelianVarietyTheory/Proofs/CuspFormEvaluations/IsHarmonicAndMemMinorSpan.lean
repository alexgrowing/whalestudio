import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsHarmonicProdOfDisjointColumns
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSymplecticCoordinatesAdapted

open NumberField Matrix Complex
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {g : ℕ}

theorem eq_zero_of_sum_type {A B : X.Ψ → ℂ}
    (h : ∀ α : 𝓞 E, ∑ τ : X.Ψ, (τ.1 α * A τ + conj (τ.1 α) * B τ) = 0) (τ : X.Ψ) :
    A τ = 0 ∧ B τ = 0 := by
  let e : X.Ψ ⊕ X.Ψ → (E →+* ℂ) := Sum.elim (·.1) fun τ => ComplexEmbedding.conjugate τ.1
  have he : Function.Injective e := by
    rintro (σ | σ) (ρ | ρ) h
    · exact congrArg _ (Subtype.ext h)
    · have h' : σ.1 = ComplexEmbedding.conjugate ρ.1 := h
      exact absurd (h' ▸ σ.2) ((X.cmType _).1 ρ.2)
    · have h' : ρ.1 = ComplexEmbedding.conjugate σ.1 := h.symm
      exact absurd (h' ▸ ρ.2) ((X.cmType _).1 σ.2)
    · exact congrArg _ (Subtype.ext ((ComplexEmbedding.involutive_conjugate E).injective h))
  have hinj : Function.Injective
      (fun i => (((e i).comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)) := fun i j hij =>
    he (IsFractionRing.ringHom_ext (A := 𝓞 E) fun s => DFunLike.congr_fun hij s)
  have hli := Fintype.linearIndependent_iff.1 ((linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hinj)
    (Sum.elim A B) (by
      funext s
      simpa [e, mul_comm, Finset.sum_add_distrib] using h s)
  exact ⟨hli (.inl τ), hli (.inr τ)⟩

theorem nonempty_type : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.1 (mt (X.cmType τ).2 h)⟩⟩

theorem conj_emb_herm (τ : E →+* ℂ) (u v : Fin r → E) :
    conj (τ (herm X.Gm u v)) = τ (herm X.Gm v u) := by
  rw [← hermC_emb, ← hermC_emb, hermC_conj τ X.Gm_herm]

theorem herm_eq_zero_symm {u v : Fin r → E} (h : herm X.Gm u v = 0) : herm X.Gm v u = 0 := by
  obtain ⟨τ⟩ := nonempty_type X
  have := conj_emb_herm X τ.1 u v
  rw [h, map_zero, map_zero] at this
  exact (map_eq_zero τ.1).1 this.symm

theorem EF_smul_eq_sum (α : E) (v w : Fin r → E) :
    ((EF X (α • v) w : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 α * (I / 2 * X.c τ * conj (τ.1 (herm X.Gm w v))) +
      conj (τ.1 α) * -(I / 2 * X.c τ * τ.1 (herm X.Gm w v))) := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (EF_eq_sum X (α • v) w)
  simp only [ofReal_ratCast, ofReal_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 : Data.emb τ.1 (α • v) = τ.1 α • Data.emb τ.1 v := by
    funext a; simp [Data.emb]
  rw [h1, hermC_smul_left, hermC_emb, ← conj_emb_herm X τ.1 w v]
  generalize τ.1 (herm X.Gm w v) = z
  generalize τ.1 α = y
  apply Complex.ext <;> simp <;> ring

theorem EF_eq_zero_of_herm {v w : Fin r → E} (h : herm X.Gm w v = 0) : EF X v w = 0 := by
  rw [EF_def, herm_eq_zero_symm X h, mul_zero, map_zero]

theorem herm_eq_zero_of_EF {v w : Fin r → E} (h : ∀ α : 𝓞 E, EF X ((α : E) • v) w = 0) :
    herm X.Gm w v = 0 := by
  obtain ⟨τ⟩ := nonempty_type X
  have h1 := (eq_zero_of_sum_type X (fun α => by
    rw [← EF_smul_eq_sum X (α : E) v w, h, Rat.cast_zero]) τ).2
  simpa [(c_pos X τ).ne'] using h1

open Classical in

def perLt (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) : X.Ψ × Fin r → ℂ := fun p =>
  if p.1 = τ ∧ (p.2 : ℕ) < X.p0 then per X x v p else 0

open Classical in

def perGe (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) : X.Ψ × Fin r → ℂ := fun p =>
  if p.1 = τ ∧ X.p0 ≤ (p.2 : ℕ) then per X x v p else 0

theorem mul_per_smul_eq_sum (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (α : E) (v : Fin r → E)
    (p : X.Ψ × Fin r) : s p.1 * per X x (α • v) p =
      ∑ τ, s τ * (τ.1 α * perGe X x v τ p + conj (τ.1 α) * perLt X x v τ p) := by
  rw [Finset.sum_eq_single p.1, per_smul]
  · rcases lt_or_ge (p.2 : ℕ) X.p0 with h | h
    · simp [perGe, perLt, rowType, h, not_le.2 h]
    · simp [perGe, perLt, rowType, h, not_lt.2 h]
  · intro τ _ hτ
    simp [perGe, perLt, hτ.symm]
  · simp

theorem mulVec_per_smul (idx : Fin g ≃ X.Ψ × Fin r) (M : Matrix (Fin g) (Fin g) ℂ)
    (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (α : E) (v : Fin r → E) (j : Fin g) :
    (M *ᵥ fun i => s (idx i).1 * per X x (α • v) (idx i)) j = ∑ τ, s τ *
      (τ.1 α * (M *ᵥ (perGe X x v τ ∘ idx)) j + conj (τ.1 α) * (M *ᵥ (perLt X x v τ ∘ idx)) j) := by
  simp only [mul_per_smul_eq_sum, mulVec, dotProduct, Finset.mul_sum, Function.comp_apply,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem emb_neg_kappa (τ : X.Ψ) : τ.1 (-X.κ0) = I * X.c τ := by
  rw [show -X.κ0 = 2 * -(X.κ0 / 2) by ring, map_mul, emb_neg_half, map_ofNat]
  push_cast; ring

section Flow

variable (ξ : Fin r → E)

theorem flowMat_mulVec_eq (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) : X.flowMat ξ τ s *ᵥ v =
    v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext a
  simp only [Data.flowMat, mulVec, dotProduct, of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, Data.emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem col_flow_eq (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) :
    FD.col (mat (X.flow ξ s x) τ) a = FD.col (mat x τ) a +
      (-(I * X.c τ * s τ) * hermC τ.1 X.Gm (FD.col (mat x τ) a) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := flowMat_mulVec_eq X ξ τ (s τ) _

theorem flow_rmul (s : X.Ψ → ℂ) (x b : Frame X.Ψ r) :
    X.flow ξ s (rmul x b) = rmul (X.flow ξ s x) b := by
  funext τ
  exact (Matrix.mul_assoc (X.flowMat ξ τ (s τ)) (mat x τ) (mat b τ)).symm

variable {X ξ} (hξ : herm X.Gm ξ ξ = 0)
include hξ

theorem flowMat_neg_mul (τ : X.Ψ) (s : ℂ) : X.flowMat ξ τ (-s) * X.flowMat ξ τ s = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, flowMat_mulVec_eq, flowMat_mulVec_eq,
    hermC_add_left, hermC_smul_left, hermC_emb, hξ, one_mulVec]
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero]
  ring

theorem inv_flow_mulVec (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    (mat (X.flow ξ s x) τ)⁻¹ *ᵥ v = (mat x τ)⁻¹ *ᵥ v +
      (I * X.c τ * s τ * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) • ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 ξ) := by
  change (X.flowMat ξ τ (s τ) * mat x τ)⁻¹ *ᵥ v = _
  rw [Matrix.mul_inv_rev, inv_eq_left_inv (flowMat_neg_mul hξ τ _), ← mulVec_mulVec,
    flowMat_mulVec_eq, mulVec_add, mulVec_smul, mul_neg, neg_neg]

theorem per_flow (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (v : Fin r → E) (p : X.Ψ × Fin r) :
    per X (X.flow ξ s x) v p =
      per X x v p + s p.1 * per X x ((-X.κ0 * herm X.Gm v ξ) • ξ) p := by
  have hκ := emb_neg_kappa X p.1
  rw [per_smul]
  simp only [per, rowType]
  split_ifs
  · rw [col_flow_eq, hermC_add_left, hermC_smul_left, ComplexEmbedding.conjugate_coe_eq,
      map_mul p.1.1, hκ, hermC_emb, map_mul, conj_emb_herm, map_mul, conj_I, conj_ofReal]
    ring
  · rw [inv_flow_mulVec hξ, map_mul, hκ, hermC_emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem per_flow_of_orth (s : X.Ψ → ℂ) (x : Frame X.Ψ r) {v : Fin r → E}
    (hv : herm X.Gm v ξ = 0) : per X (X.flow ξ s x) v = per X x v := by
  funext p
  simp [per_flow hξ, hv]

theorem coper_flow_of_orth (s : X.Ψ → ℂ) (x : Frame X.Ψ r) {v : Fin r → E}
    (hv : herm X.Gm v ξ = 0) : coper X (X.flow ξ s x) v = coper X x v := by
  funext p
  simp only [coper]
  rw [col_flow_eq, hermC_add_left, hermC_smul_left, inv_flow_mulVec hξ, hermC_emb, hermC_emb, hv,
    herm_eq_zero_symm X hv]
  simp

end Flow

section Modes

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (ξ : Fin r → E)

def IsAdapted (S : Finset (Fin g)) : Prop :=
  ∀ v : X.Λ, (v : Fin r → E) ∈ Submodule.span E {ξ} ↔
    v ∈ Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g)))

def cuspLin (τ : X.Ψ) (j : Fin g) : ℂ := τ.1 (herm X.Gm (bas (Pi.single (Sum.inr j) 1)) ξ)

def cuspMat (τ : X.Ψ) : Matrix (Fin g) (Fin g) ℝ :=
  Matrix.of fun j k => X.c τ ^ 2 * (cuspLin X bas ξ τ j * conj (cuspLin X bas ξ τ k)).re

def cuspNu (u : Fin g → ℝ) (τ : X.Ψ) : ℝ :=
  X.c τ ^ 2 / 4 * ‖∑ j, (u j : ℂ) * cuspLin X bas ξ τ j‖ ^ 2

theorem cuspNu_nonneg (u : Fin g → ℝ) (τ : X.Ψ) : 0 ≤ cuspNu X bas ξ u τ := by
  unfold cuspNu; positivity

theorem cuspNu_eq_zero_iff (u : Fin g → ℝ) (τ : X.Ψ) :
    cuspNu X bas ξ u τ = 0 ↔ ∑ j, (u j : ℂ) * cuspLin X bas ξ τ j = 0 := by
  simp [cuspNu, (c_pos X τ).ne']

theorem dot_cuspMat (u : Fin g → ℝ) (τ : X.Ψ) :
    u ⬝ᵥ cuspMat X bas ξ τ *ᵥ u = 4 * cuspNu X bas ξ u τ := by
  have h : ‖∑ j, (u j : ℂ) * cuspLin X bas ξ τ j‖ ^ 2 = ((∑ j, (u j : ℂ) * cuspLin X bas ξ τ j) *
      conj (∑ j, (u j : ℂ) * cuspLin X bas ξ τ j)).re := by
    rw [mul_conj, normSq_eq_norm_sq, ofReal_re]
  rw [cuspNu, h, map_sum, Finset.sum_mul_sum, re_sum, ← mul_assoc, Finset.mul_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [re_sum, mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cuspMat]
  ring

theorem dot_sum_cuspMat (s : X.Ψ → ℂ) (u : Fin g → ℝ) :
    (fun i => (u i : ℂ)) ⬝ᵥ (∑ τ, s τ • (cuspMat X bas ξ τ).map fun t : ℝ => (t : ℂ)) *ᵥ
      (fun i => (u i : ℂ)) = 4 * ∑ τ, (cuspNu X bas ξ u τ : ℂ) * s τ := by
  rw [sum_mulVec, dotProduct_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := congrArg (fun t : ℝ => (t : ℂ)) (dot_cuspMat X bas ξ u τ)
  simp only [dotProduct, mulVec, ofReal_sum, ofReal_mul, ofReal_ofNat] at h
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, ← h, mul_comm]
  rfl

variable {X bas ξ}

theorem coe_int_smul (hξ : ξ ∈ X.Λ) (α : 𝓞 E) :
    ((α • (⟨ξ, hξ⟩ : X.Λ) : X.Λ) : Fin r → E) = (α : E) • ξ := rfl

variable (hs : IsSympl X bas)
include hs

theorem EF_bas_inr (v : X.Λ) (j : Fin g) :
    EF X v (bas (Pi.single (Sum.inr j) 1)) = -(bas.symm v (Sum.inl j) : ℤ) := by
  conv_lhs => rw [← bas.apply_symm_apply v]
  rw [hs]
  simp [omegaStd, Pi.single_apply]

theorem EF_bas_inl (v : X.Λ) (j : Fin g) :
    EF X v (bas (Pi.single (Sum.inl j) 1)) = (bas.symm v (Sum.inr j) : ℤ) := by
  conv_lhs => rw [← bas.apply_symm_apply v]
  rw [hs]
  simp [omegaStd, Pi.single_apply]

variable {S : Finset (Fin g)} (hA : IsAdapted X bas ξ S)
include hA

omit hs in

theorem IsAdapted.symm_apply_eq_zero {v : X.Λ} (hv : (v : Fin r → E) ∈ Submodule.span E {ξ})
    {t : Fin g ⊕ Fin g} (ht : ∀ k ∈ S, t ≠ Sum.inl k) : bas.symm v t = 0 := by
  have h := (hA v).1 hv
  clear hv
  induction h using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨k, hk, rfl⟩ := hv
    rw [LinearEquiv.symm_apply_apply, Pi.single_eq_of_ne (ht k hk)]
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, Pi.add_apply, hu, hv, add_zero]
  | smul c u _ hu => rw [map_smul, Pi.smul_apply, hu, smul_zero]

omit hs in

theorem IsAdapted.symm_smul_eq_zero (hξ : ξ ∈ X.Λ) (α : 𝓞 E) {t : Fin g ⊕ Fin g}
    (ht : ∀ k ∈ S, t ≠ Sum.inl k) : bas.symm (α • ⟨ξ, hξ⟩) t = 0 :=
  hA.symm_apply_eq_zero (Submodule.mem_span_singleton.2 ⟨α, rfl⟩) ht

theorem IsAdapted.herm_inl (hξ : ξ ∈ X.Λ) (j : Fin g) :
    herm X.Gm (bas (Pi.single (Sum.inl j) 1)) ξ = 0 :=
  herm_eq_zero_of_EF X fun α => by
    rw [← coe_int_smul hξ, EF_bas_inl hs, hA.symm_smul_eq_zero hξ α (by simp), Int.cast_zero]

theorem IsAdapted.cuspLin_ne_zero (hξ : X.IsIso ξ) (τ : X.Ψ) : cuspLin X bas ξ τ ≠ 0 := by
  intro h
  have h1 : bas.symm ⟨ξ, hξ.1⟩ = 0 := by
    funext t
    rcases t with j | j
    · have h2 := EF_bas_inr hs ⟨ξ, hξ.1⟩ j
      rw [EF_eq_zero_of_herm X ((map_eq_zero τ.1).1 (congrFun h j))] at h2
      simpa using h2
    · simpa using hA.symm_smul_eq_zero hξ.1 1 (t := Sum.inr j) (by simp)
  exact hξ.2.2 (congrArg Subtype.val (bas.symm.map_eq_zero_iff.1 h1))

variable (idx : Fin g ≃ X.Ψ × Fin r)

theorem IsAdapted.hMat_flow (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    hMat X bas idx (X.flow ξ s x) = hMat X bas idx x := by
  simp only [hMat, perMat, per_flow_of_orth hξ.2.1 s x (hA.herm_inl hs hξ.1 _)]

theorem IsAdapted.splitMat_flow (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    splitMat X bas idx (X.flow ξ s x) = splitMat X bas idx x := by
  simp only [splitMat, hA.hMat_flow hs idx hξ, coMat,
    coper_flow_of_orth hξ.2.1 s x (hA.herm_inl hs hξ.1 _)]

theorem IsAdapted.hMat_mulVec_part (hξ : ξ ∈ X.Λ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (j : Fin g) :
    (hMat X bas idx x *ᵥ (perGe X x ξ τ ∘ idx)) j = -(I / 2 * X.c τ * conj (cuspLin X bas ξ τ j)) ∧
    (hMat X bas idx x *ᵥ (perLt X x ξ τ ∘ idx)) j = I / 2 * X.c τ * cuspLin X bas ξ τ j := by
  have h := eq_zero_of_sum_type X
    (A := fun τ => (hMat X bas idx x *ᵥ (perGe X x ξ τ ∘ idx)) j +
      I / 2 * X.c τ * conj (cuspLin X bas ξ τ j))
    (B := fun τ => (hMat X bas idx x *ᵥ (perLt X x ξ τ ∘ idx)) j +
      -(I / 2 * X.c τ * cuspLin X bas ξ τ j)) (fun α => by
      have h1 := mulVec_per_smul X idx (hMat X bas idx x) x 1 α ξ j
      have h2 := congrFun (hMat_mulVec_per X bas idx (isUnit_det_perMat idx hs hx)
        (bas.symm (α • ⟨ξ, hξ⟩))) j
      have h3 := EF_smul_eq_sum X α ξ (bas (Pi.single (Sum.inr j) 1))
      have h4 := EF_bas_inr hs (α • ⟨ξ, hξ⟩) j
      simp only [Pi.one_apply, one_mul] at h1
      simp only [hA.symm_smul_eq_zero hξ α (t := Sum.inr _) (by simp),
        LinearEquiv.apply_symm_apply, Pi.add_apply, mulVec, dotProduct, Int.cast_zero, mul_zero,
        Finset.sum_const_zero, add_zero] at h2
      rw [coe_int_smul] at h2 h4
      rw [h4] at h3
      push_cast at h3
      simp only [mul_add, add_add_add_comm (_ * _) (_ * (I / 2 * _ * _)), Finset.sum_add_distrib,
        cuspLin] at h1 h3 ⊢
      rw [← h1, ← h3, add_neg_eq_zero]
      exact h2) τ
  exact ⟨eq_neg_of_add_eq_zero_left h.1, add_neg_eq_zero.1 h.2⟩

theorem IsAdapted.tauMat_flow (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    tauMat X bas idx (X.flow ξ s x) =
      tauMat X bas idx x + ∑ τ, s τ • (cuspMat X bas ξ τ).map fun t : ℝ => (t : ℂ) := by
  ext j k
  have h := mulVec_per_smul X idx (hMat X bas idx x) x s
    (-X.κ0 * herm X.Gm (bas (Pi.single (Sum.inr k) 1)) ξ) ξ j
  rw [tauMat, hA.hMat_flow hs idx hξ, Matrix.add_apply, tauMat, Matrix.sum_apply]
  simp only [mul_apply, perMat_apply, per_flow hξ.2.1, mul_add, Finset.sum_add_distrib]
  congr 1
  refine h.trans (Finset.sum_congr rfl fun τ _ => ?_)
  rw [(hA.hMat_mulVec_part hs idx hξ.1 hx τ j).1, (hA.hMat_mulVec_part hs idx hξ.1 hx τ j).2,
    map_mul τ.1, emb_neg_kappa, Matrix.smul_apply, smul_eq_mul, map_apply, cuspMat, of_apply, ← cuspLin]
  congr 1
  generalize cuspLin X bas ξ τ j = y
  generalize cuspLin X bas ξ τ k = z
  apply Complex.ext <;> simp [sq] <;> ring

end Modes

section Complement

theorem exists_block (p : ℕ) (w l : Fin r → ℂ) (h : ∑ a, w a * l a = 0) {a₀ c₀ : Fin r}
    (ha : (a₀ : ℕ) < p) (hc : p ≤ (c₀ : ℕ)) (hl : l a₀ ≠ 0) (hw : w c₀ ≠ 0) :
    ∃ K : Fin r → Fin r → ℂ,
      (∀ a : Fin r, ∑ c : Fin r, (if p ≤ (c : ℕ) then K a c * w c else 0) = w a) ∧
      ∀ c : Fin r, ∑ a : Fin r, (if (a : ℕ) < p then K a c * l a else 0) = -l c := by
  obtain ⟨d, hd⟩ : ∃ d : Fin r → ℂ, ∑ c : Fin r, (if p ≤ (c : ℕ) then d c * w c else 0) = 1 :=
    ⟨Pi.single c₀ (w c₀)⁻¹, by rw [Finset.sum_eq_single c₀] <;> simp +contextual [hc, hw]⟩
  obtain ⟨e, he⟩ : ∃ e : Fin r → ℂ, ∑ a : Fin r, (if (a : ℕ) < p then e a * l a else 0) = 1 :=
    ⟨Pi.single a₀ (l a₀)⁻¹, by rw [Finset.sum_eq_single a₀] <;> simp +contextual [ha, hl]⟩
  obtain ⟨t, ht⟩ : ∃ t, t = ∑ a : Fin r, if (a : ℕ) < p then w a * l a else 0 := ⟨_, rfl⟩
  have ht' : ∑ c : Fin r, (if p ≤ (c : ℕ) then l c * w c else 0) = -t := by
    rw [eq_neg_iff_add_eq_zero, ht, ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun a _ => ?_).trans h
    rcases lt_or_ge (a : ℕ) p with h | h
    · simp [h, not_le.2 h]
    · simp [h, not_lt.2 h, mul_comm]
  refine ⟨fun a c => w a * d c - e a * l c - t * e a * d c, fun a => ?_, fun c => ?_⟩
  · calc _ = (w a - t * e a) * ∑ c : Fin r, (if p ≤ (c : ℕ) then d c * w c else 0) -
          e a * ∑ c : Fin r, (if p ≤ (c : ℕ) then l c * w c else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          split_ifs <;> ring
      _ = w a := by rw [hd, ht']; ring
  · calc _ = d c * ∑ a : Fin r, (if (a : ℕ) < p then w a * l a else 0) -
          (l c + t * d c) * ∑ a : Fin r, (if (a : ℕ) < p then e a * l a else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          split_ifs <;> ring
      _ = -l c := by rw [he, ← ht]; ring

variable {X} {ξ : Fin r → E}

theorem exists_unip_coper_eq_zero (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r}
    (hx : ∀ τ, (mat x τ).det ≠ 0) (h₁ : ∀ τ, perLt X x ξ τ ≠ 0) (h₂ : ∀ τ, perGe X x ξ τ ≠ 0) :
    ∃ K, coper X (rmul x (unip X K)) ξ = 0 := by
  have h (τ : X.Ψ) : ∃ K : Fin r → Fin r → ℂ,
      (∀ a : Fin r, ∑ c : Fin r, (if X.p0 ≤ (c : ℕ) then
        K a c * ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 ξ) c else 0) = ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 ξ) a) ∧
      ∀ c : Fin r, ∑ a : Fin r, (if (a : ℕ) < X.p0 then
        K a c * hermC τ.1 X.Gm (FD.col (mat x τ) a) (Data.emb τ.1 ξ) else 0) =
        -hermC τ.1 X.Gm (FD.col (mat x τ) c) (Data.emb τ.1 ξ) := by
    obtain ⟨⟨σ, a⟩, ha⟩ := Function.ne_iff.1 (h₁ τ)
    obtain ⟨⟨ρ, c⟩, hc⟩ := Function.ne_iff.1 (h₂ τ)
    simp only [perLt, perGe, Pi.zero_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at ha hc
    obtain ⟨⟨rfl, ha⟩, ha'⟩ := ha
    obtain ⟨⟨rfl, hc⟩, hc'⟩ := hc
    rw [per_of_lt X _ _ _ ha] at ha'
    rw [per_of_le X _ _ _ hc] at hc'
    refine exists_block X.p0 _ _ ?_ ha hc ha' hc'
    rw [← hermC_eq_sum_col _ _ (hx _), hermC_emb, hξ, map_zero]
  choose K hK hK' using h
  refine ⟨K, funext fun ⟨τ, a⟩ => ?_⟩
  have hm : mat (rmul x (unip X K)) τ = mat x τ * mat (unip X K) τ := rfl
  rcases lt_or_ge (a : ℕ) X.p0 with ha | ha
  · rw [coper_of_lt X _ _ _ ha, hm, Matrix.mul_inv_rev, inv_eq_left_inv (mat_unip_neg_mul X K τ),
      ← mulVec_mulVec]
    refine mul_eq_zero_of_right _ ?_
    have h := hK τ a
    generalize (mat x τ)⁻¹ *ᵥ Data.emb τ.1 ξ = w at h
    have h1 : w a = ∑ c, if a = c then w c else 0 := by simp
    have h2 := sub_eq_zero.2 (h1.symm.trans h.symm)
    rw [← Finset.sum_sub_distrib] at h2
    refine (Finset.sum_congr rfl fun c _ => ?_).trans h2
    simp only [mat, of_apply, unip, ha, true_and, Pi.neg_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · rw [coper_of_le X _ _ _ ha, hm, PerMove.hermC_col_mul, Pi.zero_apply, neg_eq_zero]
    refine mul_eq_zero_of_right _ ?_
    have h := hK' τ a
    have h1 : hermC τ.1 X.Gm (FD.col (mat x τ) a) (Data.emb τ.1 ξ) = ∑ c, if c = a then
      hermC τ.1 X.Gm (FD.col (mat x τ) c) (Data.emb τ.1 ξ) else 0 := by simp
    have h2 := add_eq_zero_iff_eq_neg.2 (h.trans (congrArg Neg.neg h1))
    rw [← Finset.sum_add_distrib] at h2
    refine (Finset.sum_congr rfl fun c _ => ?_).trans h2
    simp only [mat, of_apply, unip, ha, and_true, Fin.ext_iff]
    split_ifs <;> first | omega | simp

variable {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {S : Finset (Fin g)}
  (hA : IsAdapted X bas ξ S) (idx : Fin g ≃ X.Ψ × Fin r)
include hs hA

include idx in

theorem IsAdapted.part_ne_zero (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    perLt X x ξ τ ≠ 0 ∧ perGe X x ξ τ ≠ 0 := by
  have hc := (c_pos X τ).ne'
  constructor <;> refine fun h => hA.cuspLin_ne_zero hs hξ τ (funext fun j => ?_)
  · simpa [h, hc] using (hA.hMat_mulVec_part hs idx hξ.1 hx τ j).2
  · simpa [h, hc] using (hA.hMat_mulVec_part hs idx hξ.1 hx τ j).1

theorem IsAdapted.splitMat_mulVec_part (hξ : ξ ∈ X.Λ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    (h : coper X y ξ = 0) (τ : X.Ψ) :
    splitMat X bas idx y *ᵥ (perGe X y ξ τ ∘ idx) = 0 ∧
      splitMat X bas idx y *ᵥ (perLt X y ξ τ ∘ idx) = 0 := by
  have key (j) := eq_zero_of_sum_type X
    (A := fun τ => (splitMat X bas idx y *ᵥ (perGe X y ξ τ ∘ idx)) j)
    (B := fun τ => (splitMat X bas idx y *ᵥ (perLt X y ξ τ ∘ idx)) j) (fun α => by
      have h1 := mulVec_per_smul X idx (splitMat X bas idx y) y 1 α ξ j
      have h2 := congrFun (splitMat_mulVec_per idx hs hy
        fun k => bas.symm (α • ⟨ξ, hξ⟩) (Sum.inl k)) j
      have h3 : Sum.elim (fun k => bas.symm (α • ⟨ξ, hξ⟩) (Sum.inl k)) 0 =
          bas.symm (α • ⟨ξ, hξ⟩) := by
        funext t
        rcases t with k | k
        · rfl
        · exact (hA.symm_smul_eq_zero hξ α (by simp)).symm
      rw [h3, LinearEquiv.apply_symm_apply, coe_int_smul, Function.comp_apply, coper_smul, h,
        Pi.zero_apply, mul_zero] at h2
      simp only [Pi.one_apply, one_mul] at h1
      rw [← h1]
      exact h2) τ
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

end Complement

section Expansion

variable {q0 : ℕ} (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
  (idx : Fin g ≃ X.Ψ × Fin r)

def splitTerm {n : ℕ} (a b : Fin n → Fin g → ℝ) (y : Frame X.Ψ r) (m : Fin n → Fin g → ℤ)
    (z : Fin n → Fin g → ℂ) : ℂ :=
  (∏ k, cexp (Real.pi / 2 * (z k ⬝ᵥ splitMat X bas idx y *ᵥ z k))) *
    ∏ k, CanTh.thTerm (tauMat X bas idx y) (a k) (b k) (hMat X bas idx y *ᵥ z k) (m k)

def flowCoeff (n : ℕ) (a b : Fin n → Fin g → ℝ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (y : Frame X.Ψ r) (m : Fin n → Fin g → ℤ) : ℂ :=
  (hMat X bas idx y).det ^ (n / 2) * polyDeriv P (letterDir X hr idx) (splitTerm X bas idx a b y m) 0

theorem differentiable_prod_gauss {n : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) : Differentiable ℂ
    fun z : Fin n → Fin g → ℂ => ∏ k, cexp (Real.pi / 2 * (z k ⬝ᵥ M *ᵥ z k)) :=
  differentiableOn_univ.1 (CanTh.differentiableOn_prod_fun _ fun k _ => by
    simp only [dotProduct, mulVec]
    fun_prop)

theorem differentiable_mulVec_col {n : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (k : Fin n) :
    Differentiable ℂ fun z : Fin n → Fin g → ℂ => M *ᵥ z k :=
  differentiable_pi.2 fun i => by
    simp only [dotProduct, mulVec]
    fun_prop

theorem analyticAt_splitTerm {n : ℕ} (a b : Fin n → Fin g → ℝ) (y : Frame X.Ψ r)
    (m : Fin n → Fin g → ℤ) : AnalyticAt ℂ (splitTerm X bas idx a b y m) 0 :=
  SCV.analyticAt_of_differentiableOn (s := Set.univ)
    ((differentiable_prod_gauss _).differentiableOn.mul
      (CanTh.differentiableOn_prod_fun _ fun k _ =>
        CanTh.differentiableOn_thTerm (T := fun _ => tauMat X bas idx y)
          (fun _ _ => differentiableOn_const _)
          (differentiable_mulVec_col _ k).differentiableOn _ _ _)) Filter.univ_mem

theorem sum_letterDir_xVar {n : ℕ} (y : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (k : Fin n) :
    ∑ i, per X y v (rowOf X hr (τ, .inl i)) • letterDir X hr idx (Harm.xVar τ i k) =
      Pi.single k (perGe X y v τ ∘ idx) := by
  classical
  funext k' j
  obtain ⟨⟨t, ρ⟩, rfl⟩ := ((rowOf X hr).trans idx.symm).surjective j
  by_cases hk : k' = k
  · subst hk
    by_cases ht : t = τ
    · subst ht
      rcases ρ with i | i
      · simp [letterDir, perGe, Pi.single_apply]
      · have := i.isLt
        simp [letterDir, perGe, Pi.single_apply]
        omega
    · simp [letterDir, perGe, Pi.single_apply, ht]
  · simp [letterDir, hk]

theorem sum_letterDir_yVar {n : ℕ} (y : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (k : Fin n) :
    ∑ i, per X y v (rowOf X hr (τ, .inr i)) • letterDir X hr idx (Harm.yVar τ i k) =
      Pi.single k (perLt X y v τ ∘ idx) := by
  classical
  funext k' j
  obtain ⟨⟨t, ρ⟩, rfl⟩ := ((rowOf X hr).trans idx.symm).surjective j
  by_cases hk : k' = k
  · subst hk
    by_cases ht : t = τ
    · subst ht
      rcases ρ with i | i
      · simp [letterDir, perLt, Pi.single_apply]
      · have := i.isLt
        simp [letterDir, perLt, Pi.single_apply]
        omega
    · simp [letterDir, perLt, Pi.single_apply, ht]
  · simp [letterDir, hk]

variable {X bas} (hs : IsSympl X bas)
include hs

theorem splitTerm_add_single {n : ℕ} (a b : Fin n → Fin g → ℝ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    (m : Fin n → Fin g → ℤ) {d : Fin g → ℂ} (hd : splitMat X bas idx y *ᵥ d = 0)
    (hm : ∀ k, ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ)) ⬝ᵥ hMat X bas idx y *ᵥ d = 0)
    (k : Fin n) (z : Fin n → Fin g → ℂ) (t : ℂ) :
    splitTerm X bas idx a b y m (z + t • (Pi.single k d : Fin n → Fin g → ℂ)) =
      splitTerm X bas idx a b y m z := by
  have h (k' : Fin n) : ∃ c : ℂ, (z + t • (Pi.single k d : Fin n → Fin g → ℂ)) k' = z k' + c • d := by
    by_cases hk : k' = k
    · exact ⟨t, by simp [hk]⟩
    · exact ⟨0, by simp [hk]⟩
  unfold splitTerm
  congr 1 <;> refine Finset.prod_congr rfl fun k' _ => ?_ <;> obtain ⟨c, hc⟩ := h k' <;> rw [hc]
  · rw [mulVec_add, mulVec_smul, hd, smul_zero, add_zero, add_dotProduct, smul_dotProduct,
      dotProduct_mulVec d, ← mulVec_transpose, (splitMat_isSymm idx hs hy).eq, hd]
    simp
  · rw [mulVec_add, CanTh.thTerm_add_var, mulVec_smul, dotProduct_smul, hm]
    simp

theorem summable_norm_flowCoeff (n : ℕ) (a b : Fin n → Fin g → ℝ)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    Summable fun m => ‖flowCoeff X hr bas idx n a b P y m‖ := by
  simp only [flowCoeff, norm_mul]
  exact (CanTh.hasSum_polyDeriv_mul_prod_const (τ := fun _ => tauMat X bas idx y)
    (differentiable_prod_gauss _) (differentiable_mulVec_col _)
    (fun _ => CanTh.mem_thetaDomain (tauMat_im_posDef idx hs hy)) a b P _ 0).2.mul_left _

variable {ξ : Fin r → E} {S : Finset (Fin g)} (hA : IsAdapted X bas ξ S)
include hA

theorem IsAdapted.hasSum_flowCoeff (hξ : X.IsIso ξ) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : Harm.IsHarmonic P) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) {s : X.Ψ → ℂ} (hys : X.flow ξ s y ∈ X.dom) :
    HasSum (fun m : Fin n → Fin g → ℤ => flowCoeff X hr bas idx n a b P y m *
        cexp (4 * Real.pi * I * ∑ τ,
          (((∑ k, cuspNu X bas ξ fun i => (m k i : ℝ) + a k i) τ : ℝ) : ℂ) * s τ))
      (thFr X hr bas idx n a b P (X.flow ξ s y)) := by
  have hd := CanTh.mem_thetaDomain (tauMat_im_posDef idx hs hys)
  rw [hA.tauMat_flow hs idx hξ s hy] at hd
  rw [thFr_eq_splitMat idx hs hys hr n a b hP, hA.hMat_flow hs idx hξ, hA.splitMat_flow hs idx hξ,
    hA.tauMat_flow hs idx hξ s hy]
  simp only [Finset.prod_mul_distrib]
  have H := (CanTh.hasSum_polyDeriv_mul_prod_add_matrix (τ := fun _ => tauMat X bas idx y)
    (differentiable_prod_gauss (splitMat X bas idx y))
    (differentiable_mulVec_col (hMat X bas idx y)) (fun _ => hd) a b P (letterDir X hr idx)
    0).mul_left ((hMat X bas idx y).det ^ (n / 2))
  refine (congrArg (HasSum · _) (funext fun m => ?_)).mpr H
  rw [flowCoeff, mul_assoc]
  congr 3
  have h (k) : ((fun i => (m k i : ℂ)) + fun i => (a k i : ℂ)) =
      fun i => (((m k i : ℝ) + a k i : ℝ) : ℂ) := by
    funext i; simp
  simp only [h, dot_sum_cuspMat, Finset.sum_apply, ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.mul_sum]
  ring

theorem IsAdapted.flowCoeff_eq_zero (hξ : X.IsIso ξ) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ} {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ GaussGauge.minorSpan (Fin n) c c') {τ : X.Ψ}
    (hc : (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨ ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) (h : coper X y ξ = 0) {m : Fin n → Fin g → ℤ}
    (hm : (∑ k, cuspNu X bas ξ fun i => (m k i : ℝ) + a k i) τ = 0) :
    flowCoeff X hr bas idx n a b P y m = 0 := by
  rw [Finset.sum_apply, Finset.sum_eq_zero_iff_of_nonneg fun k _ => cuspNu_nonneg X bas ξ _ τ] at hm
  have h1 (k) := (cuspNu_eq_zero_iff X bas ξ _ τ).1 (hm k (Finset.mem_univ _))
  have h2 (k) := congrArg conj (h1 k)
  simp only [map_sum, map_mul, conj_ofReal, map_zero] at h2
  push_cast at h1 h2
  refine mul_eq_zero_of_right _ ?_
  rcases hc with ⟨i, hi, hc⟩ | ⟨i, hi, hc⟩
  · refine GaussGauge.polyDeriv_eq_zero_x_dir hP hi hc
      (v := fun i => per X y ξ (rowOf X hr (τ, .inl i))) (fun h0 => ?_) _
      (analyticAt_splitTerm X bas idx a b y m) fun k z t => ?_
    · refine (hA.part_ne_zero hs idx hξ hy τ).2 ?_
      have h3 := congrFun (sum_letterDir_xVar X hr idx y ξ τ (0 : Fin 1)) 0
      simp only [show ∀ i, per X y ξ (rowOf X hr (τ, .inl i)) = 0 from congrFun h0, zero_smul,
        Finset.sum_const_zero, Pi.single_eq_same] at h3
      exact funext fun p => by simpa using (congrFun h3 (idx.symm p)).symm
    · rw [sum_letterDir_xVar]
      refine splitTerm_add_single idx hs a b hy m (hA.splitMat_mulVec_part hs idx hξ.1 hy h τ).1
        (fun k => ?_) k z t
      simp only [dotProduct, (hA.hMat_mulVec_part hs idx hξ.1 hy τ _).1, Pi.add_apply, ← neg_mul]
      rw [Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _, ← Finset.mul_sum, h2, mul_zero]
  · refine GaussGauge.polyDeriv_eq_zero_y_dir hP hi hc
      (v := fun i => per X y ξ (rowOf X hr (τ, .inr i))) (fun h0 => ?_) _
      (analyticAt_splitTerm X bas idx a b y m) fun k z t => ?_
    · refine (hA.part_ne_zero hs idx hξ hy τ).1 ?_
      have h3 := congrFun (sum_letterDir_yVar X hr idx y ξ τ (0 : Fin 1)) 0
      simp only [show ∀ i, per X y ξ (rowOf X hr (τ, .inr i)) = 0 from congrFun h0, zero_smul,
        Finset.sum_const_zero, Pi.single_eq_same] at h3
      exact funext fun p => by simpa using (congrFun h3 (idx.symm p)).symm
    · rw [sum_letterDir_yVar]
      refine splitTerm_add_single idx hs a b hy m (hA.splitMat_mulVec_part hs idx hξ.1 hy h τ).2
        (fun k => ?_) k z t
      simp only [dotProduct, (hA.hMat_mulVec_part hs idx hξ.1 hy τ _).2, Pi.add_apply]
      rw [Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _, ← Finset.mul_sum, h1, mul_zero]

include idx in

theorem IsAdapted.exists_unip (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ K, coper X (rmul x (unip X K)) ξ = 0 :=
  exists_unip_coper_eq_zero hξ.2.1 (fun τ => (hx τ).1)
    (fun τ => (hA.part_ne_zero hs idx hξ hx τ).1) fun τ => (hA.part_ne_zero hs idx hξ hx τ).2

theorem IsAdapted.exists_expansion (hξ : X.IsIso ξ) (n : ℕ) (a b : Fin n → Fin g → ℝ)
    {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ} {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hH : Harm.IsHarmonic P) (hP : P ∈ GaussGauge.minorSpan (Fin n) c c')
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ A : (Fin n → Fin g → ℤ) → ℂ, (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
        HasSum (fun m : Fin n → Fin g → ℤ => A m * cexp (4 * Real.pi * I * ∑ τ,
          (((∑ k, cuspNu X bas ξ fun i => (m k i : ℝ) + a k i) τ : ℝ) : ℂ) * s τ))
          (thFr X hr bas idx n a b P (X.flow ξ s x))) ∧
      ∀ m : Fin n → Fin g → ℤ, (∑ k, cuspNu X bas ξ fun i => (m k i : ℝ) + a k i) = 0 → A m = 0 := by
  obtain ⟨K, hK⟩ := hA.exists_unip idx hs hξ hx
  obtain ⟨τ, hc⟩ := hc
  have hy := PerMove.rmul_mem_GG hx (unip_mem_Bor X K)
  refine ⟨_, summable_norm_flowCoeff hr idx hs n a b P hy, fun s hxs => ?_,
    fun m hm => hA.flowCoeff_eq_zero hr idx hs hξ n a b hP hc hy hK (congrFun hm τ)⟩
  rw [← thFr_congr bas idx (per_rmul_unip X _ K), ← flow_rmul]
  exact hA.hasSum_flowCoeff hr idx hs hξ n a b hH hy
    (flow_rmul X ξ s x _ ▸ PerMove.rmul_mem_GG hxs (unip_mem_Bor X K))

end Expansion

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem exists_isAdapted (hs : IsSympl X bas) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) :
    ∃ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (S : Finset (Fin g)),
      IsSympl X bas' ∧ IsAdapted X bas' ξ S := by
  let J : Submodule ℤ (Fin g ⊕ Fin g → ℤ) :=
    { carrier := {m | (bas m : Fin r → E) ∈ Submodule.span E {ξ}}
      add_mem' := fun {u v} hu hv => by
        rw [Set.mem_setOf_eq, map_add]; exact add_mem hu hv
      zero_mem' := by simp
      smul_mem' := fun k u hu => by
        rw [Set.mem_setOf_eq, map_zsmul, AddSubgroupClass.coe_zsmul]; exact zsmul_mem hu k }
  have hJ (m) : m ∈ J ↔ (bas m : Fin r → E) ∈ Submodule.span E {ξ} := Iff.rfl
  have hω (u v : Fin g ⊕ Fin g → ℤ) :
      standardAltForm (fun _ : Fin g => (1 : ℤ)) u v = omegaStd u v := by
    simp [standardAltForm_apply, omegaStd]
  obtain ⟨g', e, S, h₁, h₂, h₃⟩ := exists_symplectic_coordinates_adapted
    (isAlt_standardAltForm fun _ : Fin g => (1 : ℤ)) bijective_standardAltForm_one (I := J)
    (fun k m hk h => by
      rw [hJ, map_zsmul, AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul E] at h
      exact (hJ m).2 ((Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hk : (k : E) ≠ 0)).1 h))
    (fun u hu v hv => by
      obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 ((hJ u).1 hu)
      obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 ((hJ v).1 hv)
      obtain ⟨τ⟩ := nonempty_type X
      have h := hs u v
      rw [← hα, ← hβ, EF_eq_zero_of_herm X ((map_eq_zero τ.1).1 ?_)] at h
      · rw [hω]; simpa using h
      · have h1 (γ : E) : Data.emb τ.1 (γ • ξ) = τ.1 γ • Data.emb τ.1 ξ := by
          funext a; simp [Data.emb]
        rw [← hermC_emb, h1, h1, hermC_smul_left, hermC_smul_right, hermC_emb, hξ]
        simp) (Or.inl rfl)
  obtain rfl : g' = g := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h₃
    omega
  refine ⟨e.trans bas, S, fun u v => ?_, fun v => ?_⟩
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hs, ← hω, h₁, one_mul]
  · obtain ⟨m, rfl⟩ := bas.surjective v
    rw [← hJ, h₂, ← Submodule.apply_mem_span_image_iff_mem_span (f := bas.toLinearMap) bas.injective,
      Set.image_image]
    rfl

example : ∃ (bas : (Fin 2 ⊕ Fin 2 → ℤ) ≃ₗ[ℤ] HyperbolicCusp.flagData.Λ) (S : Finset (Fin 2)),
    IsSympl _ bas ∧ HyperbolicCusp.flagData.IsIso ![1, 1] ∧ IsAdapted _ bas ![1, 1] S ∧
      Gauss.one ∈ HyperbolicCusp.flagData.dom ∧ ∀ τ, cuspLin _ bas ![1, 1] τ ≠ 0 := by
  obtain ⟨bas, S, h₁, h₂⟩ := exists_isAdapted Gauss.isSympl_bas HyperbolicCusp.isIso_one.2.1
  exact ⟨bas, S, h₁, HyperbolicCusp.isIso_one, h₂, Gauss.one_mem,
    h₂.cuspLin_ne_zero h₁ HyperbolicCusp.isIso_one⟩

end

end GlobalTheory.ThFr
