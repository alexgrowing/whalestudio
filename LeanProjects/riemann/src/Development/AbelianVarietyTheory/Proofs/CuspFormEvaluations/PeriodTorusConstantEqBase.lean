import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EqTopOfForallEmbAllMem
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCMulImHermCEqSignMulTrace
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusCoordinates
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExistsOfParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem

open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf (conj_conj_X)

namespace GlobalTheory.PerTorus

noncomputable section

open ThFr TorusCoord TorusAtAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open Classical in

def dimPer (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then r - X.p0 else X.p0

theorem dimPer_mem {σ : E →+* ℂ} (h : σ ∈ X.Ψ) : dimPer X σ = r - X.p0 := by simp [dimPer, h]

theorem dimPer_not_mem {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimPer X σ = X.p0 := by simp [dimPer, h]

theorem dimPer_add (σ : E →+* ℂ) :
    dimPer X σ + dimPer X (ComplexEmbedding.conjugate σ) = r := by
  have := X.p0_le
  by_cases h : σ ∈ X.Ψ
  · rw [dimPer_mem X h, dimPer_not_mem X ((X.cmType σ).mp h)]; omega
  · rw [dimPer_not_mem X h, dimPer_mem X (conj_mem X h)]; omega

theorem card_idx_dimPer : Fintype.card (Idx (dimPer X)) = X.Ψ.card * r := by
  rw [Fintype.card_sigma, sum_emb_split X]
  simp [dimPer_add]

open Classical in

def rowFn (i : Idx (dimPer X)) : X.Ψ × Fin r :=
  if h : i.1 ∈ X.Ψ then (⟨i.1, h⟩, ⟨X.p0 + i.2.1, by
      have := lt_of_lt_of_eq i.2.2 (dimPer_mem X h); omega⟩)
  else (⟨ComplexEmbedding.conjugate i.1, conj_mem X h⟩, ⟨X.p0 - 1 - i.2.1, by
      have := lt_of_lt_of_eq i.2.2 (dimPer_not_mem X h); have := X.p0_le; omega⟩)

theorem rowFn_mem (τ : X.Ψ) (i : Fin (dimPer X τ.1)) (a : Fin r) (ha : (a : ℕ) = X.p0 + i) :
    rowFn X ⟨τ.1, i⟩ = (τ, a) := by
  unfold rowFn
  rw [dif_pos τ.2]
  exact Prod.ext rfl (Fin.ext ha.symm)

theorem rowFn_conj (τ : X.Ψ) (i : Fin (dimPer X (ComplexEmbedding.conjugate τ.1))) (a : Fin r)
    (ha : (a : ℕ) = X.p0 - 1 - i) : rowFn X ⟨ComplexEmbedding.conjugate τ.1, i⟩ = (τ, a) := by
  unfold rowFn
  rw [dif_neg ((X.cmType _).mp τ.2)]
  exact Prod.ext (Subtype.ext (conj_conj_X _)) (Fin.ext ha.symm)

theorem rowFn_bijective : Function.Bijective (rowFn X) := by
  refine (Fintype.bijective_iff_surjective_and_card _).2 ⟨?_, by rw [card_idx_dimPer]; simp⟩
  rintro ⟨τ, a⟩
  have := a.2
  by_cases h : (a : ℕ) < X.p0
  · exact ⟨_, rowFn_conj X τ ⟨X.p0 - 1 - a, by
      rw [dimPer_not_mem X ((X.cmType _).mp τ.2)]; omega⟩ a (by simp only; omega)⟩
  · exact ⟨_, rowFn_mem X τ ⟨a - X.p0, by rw [dimPer_mem X τ.2]; omega⟩ a (by simp only; omega)⟩

def rowEquiv : Idx (dimPer X) ≃ X.Ψ × Fin r := Equiv.ofBijective _ (rowFn_bijective X)

theorem rowEquiv_apply (i : Idx (dimPer X)) : rowEquiv X i = rowFn X i := rfl

theorem rowType_rowEquiv (i : Idx (dimPer X)) : rowType X (rowEquiv X i) = i.1 := by
  rw [rowEquiv_apply, rowFn]
  split_ifs with h
  · exact rowType_of_le X _ (Nat.le_add_right _ _)
  · have := lt_of_lt_of_eq i.2.2 (dimPer_not_mem X h)
    rw [rowType_of_lt X _ (by simp only; omega), conj_conj_X]

def perR (x : Frame X.Ψ r) (y : X.Ψ → Fin r → ℂ) (p : X.Ψ × Fin r) : ℂ :=
  if (p.2 : ℕ) < X.p0 then hermC p.1.1 X.Gm (FD.col (mat x p.1) p.2) (y p.1)
  else ((mat x p.1)⁻¹ *ᵥ y p.1) p.2

def scaledR (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimPer X) where
  toFun y := WithLp.toLp 2 fun i =>
    (Real.sqrt (X.c (rowEquiv X i).1) : ℂ) * perR X x y (rowEquiv X i)
  map_add' y y' := by
    ext i
    simp only [PiLp.add_apply, perR, Pi.add_apply]
    split_ifs
    · simp [hermC, mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply, mul_add]
  map_smul' t y := by
    ext i
    simp only [PiLp.smul_apply, perR, Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
    split_ifs
    · simp only [hermC, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply, Complex.real_smul]; ring

theorem scaledR_apply (x : Frame X.Ψ r) (y : X.Ψ → Fin r → ℂ) (i : Idx (dimPer X)) :
    scaledR X x y i = (Real.sqrt (X.c (rowEquiv X i).1) : ℂ) * perR X x y (rowEquiv X i) := rfl

def scaled (x : Frame X.Ψ r) : (Fin r → E) →+ Vsp (dimPer X) where
  toFun v := scaledR X x fun τ => Data.emb τ.1 v
  map_zero' := by rw [← map_zero (scaledR X x)]; congr 1; ext τ a; simp [Data.emb]
  map_add' u v := by rw [← map_add (scaledR X x)]; congr 1; ext τ a; simp [Data.emb]

theorem scaled_apply (x : Frame X.Ψ r) (v : Fin r → E) (i : Idx (dimPer X)) :
    scaled X x v i = (Real.sqrt (X.c (rowEquiv X i).1) : ℂ) * per X x v (rowEquiv X i) := rfl

theorem scaled_smul (x : Frame X.Ψ r) (α : 𝓞 E) (v : Fin r → E) :
    scaled X x ((α : E) • v) = act α (scaled X x v) := by
  ext i
  change _ = i.1 (α : E) * scaled X x v i
  rw [scaled_apply, scaled_apply, per_smul, rowType_rowEquiv]
  ring

theorem Hf_scaledR (x : Frame X.Ψ r) (y y' : X.Ψ → Fin r → ℂ) :
    Hf (scaledR X x y) (scaledR X x y') =
      ∑ τ : X.Ψ, (X.c τ : ℂ) * ∑ a, perR X x y (τ, a) * conj (perR X x y' (τ, a)) := by
  simp only [Finset.mul_sum]
  rw [Hf, ← Fintype.sum_prod_type' fun τ a =>
    (X.c τ : ℂ) * (perR X x y (τ, a) * conj (perR X x y' (τ, a)))]
  refine Fintype.sum_equiv (rowEquiv X) _ _ fun i => ?_
  have h : (Real.sqrt (X.c (rowEquiv X i).1) : ℂ) * Real.sqrt (X.c (rowEquiv X i).1) =
      X.c (rowEquiv X i).1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (c_pos X _).le]
  rw [scaledR_apply, scaledR_apply, map_mul, Complex.conj_ofReal, ← h]
  ring

section Orth

variable {X} {x : Frame X.Ψ r}
  (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
    Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
include hx

theorem col_orth (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (FD.col (mat x τ) a) (FD.col (mat x τ) b) =
      if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0 := by
  have := congrFun (congrFun (hx τ) a) b
  rwa [diagonal_apply] at this

theorem det_ne_zero (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [UnitFrame.gram_eq, det_mul, det_transpose, h, zero_mul, det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) h1.symm
  unfold FD.sgn; split_ifs <;> simp

theorem mem_dom : x ∈ X.dom := fun τ => by
  refine ⟨det_ne_zero hx τ, fun i => ?_⟩
  rw [dmin, lminor, hx, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
  have h : ∏ a : Fin i, ((fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∘
      Fin.castLE (Nat.le_of_lt_succ i.isLt)) a = ((psgn X.p0 i : ℝ) : ℂ) := by
    rw [psgn, Finset.prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.mpr fun a _ => ?_)
  unfold FD.sgn; split_ifs <;> simp

theorem norm_perR (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin r) :
    ‖perR X x y (τ, a)‖ = ‖hermC τ.1 X.Gm (y τ) (FD.col (mat x τ) a)‖ := by
  unfold perR
  split_ifs with h
  · rw [← hermC_conj τ.1 X.Gm_herm, Complex.norm_conj]
  · have hu : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ y τ) = y τ := by
      rw [mulVec_mulVec, mul_nonsing_inv _ (det_ne_zero hx τ).isUnit, one_mulVec]
    have hcol : FD.col (mat x τ) a = mat x τ *ᵥ Pi.single a 1 := by
      ext k; simp [FD.col]
    conv_rhs => rw [hcol, ← hu]
    rw [UnitFrame.hermC_mulVec, hx]
    simp only at h
    simp [dotProduct, mulVec_diagonal, FD.sgn, h, Pi.single_apply, apply_ite]

theorem norm_sq_scaledR (y : X.Ψ → Fin r → ℂ) :
    ‖scaledR X x y‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (y τ) := by
  have hmaj (τ : X.Ψ) := TorusAtDataPf.maj_eq_sum X τ _ (col_orth hx τ) x rfl
    ((TorusAtDataPf.e_linInd X τ _ (col_orth hx τ)).comp _ (Fin.castLE_injective X.p0_le)) (y τ)
  simp only [hmaj, Finset.mul_sum, ← norm_perR hx]
  rw [EuclideanSpace.norm_sq_eq, ← Fintype.sum_prod_type' fun τ a =>
    X.c τ * ‖perR X x y (τ, a)‖ ^ 2]
  refine Fintype.sum_equiv (rowEquiv X) _ _ fun i => ?_
  rw [scaledR_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (c_pos X _).le]

theorem scaledR_injective : Function.Injective (scaledR X x) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  funext τ
  by_contra h
  have h1 := norm_sq_scaledR hx y
  rw [hy, norm_zero] at h1
  have h2 : 0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (y τ) := by
    refine Finset.sum_pos' (fun σ _ => mul_nonneg (c_pos X σ).le ?_)
      ⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) (X.maj_pos (mem_dom hx) τ h)⟩
    rcases eq_or_ne (y σ) 0 with h0 | h0
    · simp [h0, Data.maj, Data.posPart, hermC]
    · exact (X.maj_pos (mem_dom hx) σ h0).le
  rw [← h1] at h2
  simp at h2

def scaledEquiv : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] Vsp (dimPer X) :=
  (scaledR X x).linearEquivOfInjective (scaledR_injective hx) (by
    rw [(WithLp.linearEquiv 2 ℝ (Idx (dimPer X) → ℂ)).finrank_eq]
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, card_idx_dimPer, smul_eq_mul, Fintype.card_coe, Fintype.card_fin]
    ring)

theorem exists_basis : ∃ b : Module.Basis (Fin (2 * Fintype.card (Idx (dimPer X)))) ℝ
    (Vsp (dimPer X)), ∀ y, y ∈ lat b ↔ ∃ v ∈ X.Λ, scaled X x v = y := by
  obtain ⟨b₀, hb₀⟩ := CMLattice.exists_basis_lattice E r X
  refine ⟨(b₀.map (scaledEquiv hx)).reindex (finCongr (by rw [card_idx_dimPer])), fun y => ?_⟩
  have h1 : Submodule.span ℤ (Set.range (b₀.map (scaledEquiv hx))) =
      (Submodule.span ℤ (Set.range b₀)).map ((scaledR X x).restrictScalars ℤ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [lat, Module.Basis.range_reindex, h1, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (hb₀ z).1 hz
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, (hb₀ _).2 ⟨v, hv, rfl⟩, rfl⟩

theorem im_Hf_scaled (u v : Fin r → E) :
    (Hf (scaled X x u) (scaled X x v)).im = EF X u v := by
  change (Hf (scaledR X x _) (scaledR X x _)).im = _
  rw [Hf_scaledR, EF_def, UnitFrame.trace_eq_sum_re X.Ψ X.cmType, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat x τ) (hx τ) (Data.emb τ.1 u)
    (Data.emb τ.1 v)
  rw [Complex.im_ofReal_mul]
  refine (congrArg _ h).trans ?_
  have h0 := re_map_xi_eq_zero X τ.1
  have hs := X.κ0_sign τ
  rw [hermC_emb_eq_map_herm, c_eq_two_mul_abs_im, map_mul, Complex.mul_re]
  rcases X.κ0_xi with h | h <;> rw [h] at hs ⊢ <;>
    simp only [map_neg, map_mul, map_div₀, map_ofNat] at hs ⊢
  · have : (τ.1 X.ξ0).im < 0 := by simp at hs; linarith
    rw [abs_of_neg this]; simp [h0]; ring
  · have : 0 < (τ.1 X.ξ0).im := by simp at hs; linarith
    rw [abs_of_pos this]; simp [h0]; ring

end Orth

section Torus

variable {Y : DataX E r} {x : Frame Y.Ψ r}
  (hx : ∀ τ : Y.Ψ, gram τ.1 Y.Gm (mat x τ) =
    Matrix.diagonal fun a : Fin r => ((sgn Y.p0 (a : ℕ) : ℝ) : ℂ))

def basis : Module.Basis (Fin (2 * Fintype.card (Idx (dimPer Y.toData)))) ℝ
    (Vsp (dimPer Y.toData)) := (exists_basis hx).choose

theorem mem_lat_basis (y : Vsp (dimPer Y.toData)) :
    y ∈ lat (basis hx) ↔ ∃ v ∈ Y.Λ, scaled Y.toData x v = y := (exists_basis hx).choose_spec y

theorem stable (α : 𝓞 E) (y : Vsp (dimPer Y.toData)) (hy : y ∈ lat (basis hx)) :
    act α y ∈ lat (basis hx) := by
  obtain ⟨v, hv, rfl⟩ := (mem_lat_basis hx y).1 hy
  exact (mem_lat_basis hx _).2 ⟨(α : E) • v, Y.Λ.smul_mem α hv, scaled_smul _ x α v⟩

theorem integral (y z : Vsp (dimPer Y.toData)) (hy : y ∈ lat (basis hx))
    (hz : z ∈ lat (basis hx)) : ∃ k : ℤ, (Hf y z).im = k := by
  obtain ⟨u, hu, rfl⟩ := (mem_lat_basis hx y).1 hy
  obtain ⟨v, hv, rfl⟩ := (mem_lat_basis hx z).1 hz
  obtain ⟨k, hk⟩ := Y.EF_int u hu v hv
  rw [im_Hf_scaled hx]
  rcases EF_eq_or Y.toData with h | h
  · exact ⟨k, by rw [h, hk, Rat.cast_intCast]⟩
  · exact ⟨-k, by rw [h, hk]; simp⟩

theorem perfect (ψ : lat (basis hx) →+ ℤ) : ∃ y ∈ lat (basis hx), ∀ z : lat (basis hx),
    (ψ z : ℝ) = (Hf y (z : Vsp (dimPer Y.toData))).im := by
  let j : Y.Λ →+ lat (basis hx) :=
    { toFun := fun v => ⟨scaled Y.toData x v, (mem_lat_basis hx _).2 ⟨v, v.2, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun u v => by ext1; simp }
  obtain ⟨u, hu, hψ⟩ := Y.EF_perf (ψ.comp j)
  have hu' : scaled Y.toData x u ∈ lat (basis hx) := (mem_lat_basis hx _).2 ⟨u, hu, rfl⟩
  rcases EF_eq_or Y.toData with h | h
  · refine ⟨_, hu', ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨v, hv, rfl⟩ := (mem_lat_basis hx z).1 hz
    rw [im_Hf_scaled hx, h, ← hψ ⟨v, hv⟩, Rat.cast_intCast]
    rfl
  · refine ⟨_, neg_mem hu', ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨v, hv, rfl⟩ := (mem_lat_basis hx z).1 hz
    rw [im_Hf_neg_left, im_Hf_scaled hx, h, ← hψ ⟨v, hv⟩, Rat.cast_neg, neg_neg, Rat.cast_intCast]
    rfl

variable {w₀ : 𝓞 E} (hw : (w₀ : E) + cc (w₀ : E) = 1)

include hw in
theorem coe_one_sub : ((1 - w₀ : 𝓞 E) : E) = cc (w₀ : E) := by
  rw [← sub_eq_iff_eq_add'.2 hw.symm]
  simp

theorem even_im_hermitian_sub : ∀ y ∈ lat (basis hx), ∀ z ∈ lat (basis hx), ∃ k : ℤ,
    (Hf y (act w₀ z)).im - (Hf y (act (1 - w₀) z)).im - (Hf y z).im = 2 * k := by
  intro y hy z hz
  obtain ⟨k, hk⟩ := integral hx y _ hy (stable hx (1 - w₀) z hz)
  have h : z = act w₀ z + act (1 - w₀) z := by
    ext i
    simp [act]
    ring
  refine ⟨-k, ?_⟩
  have h2 := im_Hf_add_right y (act w₀ z) (act (1 - w₀) z)
  rw [← h] at h2
  push_cast
  linarith

def perTorus : PT E :=
  torus r (dimPer_add Y.toData) (coe_one_sub hw) (stable hx) (even_im_hermitian_sub hx) (perfect hx)

end Torus

end

end GlobalTheory.PerTorus
