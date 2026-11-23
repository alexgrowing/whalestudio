import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Formalism.LocalRingCardinality.DataIdx

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Core

variable {K V M : Type} [Field K] {σ : K →+* ℂ} [AddCommGroup V] [Module K V]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]

theorem orth_inf_range (Ker : Submodule ℂ M) (eM : M →ₗ[ℂ] M) (hid : eM ∘ₗ eM = eM) (hsa : eM.IsSymmetric)
    (J : V →ₛₗ[σ] M) (Zl Zg : Set V) (op : V → V) (hop : ∀ x, eM (J x) = J (op x))
    (h1 : ∀ x ∈ Zl, J x ∈ Kerᗮ) (h2 : ∀ w, (∀ x ∈ Zl, inner ℂ (J x) w = 0) → w ∈ Ker)
    (h3 : ∀ x ∈ Zl, op x ∈ Zg) (h4 : Zg ⊆ Zl) (h5 : ∀ x ∈ Zg, op x = x) :
    Kerᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (J '' Zg) ∧
      ∀ y, eM (Kerᗮ.starProjection y) = (Kerᗮ ⊓ LinearMap.range eM).starProjection y := by
  have hN : Kerᗮ = Submodule.span ℂ (J '' Zl) := by
    apply le_antisymm
    · rw [← Submodule.orthogonal_orthogonal (Submodule.span ℂ (J '' Zl))]
      apply Submodule.orthogonal_le
      intro w hw
      exact h2 w fun x hx => hw _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact h1 x hx
  have hmap : ∀ y ∈ Kerᗮ, eM y ∈ Submodule.span ℂ (J '' Zg) := by
    intro y hy
    rw [hN] at hy
    have : Submodule.span ℂ (J '' Zl) ≤ (Submodule.span ℂ (J '' Zg)).comap eM := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      show eM (J x) ∈ Submodule.span ℂ (J '' Zg)
      rw [hop]
      exact Submodule.subset_span ⟨_, h3 x hx, rfl⟩
    exact this hy
  have hfix : ∀ y ∈ LinearMap.range eM, eM y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : M →ₗ[ℂ] M => f y) hid
  have hZ : Kerᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (J '' Zg) := by
    apply le_antisymm
    · rintro y ⟨hy, hy'⟩
      rw [← hfix y hy']
      exact hmap y hy
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨h1 x (h4 hx), J x, by rw [hop, h5 x hx]⟩
  refine ⟨hZ, fun y => ?_⟩
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hZ]
    exact hmap _ (Submodule.starProjection_apply_mem _ _)
  · rintro w ⟨hw, hw'⟩
    rw [inner_sub_left, hsa, hfix w hw', ← inner_sub_left]
    exact Submodule.starProjection_inner_eq_zero _ _ hw

omit [FiniteDimensional ℂ M] in

theorem inner_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : M) : inner ℂ (f x) (f y) = (n : ℂ) * inner ℂ x y := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h1 : ∀ x, ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • f) x‖ = ‖x‖ := by
    intro x
    have h2 : ‖f x‖ = Real.sqrt n * ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h, mul_pow, Real.sq_sqrt hn.le]
    rw [LinearMap.smul_apply, norm_smul, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h3 := (LinearMap.norm_map_iff_inner_map_map _).1 h1 x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hn.le] at h3
  rw [← h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']
  simp

omit [FiniteDimensional ℂ M] in
theorem inj_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := h x
  rw [hx, norm_zero] at this
  have h2 : ‖x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (show n * ‖x‖ ^ 2 = 0 by rw [← this]; simp) with h | h
    · exact absurd h hn.ne'
    · exact h
  simpa using h2

end Core

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec {n a b : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin n) (Fin b) K)
    (x : Fin a → K) (y : Fin b → K) : hform H (E *ᵥ x) (E' *ᵥ y) = star x ⬝ᵥ (Eᴴ * H * E') *ᵥ y := by
  rw [hform_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hform_orth {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K}
    (h : IsOrthProj H E Pr) (z : Fin d → K) (x : Fin n → K) : hform H (E *ᵥ z) (E *ᵥ (Pr *ᵥ x)) = hform H (E *ᵥ z) x := by
  have h1 := hform_mulVec H E (1 - E * Pr) z x
  rw [h.2, Matrix.zero_mulVec, dotProduct_zero, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero,
    ← Matrix.mulVec_mulVec] at h1
  exact h1.symm

variable (S : CSD K) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem csum_hform (x y : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm x : S.Forms) (S.basis.equivFun.symm y : S.Forms) = hform S.H x y :=
  (S.isClassSum x y).symm

theorem act_coord (t : G) (x : Fin S.dim → K) :
    r t (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.actMat r t *ᵥ x) :=
  Subtype.ext (S.I_actMat r t x).symm

theorem gaOp_coord (a : MonoidAlgebra K G) (x : Fin S.dim → K) :
    S.gaOp r a (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.gaMat r a *ᵥ x) := by
  simp only [CSD.gaOp, CSD.gaMat, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, map_sum,
    map_smul, act_coord]

def lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlForm_apply (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    lvlForm S r P ψ x = S.basis.equivFun.symm (S.lvlE r P ψ *ᵥ x) := rfl

theorem lvlForm_injective (P : Subgroup G) (ψ : P →* Kˣ) : Function.Injective (lvlForm S r P ψ) :=
  S.basis.equivFun.symm.injective.comp (image_idempotent_spec K _ _).1

theorem range_lvlE (P : Subgroup G) (ψ : P →* Kˣ) : LinearMap.range (S.lvlE r P ψ).mulVecLin = S.lvlPart r P ψ :=
  (image_idempotent_spec K _ _).2.trans (level_part_spec K S G r P ψ)

theorem range_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : Set.range (lvlForm S r P ψ) = lvlForms S r P ψ := by
  ext f
  obtain ⟨u, rfl⟩ := S.basis.equivFun.symm.surjective f
  have key : S.basis.equivFun.symm u ∈ lvlForms S r P ψ ↔ u ∈ S.lvlPart r P ψ := by
    refine forall_congr' fun h => ?_
    rw [act_coord, ← map_smul, S.basis.equivFun.symm.injective.eq_iff]
  rw [key, ← range_lvlE]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, S.basis.equivFun.symm.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem csum_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) (x y : Fin (S.lvlDim r P ψ) → K) :
    S.csum (lvlForm S r P ψ x) (lvlForm S r P ψ y) = (Nat.card P : K) * hform (S.lvlH r P ψ) x y := by
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  rw [lvlForm_apply, lvlForm_apply, csum_hform, hform_mulVec, hform_dot, CSD.lvlH, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

theorem mem_lvlNab (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    x ∈ S.lvlNab r P ψ ↔ lvlForm S r P ψ x ∈ intForms S := by
  unfold CSD.lvlNab CSD.cutNab CSD.nabLat
  rw [exponent_index_lattice.mem_cutLat, mem_valLatF]
  rfl

theorem gaOp_mem {Z : Submodule K S.Forms} (hZ : ∀ g, ∀ f ∈ Z, r g f ∈ Z) (a : MonoidAlgebra K G) {f : S.Forms} (hf : f ∈ Z) :
    S.gaOp r a f ∈ Z := by
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Z.sum_mem fun g _ => Z.smul_mem _ (hZ g f hf)

end Coord

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lvlE_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ x) := by
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2 (lvlIdem ℓ.P ℓ.ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ _ hc.symm).1]

theorem lvlForm_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaOp B.r (idemOf ℓ.X) (lvlForm B.S B.r ℓ.P ℓ.ψ x) := by
  rw [lvlForm_apply, lvlForm_apply, gaOp_coord, lvlE_lvlOp h]

theorem lvlE_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.lE ℓ Z *ᵥ z) = B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, BlockDat.lf_lvlE_lE h]
  rfl

theorem lvlForm_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) = B.toF ℓ Z z := by
  rw [lvlForm_apply, lvlE_lE h]
  rfl

theorem mem_Z0_iff (w : Fin (B.nV ℓ) → K) : w ∈ B.Z0 ℓ Z ↔ B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w) ∈ Z := by
  constructor
  · rintro ⟨f, hf, hw⟩
    have : B.vE ℓ *ᵥ w = B.S.basis.equivFun f := hw.symm
    rw [this, LinearEquiv.symm_apply_apply]
    exact hf
  · intro hw
    exact ⟨_, hw, B.S.basis.equivFun.apply_symm_apply _⟩

theorem range_zE : LinearMap.range (B.zE ℓ Z).mulVecLin = B.Z0 ℓ Z := (subspace_image_spec K _ (B.Z0 ℓ Z)).2

theorem range_vE (h : BlockHyp B ℓ v0 s) : LinearMap.range (B.vE ℓ).mulVecLin =
    LinearMap.range (B.S.gaMat B.r (idemOf ℓ.X)).mulVecLin ⊓ B.S.lvlPart B.r ℓ.P ℓ.ψ :=
  good_part_spec K B.S G B.r ℓ.X h.irr ℓ.P ℓ.ψ

theorem lE_mem (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) : lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) ∈ Z := by
  rw [lvlForm_apply, lvlE_lE h, ← mem_Z0_iff, ← range_zE]
  exact ⟨z, rfl⟩

theorem lvlOp_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ (B.lE ℓ Z *ᵥ z) = B.lE ℓ Z *ᵥ z := by
  apply BlockDat.lf_lvlE_inj
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lvlOp h, lvlE_lE h]
  have hm : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
  rw [range_vE h] at hm
  obtain ⟨⟨u, hu⟩, -⟩ := hm
  rw [← hu, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2,
    (idempotent_spec K v0 h.conj G ℓ.X h.irr).1.idem]

theorem lvlOp_mem (h : BlockHyp B ℓ v0 s) (hZ : ∀ g, ∀ f ∈ Z, B.r g f ∈ Z) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K)
    (hx : lvlForm B.S B.r ℓ.P ℓ.ψ x ∈ Z) :
    ∃ z, B.lE ℓ Z *ᵥ z = B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x := by
  have hm : B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
    rw [range_vE h]
    refine ⟨⟨_, (lvlE_lvlOp h x).symm⟩, ?_⟩
    rw [← range_lvlE]
    exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hm
  rw [Matrix.mulVecLin_apply] at hw
  have hw0 : w ∈ B.Z0 ℓ Z := by
    rw [mem_Z0_iff, hw, ← lvlForm_apply, lvlForm_lvlOp h]
    exact gaOp_mem _ _ hZ _ hx
  rw [← range_zE] at hw0
  obtain ⟨z, rfl⟩ := hw0
  refine ⟨z, BlockDat.lf_lvlE_inj ?_⟩
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lE h, ← hw]
  rfl

theorem exists_lvl_proj (h : BlockHyp B ℓ v0 s) (hZ : ∀ g, ∀ f ∈ Z, B.r g f ∈ Z) {f : B.S.Forms} (hf : f ∈ Z) :
    ∃ x, lvlForm B.S B.r ℓ.P ℓ.ψ x ∈ Z ∧ ∀ y, B.S.csum (lvlForm B.S B.r ℓ.P ℓ.ψ y) (lvlForm B.S B.r ℓ.P ℓ.ψ x) =
      B.S.csum (lvlForm B.S B.r ℓ.P ℓ.ψ y) f := by
  obtain ⟨u, rfl⟩ := B.S.basis.equivFun.symm.surjective f
  refine ⟨B.S.lvlPr B.r ℓ.P ℓ.ψ *ᵥ u, ?_, fun y => ?_⟩
  · rw [lvlForm_apply, Matrix.mulVec_mulVec, (BlockDat.lf_lvl_proj h).2, ← gaOp_coord]
    exact gaOp_mem _ _ hZ _ hf
  · rw [lvlForm_apply, lvlForm_apply, csum_hform, csum_hform, hform_orth (BlockDat.lf_lvl_proj h).1]

theorem span_range_mulVec {σ : K →+* ℂ} {M : Type} [AddCommGroup M] [Module ℂ M] {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (E : Matrix (Fin n) (Fin d) K) :
    Submodule.span ℂ (J '' Set.range fun z => E *ᵥ z) = Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin d → K) := by
      ext i; simp [Pi.single_apply]
    rw [SetLike.mem_coe]
    beta_reduce
    rw [hz, Matrix.mulVec_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mulVec_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

variable {σ : K →+* ℂ} {H M ML : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M] [AddCommGroup ML] [Module K ML]

omit [FiniteDimensional ℂ M] in

theorem exists_coord (j : B.S.Forms →ₛₗ[σ] H) (hj : Function.Injective j) (jM : ML →ₛₗ[σ] M) (hjM : Function.Injective jM)
    (eV : M →ₗ[ℂ] H) (heV : Function.Injective eV)
    (hrat : Set.range (fun x => eV (jM x)) = j '' lvlForms B.S B.r ℓ.P ℓ.ψ) :
    ∃ e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) ≃ₗ[K] ML, ∀ x, eV (jM (e x)) = j (lvlForm B.S B.r ℓ.P ℓ.ψ x) := by
  have hex : ∀ x, ∃ y, eV (jM y) = j (lvlForm B.S B.r ℓ.P ℓ.ψ x) := by
    intro x
    have : j (lvlForm B.S B.r ℓ.P ℓ.ψ x) ∈ Set.range (fun x => eV (jM x)) := by
      rw [hrat, ← range_lvlForm]
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    exact this
  choose g hg using hex
  have hi : ∀ a b, eV (jM a) = eV (jM b) → a = b := fun a b hab => hjM (heV hab)
  let g' : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) →ₗ[K] ML :=
    { toFun := g
      map_add' := fun x y => hi _ _ (by simp only [map_add, hg])
      map_smul' := fun a x => hi _ _ (by simp only [map_smulₛₗ, hg, RingHom.id_apply]) }
  refine ⟨LinearEquiv.ofBijective g' ⟨fun x y hxy => ?_, fun y => ?_⟩, hg⟩
  · have hxy' : g x = g y := hxy
    apply lvlForm_injective B.S B.r ℓ.P ℓ.ψ
    apply hj
    rw [← hg, ← hg, hxy']
  · have : eV (jM y) ∈ j '' lvlForms B.S B.r ℓ.P ℓ.ψ := hrat ▸ ⟨y, rfl⟩
    rw [← range_lvlForm] at this
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := this
    exact ⟨x, hi _ _ ((hg x).trans hx)⟩

theorem coord_facts (h : BlockHyp B ℓ v0 s) (hZ : ∀ g, ∀ f ∈ Z, B.r g f ∈ Z)
    (j : B.S.Forms →ₛₗ[σ] H) (hj : ∀ f g : B.S.Forms, inner ℂ (j f) (j g) = σ (B.S.csum f g))
    (Kθ : Submodule ℂ H) (hz1 : ∀ f ∈ Z, j f ∈ Kθᗮ) (hz2 : ∀ w, (∀ f ∈ Z, inner ℂ (j f) w = 0) → w ∈ Kθ)
    (eV : M →ₗ[ℂ] H) (hn : ∀ x, ‖eV x‖ ^ 2 = (Nat.card ℓ.P : ℝ) * ‖x‖ ^ 2)
    (hr : LinearMap.range eV = Submodule.span ℂ (j '' lvlForms B.S B.r ℓ.P ℓ.ψ))
    (eM : M →ₗ[ℂ] M) (hid : eM ∘ₗ eM = eM) (hsa : eM.IsSymmetric)
    (he : ∀ x f, eV x = j f → eV (eM x) = j (B.S.gaOp B.r (idemOf ℓ.X) f))
    (J : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) →ₛₗ[σ] M) (hJ : ∀ x, eV (J x) = j (lvlForm B.S B.r ℓ.P ℓ.ψ x)) :
    (∀ x y, inner ℂ (J x) (J y) = σ (hform (B.S.lvlH B.r ℓ.P ℓ.ψ) x y)) ∧
    (∀ x, eM (J x) = J (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x)) ∧
    (Kθ.comap eV)ᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (Set.range fun k => J (B.lE ℓ Z *ᵥ Pi.single k 1)) ∧
    (∀ y, eM ((Kθ.comap eV)ᗮ.starProjection y) = ((Kθ.comap eV)ᗮ ⊓ LinearMap.range eM).starProjection y) ∧
    ∀ x, ((Kθ.comap eV)ᗮ ⊓ LinearMap.range eM).starProjection (J x) = J (B.lE ℓ Z *ᵥ (B.lPr ℓ Z *ᵥ x)) := by
  have hpos : (0 : ℝ) < Nat.card ℓ.P := by exact_mod_cast Nat.card_pos (α := ℓ.P)
  have hc : (((Nat.card ℓ.P : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hin := inner_of_norm_sq eV hpos hn
  have hinj := inj_of_norm_sq eV hpos hn
  have h1 : ∀ x y, inner ℂ (J x) (J y) = σ (hform (B.S.lvlH B.r ℓ.P ℓ.ψ) x y) := by
    intro x y
    apply mul_left_cancel₀ hc
    rw [← hin, hJ, hJ, hj, csum_lvlForm, map_mul, map_natCast]
    simp
  have h2 : ∀ x, eM (J x) = J (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) := by
    intro x
    apply hinj
    rw [he _ _ (hJ x), hJ, lvlForm_lvlOp h]
  obtain ⟨h3, h4⟩ := orth_inf_range (Kθ.comap eV) eM hid hsa J {x | lvlForm B.S B.r ℓ.P ℓ.ψ x ∈ Z}
    (Set.range fun z => B.lE ℓ Z *ᵥ z) _ h2
    (by
      intro x hx u hu
      apply mul_left_cancel₀ hc
      rw [← hin, hJ, mul_zero]
      exact hz1 _ hx _ hu)
    (by
      intro w hw
      refine hz2 _ fun f hf => ?_
      obtain ⟨x, hx, hxf⟩ := exists_lvl_proj h hZ hf
      have hw' : inner ℂ (j (lvlForm B.S B.r ℓ.P ℓ.ψ x)) (eV w) = 0 := by
        rw [← hJ, hin, hw x hx, mul_zero]
      have hmem : eV w ∈ Submodule.span ℂ (j '' lvlForms B.S B.r ℓ.P ℓ.ψ) := hr ▸ ⟨w, rfl⟩
      have hle : Submodule.span ℂ (j '' lvlForms B.S B.r ℓ.P ℓ.ψ) ≤
          (Submodule.span ℂ {j f - j (lvlForm B.S B.r ℓ.P ℓ.ψ x)})ᗮ := by
        rw [Submodule.span_le, ← range_lvlForm]
        rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hj, hj, hxf, sub_self]
      have := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hmem)
      rwa [inner_sub_left, hw', sub_zero] at this)
    (by
      intro x hx
      exact lvlOp_mem h hZ x hx)
    (by
      rintro _ ⟨z, rfl⟩
      exact lE_mem h z)
    (by
      rintro _ ⟨z, rfl⟩
      exact lvlOp_lE h z)
  refine ⟨h1, h2, h3.trans (span_range_mulVec J _), h4, fun x => ?_⟩
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [h3]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  · intro w hw
    rw [h3] at hw
    have hle : Submodule.span ℂ (J '' Set.range fun z => B.lE ℓ Z *ᵥ z) ≤
        (Submodule.span ℂ {J x - J (B.lE ℓ Z *ᵥ (B.lPr ℓ Z *ᵥ x))})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, h1, h1,
        hform_orth (BlockDat.lf_l_proj h), sub_self]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

omit [FiniteDimensional ℂ M] in

theorem coord_lattice [Module (𝓞 K) ML] [IsScalarTower (𝓞 K) K ML]
    (j : B.S.Forms →ₛₗ[σ] H) (jM : ML →ₛₗ[σ] M) (hjM : Function.Injective jM)
    (eV : M →ₗ[ℂ] H) (heV : Function.Injective eV)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) ≃ₗ[K] ML) (hJ : ∀ x, eV (jM (e x)) = j (lvlForm B.S B.r ℓ.P ℓ.ψ x))
    (C : Set M) (hC : ∀ m ∈ C, m ∈ Set.range jM)
    (hlat : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ eV '' C, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ j '' (lvlForms B.S B.r ℓ.P ℓ.ψ ∩ intForms B.S), y = σ (a : K) • x}) :
    Submodule.span (𝓞 K) {x | jM x ∈ C} =
      (B.S.lvlNab B.r ℓ.P ℓ.ψ).map ((e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) →ₗ[K] ML).restrictScalars (𝓞 K)) := by
  have key : ∀ (N : Submodule (𝓞 K) ML) (S : Set H), (∀ y ∈ S, ∃ x ∈ N, eV (jM x) = y) →
      ∀ y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}, ∃ x ∈ N, eV (jM x) = y := by
    intro N S hS y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := hS u hu
      refine ⟨a • x, N.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, N.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', N.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, N.neg_mem hx, by simp⟩
  have hsub : ∀ (S : Set H), ∀ y ∈ S, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} :=
    fun S y hy => AddSubgroup.subset_closure ⟨1, y, hy, by simp⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    have h1 := hsub (eV '' C) _ ⟨_, hx, rfl⟩
    rw [hlat] at h1
    obtain ⟨x', hx', hxx⟩ := key ((B.S.lvlNab B.r ℓ.P ℓ.ψ).map
      ((e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) →ₗ[K] ML).restrictScalars (𝓞 K))) _ (by
        rintro _ ⟨f, ⟨hf, hf'⟩, rfl⟩
        rw [← range_lvlForm] at hf
        obtain ⟨y, rfl⟩ := hf
        exact ⟨e y, ⟨y, (mem_lvlNab _ _ _ _ y).2 hf', rfl⟩, hJ y⟩) _ h1
    rw [← hjM (heV hxx)]
    exact hx'
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hsub (j '' (lvlForms B.S B.r ℓ.P ℓ.ψ ∩ intForms B.S)) (j (lvlForm B.S B.r ℓ.P ℓ.ψ y))
      ⟨_, ⟨range_lvlForm B.S B.r ℓ.P ℓ.ψ ▸ ⟨y, rfl⟩, (mem_lvlNab _ _ _ _ y).1 hy⟩, rfl⟩
    rw [← hlat] at h1
    obtain ⟨x', hx', hxx⟩ := key (Submodule.span (𝓞 K) {x | jM x ∈ C}) _ (by
        rintro _ ⟨m, hm, rfl⟩
        obtain ⟨x, rfl⟩ := hC m hm
        exact ⟨x, Submodule.subset_span hm, rfl⟩) _ h1
    rw [← hJ] at hxx
    have : x' = e y := hjM (heV hxx)
    rw [this] at hx'
    exact hx'

end Block

end GlobalTheory.Mem.LiftForms

end
