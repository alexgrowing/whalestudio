import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E) (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h
    · rw [mul_smul]; exact Λ.smul_mem _ h'
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have : (b * d) • (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) • x = a • d • x := by
      rw [← algebraMap_smul E (b * d), ← algebraMap_smul E a, ← algebraMap_smul E d, smul_smul, smul_smul]
      congr 1
      rw [map_mul]; field_simp
    rw [this]; exact Λ.smul_mem _ h

theorem span_inf {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (W : Submodule E (Fin n → E)) :
    Submodule.span E ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = W := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun y hy => hy.2
  · intro y hy
    obtain ⟨d, hd, h⟩ := exists_smul_mem Λ y (hΛ ▸ Submodule.mem_top)
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd
    have h1 : d • y ∈ Submodule.span E
        ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.subset_span ⟨h, (W.restrictScalars (𝓞 E)).smul_mem d hy⟩
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ h1
    rwa [← algebraMap_smul E d, smul_smul, inv_mul_cancel₀ hd1, one_smul] at h2

theorem isSatFlag_inf (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤) {a : ℕ} (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule I.E (Fin I.n → I.E)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hr : ∀ i : Fin a, Module.finrank I.E (W i.succ) = Module.finrank I.E (W i.castSucc) + j i)
    (hi : ∀ x ∈ W (Fin.last a), ∀ y ∈ W (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0) :
    IsSatFlag I Λ j fun i => Λ ⊓ (W i).restrictScalars (𝓞 I.E) := by
  refine ⟨by simp [h0], fun i k h => inf_le_inf_left _ fun y hy => hm h hy, fun i => ?_, fun i y => ?_,
    fun x hx y hy => hi x hx.2 y hy.2⟩
  · unfold Formalism.HN.rkK
    rw [span_inf Λ hΛ, span_inf Λ hΛ, hr]
  · rw [span_inf Λ hΛ]; rfl

theorem exists_isSatFlag_one (I : AutInst) (x : Fin I.n → I.E) (hx : x ≠ 0)
    (hi : Formalism.UG.hform (starRingEnd I.E) I.J x x = 0) :
    ∃ S, IsSatFlag I I.L (fun _ : Fin 1 => 1) S := by
  refine ⟨_, isSatFlag_inf I I.L I.L_span _ ![⊥, I.E ∙ x] rfl ?_ ?_ ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i
    fin_cases i
    change Module.finrank I.E (I.E ∙ x) = Module.finrank I.E (⊥ : Submodule I.E (Fin I.n → I.E)) + 1
    rw [finrank_span_singleton hx, finrank_bot]
  · intro y hy z hz
    change y ∈ I.E ∙ x at hy
    change z ∈ I.E ∙ x at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have : Formalism.UG.hform (starRingEnd I.E) I.J (c • x) (d • x) =
        starRingEnd I.E c * d * Formalism.UG.hform (starRingEnd I.E) I.J x x := by
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hi, mul_zero]

theorem cIw_one_one : cIw 1 1 (fun _ : Fin 1 => 1) = Real.pi := by
  have h : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * 2 = 2 ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one (by norm_num)]; norm_num
  have hp : (2 : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have e : cIw 1 1 (fun _ : Fin 1 => 1) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.pi * (2 * Real.pi)) / (2 * Real.pi * 2 ^ (1 / 2 : ℝ)) := by
    simp [cIw, dimN, volU, sphV, Finset.filter_singleton]
  rw [e, div_eq_iff (by positivity)]
  calc _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * 2 * (2 * Real.pi * Real.pi) := by ring
    _ = _ := by rw [h]; ring

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))

theorem rankFac_eq (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) :
    rankFac E (M + 1) = Formalism.HermitianLatticesTheory.massRatioRightSide E (M + 1) *
      (2 * Real.pi ^ (M + 1) / (M.factorial : ℝ) * 2 ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E := by
    unfold Formalism.HermitianLatticesTheory.vInv
    have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
    positivity
  unfold rankFac Formalism.HermitianLatticesTheory.massRatioRightSide
  generalize Formalism.HermitianLatticesTheory.vInv E = v at hv
  generalize Formalism.HermitianLatticesTheory.fDeg E = f
  have hπ := Real.pi_pos
  have e1 : ((M.factorial : ℝ) * (v / Real.pi) ^ (M + 1)) * (2 * Real.pi ^ (M + 1) / (M.factorial : ℝ) * 2 ^ M)
      = (2 * v) ^ (M + 1) := by
    have : (M.factorial : ℝ) ≠ 0 := by positivity
    rw [div_pow, mul_pow]; field_simp; ring
  have e2 : (2 * v) ^ ((f : ℝ) * (((M + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (M + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_sub (by positivity)]
    congr 1; push_cast; ring
  rw [e2, ← e1, mul_pow, Nat.add_sub_cancel]
  ring

theorem finrank_span_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) =
      Module.finrank E (Submodule.span E s) := by
  letI : Algebra E ℂ := φ.toAlgebra
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent E s
  haveI : Finite t := hli.finite
  haveI : Fintype t := Fintype.ofFinite t
  have hli' : LinearIndependent ℂ fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E)) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hli'
  rw [Subtype.range_coe, hsp] at h1
  rw [h1, ← h2]
  suffices hs : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) =
      Submodule.span ℂ (Set.range fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E))) by rw [hs]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span E t := hsp ▸ Submodule.subset_span hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    | zero =>
      have : (fun l : Fin n => φ ((0 : Fin n → E) l)) = 0 := by ext; simp
      simp only [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun l : Fin n => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      simp only [this]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : (fun l : Fin n => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      simp only [this]; exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i, hts i.2, rfl⟩

theorem finrank_flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (i : Fin (a + 1)) :
    Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) :=
    Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  have : flagAt I S v i = (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
      (Matrix.mulVecLin (I.P v)⁻¹) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [this, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image]
  rfl

theorem isIsoFlag_flagAt (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h : IsSatFlag I Λ j S) (v : InfinitePlace I.F) :
    IsIsoFlag (I.ε v) j (flagAt I S v) := by
  obtain ⟨h0, hm, hr, -, hi⟩ := h
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  refine ⟨by simp [flagAt, h0]; exact Matrix.mulVec_zero _, fun i k hik => Submodule.span_mono (Set.image_mono (hm hik)), fun i => ?_, ?_⟩
  · rw [finrank_flagAt, finrank_flagAt, hr]
  · have key : ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a),
        star ((I.P v)⁻¹ *ᵥ fun l => I.φ v (x l)) ⬝ᵥ
          (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ fun l => I.φ v (y l))) = 0 := by
      intro x hx y hy
      rw [← I.P_spec v, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      have h1 := congrArg (I.φ v) (hi x hx y hy)
      rw [map_zero] at h1
      rw [← h1]
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
        Matrix.map_apply, starRingEnd_apply, I.cm.cmUnram.2.1, mul_assoc]
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨y, hy, rfl⟩ := hy; exact key x hx y hy
      | zero => simp
      | add y z _ _ h1 h2 => rw [Matrix.mulVec_add, dotProduct_add, h1, h2, add_zero]
      | smul c y _ h1 => rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
    | zero => simp
    | add x z _ _ h1 h2 => rw [star_add, add_dotProduct, h1, h2, add_zero]
    | smul c x _ h1 => rw [star_smul, smul_dotProduct, h1, smul_zero]

end GlobalTheory.FlagMeas.SatModel
