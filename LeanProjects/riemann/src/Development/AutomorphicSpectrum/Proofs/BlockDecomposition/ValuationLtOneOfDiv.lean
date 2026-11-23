import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound.LargeLattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem uniformizer_mem : (uniformizer F : F) ∈ 𝒪[F] :=
  (Valuation.mem_integer_iff _ _).2 (valuation_uniformizer_lt_one F).le

theorem exists_pow_mul_mem (a : F) : ∃ M : ℕ, (uniformizer F : F) ^ M * a ∈ 𝒪[F] := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hvx : ValuativeRel.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, (Valuation.mem_integer_iff _ _).2 ?_⟩
  have h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F a < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  rw [map_mul, map_pow]
  exact h1.le

theorem lat_mono {m M M' : ℕ} (h : M ≤ M') : lat F m M ⊆ lat F m M' := by
  intro x hx i
  have : (uniformizer F : F) ^ M' * x i =
      (uniformizer F : F) ^ (M' - M) * ((uniformizer F : F) ^ M * x i) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  rw [this]
  exact Subring.mul_mem _ (Subring.pow_mem _ uniformizer_mem _) (hx i)

theorem exists_mem_lat {m : ℕ} (x : Fin m → F) : ∃ M, x ∈ lat F m M := by
  choose M hM using fun i => exists_pow_mul_mem (x i)
  refine ⟨Finset.univ.sup M, fun i => ?_⟩
  exact lat_mono (m := 1) (F := F) (Finset.le_sup (f := M) (Finset.mem_univ i))
    (show (fun _ => x i) ∈ lat F 1 (M i) from fun _ => hM i) 0

theorem mem_lat_iff_box {m M : ℕ} {x : Fin m → F} :
    x ∈ lat F m M ↔ ((uniformizer F : F) ^ M • x) ∈ Measures.box F (Fin m) := by
  rw [Measures.mem_box]
  rfl

theorem mulVec_mem_lat {m M : ℕ} {A : Matrix (Fin m) (Fin m) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    {x : Fin m → F} (hx : x ∈ lat F m M) : A *ᵥ x ∈ lat F m M := by
  rw [mem_lat_iff_box, ← Matrix.mulVec_smul]
  exact Measures.mulVec_mem_box hA (mem_lat_iff_box.1 hx)

def rowM {k : ℕ} (η : Fin (k + 1) → F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  Matrix.of fun i j => if i = Fin.last k then η j else 0

theorem rowM_mul {k : ℕ} (η : Fin (k + 1) → F) :
    rowM η * rowM η = η (Fin.last k) • rowM η := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = Fin.last k
  · simp [rowM, hi]
  · simp [rowM, hi]

def hGL {k : ℕ} (η : Fin (k + 1) → F) (hu : 1 - η (Fin.last k) ≠ 0) : GL (Fin (k + 1)) F where
  val := 1 - rowM η
  inv := 1 + (1 - η (Fin.last k))⁻¹ • rowM η
  val_inv := by
    rw [sub_mul, one_mul, mul_add, mul_one, mul_smul_comm, rowM_mul, smul_smul]
    have : (1 - η (Fin.last k))⁻¹ * η (Fin.last k) = (1 - η (Fin.last k))⁻¹ - 1 := by
      field_simp
      ring
    rw [this, sub_smul, one_smul]
    abel
  inv_val := by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, rowM_mul, smul_smul]
    have : (1 - η (Fin.last k))⁻¹ * η (Fin.last k) = (1 - η (Fin.last k))⁻¹ - 1 := by
      field_simp
      ring
    rw [this, sub_smul, one_smul]
    abel

theorem hGL_mulVec_last {k : ℕ} (η : Fin (k + 1) → F) (hu : 1 - η (Fin.last k) ≠ 0)
    (x : Fin (k + 1) → F) :
    (((hGL η hu : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) (Fin.last k) =
      x (Fin.last k) - η ⬝ᵥ x := by
  show ((1 - rowM η) *ᵥ x) (Fin.last k) = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [rowM, Matrix.mulVec, dotProduct]

theorem valuation_lt_one_of_div {c : ℕ} {e t : F} (ht : t ∈ 𝒪[F])
    (he : e = (uniformizer F : F) ^ (c + 1) * t) : ValuativeRel.valuation F e < 1 := by
  have h1 : ValuativeRel.valuation F t ≤ 1 := (Valuation.mem_integer_iff _ _).1 ht
  have h2 : ValuativeRel.valuation F (uniformizer F : F) ^ (c + 1) < 1 :=
    pow_lt_one₀ zero_le' (valuation_uniformizer_lt_one F) (Nat.succ_ne_zero c)
  rw [he, map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) h2

theorem one_sub_valuation {e : F} (he : ValuativeRel.valuation F e < 1) :
    ValuativeRel.valuation F (1 - e) = 1 :=
  Valuation.map_one_sub_of_lt _ he

theorem one_sub_ne_zero {e : F} (he : ValuativeRel.valuation F e < 1) : 1 - e ≠ 0 := by
  intro h
  have := one_sub_valuation he
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem inv_one_sub_mem {e : F} (he : ValuativeRel.valuation F e < 1) : (1 - e)⁻¹ ∈ 𝒪[F] := by
  rw [Valuation.mem_integer_iff, map_inv₀, one_sub_valuation he, inv_one]

theorem one_apply_mem {ι : Type} [DecidableEq ι] (i j : ι) :
    (1 : Matrix ι ι F) i j ∈ 𝒪[F] := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem mem_of_div_sub_one {ι : Type} [DecidableEq ι] {c : ℕ} {A : Matrix ι ι F}
    (h : Div c (A - 1)) (i j : ι) : A i j ∈ 𝒪[F] := by
  obtain ⟨y, hy, e⟩ := h i j
  have : A i j = (uniformizer F : F) ^ c * y + (1 : Matrix ι ι F) i j := by
    rw [← e, Matrix.sub_apply, sub_add_cancel]
  rw [this]
  exact Subring.add_mem _ (Subring.mul_mem _ (Subring.pow_mem _ uniformizer_mem _) hy)
    (one_apply_mem i j)

theorem hGL_div {k c : ℕ} {η : Fin (k + 1) → F}
    (hη : ∀ j, ∃ t ∈ 𝒪[F], η j = (uniformizer F : F) ^ (c + 1) * t)
    (hu : 1 - η (Fin.last k) ≠ 0) :
    Div (c + 1) (((hGL η hu : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) := by
  intro i j
  show ∃ y ∈ 𝒪[F], ((1 - rowM η) - 1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) i j = _
  obtain ⟨t, ht, e⟩ := hη j
  by_cases hi : i = Fin.last k
  · refine ⟨-t, Subring.neg_mem _ ht, ?_⟩
    simp [rowM, hi, e]
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    simp [rowM, hi]

theorem hGL_inv_div {k c : ℕ} {η : Fin (k + 1) → F}
    (hη : ∀ j, ∃ t ∈ 𝒪[F], η j = (uniformizer F : F) ^ (c + 1) * t)
    (hv : ValuativeRel.valuation F (η (Fin.last k)) < 1)
    (hu : 1 - η (Fin.last k) ≠ 0) :
    Div (c + 1) ((((hGL η hu)⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) := by
  intro i j
  show ∃ y ∈ 𝒪[F], ((1 + (1 - η (Fin.last k))⁻¹ • rowM η) - 1 :
    Matrix (Fin (k + 1)) (Fin (k + 1)) F) i j = _
  obtain ⟨t, ht, e⟩ := hη j
  by_cases hi : i = Fin.last k
  · refine ⟨(1 - η (Fin.last k))⁻¹ * t, Subring.mul_mem _ (inv_one_sub_mem hv) ht, ?_⟩
    simp [rowM, hi, e]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    simp [rowM, hi]

theorem modulus_det_eq_one {m : ℕ} (h : GL (Fin m) F)
    (h₁ : ∀ a b, (h : Matrix (Fin m) (Fin m) F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a b ∈ 𝒪[F]) :
    Measures.modulus (h : Matrix (Fin m) (Fin m) F).det = 1 := by
  have := Measures.distribHaarChar_glEquiv_eq_one h₁ h₂
  rw [Measures.distribHaarChar_glEquiv] at this
  rw [show (h : Matrix (Fin m) (Fin m) F).det = ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) from rfl,
    Measures.modulus_units]
  exact this

theorem image_lat {m M : ℕ} (h : GL (Fin m) F)
    (h₁ : ∀ a b, (h : Matrix (Fin m) (Fin m) F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a b ∈ 𝒪[F]) :
    (fun x => (h : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m M = lat F m M := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mulVec_mem_lat h₁ hx
  · refine ⟨((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x, mulVec_mem_lat h₂ hx, ?_⟩
    show (h : Matrix (Fin m) (Fin m) F) *ᵥ (((h⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

def g0 (m c : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F) ^ (c + 1))⁻¹ • 1
  inv := ((uniformizer F : F) ^ (c + 1)) • 1
  val_inv := by
    have : (uniformizer F : F) ^ (c + 1) ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero F)
    rw [smul_mul_smul_comm, inv_mul_cancel₀ this, one_mul, one_smul]
  inv_val := by
    have : (uniformizer F : F) ^ (c + 1) ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero F)
    rw [smul_mul_smul_comm, mul_inv_cancel₀ this, one_mul, one_smul]

theorem g0_div (m c : ℕ) :
    Div (c + 1) (((g0 m c : GL (Fin m) F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  intro i j
  refine ⟨(1 : Matrix (Fin m) (Fin m) F) i j, one_apply_mem i j, ?_⟩
  show (((uniformizer F : F) ^ (c + 1)) • (1 : Matrix (Fin m) (Fin m) F)) i j = _
  rw [Matrix.smul_apply, smul_eq_mul]

theorem g0_image (m c : ℕ) :
    (fun x => ((g0 m c : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 =
      lat F m (c + 1) := by
  have hϖ : (uniformizer F : F) ^ (c + 1) ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero F)
  have hg : ∀ x : Fin m → F, ((g0 m c : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x =
      ((uniformizer F : F) ^ (c + 1))⁻¹ • x := fun x => by
    show (((uniformizer F : F) ^ (c + 1))⁻¹ • (1 : Matrix (Fin m) (Fin m) F)) *ᵥ x = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  ext x
  simp only [Set.mem_image, hg]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    rw [pow_zero, one_mul] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hϖ]
    exact this
  · intro hx
    refine ⟨((uniformizer F : F) ^ (c + 1)) • x, fun i => ?_, ?_⟩
    · rw [pow_zero, one_mul]
      exact hx i
    · rw [smul_smul, inv_mul_cancel₀ hϖ, one_smul]

theorem continuous_of_periodic {m c' : ℕ} {f : (Fin m → F) → ℂ}
    (hf : ∀ x y, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c' * t) → f (x + y) = f x) :
    Continuous f := by
  have hϖ : (uniformizer F : F) ^ c' ≠ 0 := pow_ne_zero _ (uniformizer_ne_zero F)
  have hU : IsOpen ((fun y : Fin m → F => ((uniformizer F : F) ^ c')⁻¹ • y) ⁻¹'
      Measures.box F (Fin m)) :=
    Measures.isOpen_box.preimage (continuous_const_smul _)
  refine (IsLocallyConstant.iff_eventually_eq f |>.2 fun x => ?_).continuous
  have h0 : ((fun y : Fin m → F => ((uniformizer F : F) ^ c')⁻¹ • y) ⁻¹'
      Measures.box F (Fin m)) ∈ nhds (0 : Fin m → F) :=
    hU.mem_nhds (by simpa using Measures.zero_mem_box)
  have h1 : Filter.Tendsto (fun z : Fin m → F => z - x) (nhds x) (nhds 0) := by
    have : Continuous fun z : Fin m → F => z - x := continuous_id.sub continuous_const
    simpa using this.tendsto x
  filter_upwards [h1 h0] with z hz
  have hz' := hf x (z - x) fun i => ⟨((uniformizer F : F) ^ c')⁻¹ * (z - x) i,
    Measures.mem_box.1 hz i, by rw [mul_inv_cancel_left₀ hϖ]⟩
  rw [add_sub_cancel] at hz'
  exact hz'

section Integrals

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_image_eq (hL0 : L0) (hL1 : L1) (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : PsiOK ψ) {k c : ℕ} {f : (Fin (k + 1) → F) → ℂ} (hfc : Continuous f)
    (hf : ∀ h : GL (Fin (k + 1)) F, Div (c + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
      ∀ x, f ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) = f x)
    (g : GL (Fin (k + 1)) F)
    (hg : Div (c + 1) ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F))
    {M : ℕ}
    (hM : (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 ⊆
      lat F (k + 1) M) :
    ∫ x in (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0,
        ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ) =
      ∫ x in lat F (k + 1) M, ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ) := by
  haveI := Measures.sigmaCompactSpace F
  obtain ⟨hψc, hlat⟩ := hL0 F μ ψ hψ
  obtain ⟨hlat', hcv⟩ := hlat (k + 1)
  have hL1' := hL1 F μ ψ hψ (k + 1)
  set ν : Measure (Fin (k + 1) → F) := Measure.pi fun _ => μ with hν
  set G : (Fin (k + 1) → F) → ℂ := fun x => ψ (-x (Fin.last k)) * f x with hG
  set S := (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 with hSdef
  set gi : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
    ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) with hgi
  have hGc : Continuous G :=
    (hψc.comp (continuous_apply _).neg).mul hfc
  set Φ : (Fin (k + 1) → F) → (Fin (k + 1) → F) → ℂ := fun x ξ => ψ (ξ ⬝ᵥ (gi *ᵥ x)) * G x with hΦ
  have hgg : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * gi = 1 := by
    rw [hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : gi * (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = 1 := by
    rw [hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmemS : ∀ x, x ∈ S ↔ ∀ i, (gi *ᵥ x) i ∈ 𝒪[F] := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      have := hy i
      rw [pow_zero, one_mul] at this
      show (gi *ᵥ ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ y)) i ∈ 𝒪[F]
      rwa [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
    · intro h
      refine ⟨gi *ᵥ x, fun i => ?_, ?_⟩
      · rw [pow_zero, one_mul]
        exact h i
      · show (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ (gi *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hgic : Continuous fun x : Fin (k + 1) → F => gi *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hS : MeasurableSet S := by
    have : S = (fun x => gi *ᵥ x) ⁻¹' lat F (k + 1) 0 := by
      ext x
      rw [hmemS]
      simp [lat]
    rw [this]
    exact hgic.measurable (hlat' 0).2.2.1
  have hA := (hlat' 0).2.2.1
  have hB := (hlat' M).2.2.1
  set vol : ℝ := ν.real (lat F (k + 1) 0) with hvol
  have hvolpos : 0 < vol := (hlat' 0).2.2.2
  have h1 : ∀ x, ∫ ξ in lat F (k + 1) 0, Φ x ξ ∂ν = S.indicator (fun x => (vol : ℂ) * G x) x := by
    intro x
    simp only [hΦ]
    rw [integral_mul_const, hL1' (gi *ᵥ x)]
    by_cases hx : x ∈ S
    · rw [if_pos ((hmemS x).1 hx), Set.indicator_of_mem hx]
    · rw [if_neg (fun h => hx ((hmemS x).2 h)), Set.indicator_of_notMem hx, zero_mul]
  have h2 : ∫ x in lat F (k + 1) M, ∫ ξ in lat F (k + 1) 0, Φ x ξ ∂ν ∂ν =
      (vol : ℂ) * ∫ x in S, G x ∂ν := by
    simp_rw [h1]
    rw [setIntegral_indicator hS, Set.inter_eq_right.2 hM, integral_const_mul]
  have hΦc : Continuous (Function.uncurry Φ) := by
    refine (hψc.comp (Continuous.dotProduct continuous_snd
      (Continuous.matrix_mulVec continuous_const continuous_fst))).mul (hGc.comp continuous_fst)
  have hint : Integrable (Function.uncurry Φ) ((ν.restrict (lat F (k + 1) M)).prod
      (ν.restrict (lat F (k + 1) 0))) := by
    rw [Measure.prod_restrict]
    exact hΦc.continuousOn.integrableOn_compact ((hlat' M).1.prod (hlat' 0).1)
  have h3 := integral_integral_swap hint
  have h4 : ∀ ξ ∈ lat F (k + 1) 0, ∫ x in lat F (k + 1) M, Φ x ξ ∂ν =
      ∫ x in lat F (k + 1) M, G x ∂ν := by
    intro ξ hξ
    set η : Fin (k + 1) → F := ξ ᵥ* gi with hηdef
    have hη : ∀ j, ∃ t ∈ 𝒪[F], η j = (uniformizer F : F) ^ (c + 1) * t := by
      intro j
      choose y hy e using hg
      refine ⟨∑ i, ξ i * y i j, Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (hy i j), ?_⟩
      · have := hξ i
        rwa [pow_zero, one_mul] at this
      · rw [Finset.mul_sum]
        simp only [hηdef, Matrix.vecMul, dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show gi i j = _ from e i j]
        ring
    have hv : ValuativeRel.valuation F (η (Fin.last k)) < 1 := by
      obtain ⟨t, ht, e⟩ := hη (Fin.last k)
      exact valuation_lt_one_of_div ht e
    have hu := one_sub_ne_zero hv
    have hd := hGL_div hη hu
    have hd' := hGL_inv_div hη hv hu
    have h₁ := mem_of_div_sub_one hd
    have h₂ := mem_of_div_sub_one hd'
    have hc := hcv (hGL η hu) (lat F (k + 1) M) G hB
    rw [image_lat _ h₁ h₂, modulus_det_eq_one _ h₁ h₂] at hc
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul] at hc
    rw [hc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ x ξ = G _
    simp only [hΦ, hG]
    rw [hf _ hd, hGL_mulVec_last, ← mul_assoc, ← AddChar.map_add_eq_mul, Matrix.dotProduct_mulVec]
    congr 2
    ring
  have h5 : ∫ ξ in lat F (k + 1) 0, ∫ x in lat F (k + 1) M, Φ x ξ ∂ν ∂ν =
      (vol : ℂ) * ∫ x in lat F (k + 1) M, G x ∂ν := by
    rw [setIntegral_congr_fun hA h4, setIntegral_const, Complex.real_smul]
  have hne : (vol : ℂ) ≠ 0 := by exact_mod_cast hvolpos.ne'
  exact mul_left_cancel₀ hne (h2.symm.trans (h3.trans h5))

end Integrals

theorem stability : L0 → L1 → L2 := by
  intro hL0 hL1 F _ _ _ _ _ _ μ _ ψ hψ k c c' f hf₁ hf₂ g hg
  have hfc : Continuous f := continuous_of_periodic hf₁
  have hcomp := ((hL0 F μ ψ hψ).2 (k + 1)).1
  have himg : IsCompact ((fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) ''
      lat F (k + 1) 0) :=
    (hcomp 0).1.image (Continuous.matrix_mulVec continuous_const continuous_id)
  obtain ⟨M₁, hM₁⟩ : ∃ M, (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) ''
      lat F (k + 1) 0 ⊆ lat F (k + 1) M := by
    refine himg.elim_directed_cover (fun M => lat F (k + 1) M) (fun M => (hcomp M).2.1) ?_
      (directed_of_isDirected_le fun _ _ h => lat_mono h)
    intro x _
    exact Set.mem_iUnion.2 (exists_mem_lat x)
  rw [integral_image_eq hL0 hL1 μ ψ hψ hfc hf₂ g hg
      (hM₁.trans (lat_mono (le_max_left M₁ (c + 1)))),
    ← g0_image (k + 1) c,
    integral_image_eq hL0 hL1 μ ψ hψ hfc hf₂ (g0 (k + 1) c) (g0_div (k + 1) c)
      (M := max M₁ (c + 1))
      ((g0_image (k + 1) c).subset.trans (lat_mono (le_max_right M₁ (c + 1))))]

end GlobalTheory.CompanionTheory.SatakeBound.LargeLattice

end
