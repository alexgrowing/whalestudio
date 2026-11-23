import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

abbrev L : Type := FractionRing (MvPolynomial (Fin 2) ℚ)

def xL (i : Fin 2) : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X i)

theorem xL_ne_zero (i : Fin 2) : xL i ≠ 0 := by
  unfold xL
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact X_ne_zero i

theorem transcendental_div {i j : Fin 2} (hij : i ≠ j) : Transcendental ℚ (xL i / xL j) := by
  rw [transcendental_iff_injective, injective_iff_map_eq_zero]
  intro p hp
  set n := p.natDegree
  set Q : MvPolynomial (Fin 2) ℚ :=
    ∑ k ∈ Finset.range (n + 1), C (p.coeff k) * X i ^ k * X j ^ (n - k) with hQdef
  have hQ : algebraMap _ L Q = xL j ^ n * Polynomial.aeval (xL i / xL j) p := by
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, hQdef, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : xL j ^ n = xL j ^ (n - k) * xL j ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [map_mul, map_mul, map_pow, map_pow, hpow, Algebra.smul_def, div_pow]
    rw [show algebraMap (MvPolynomial (Fin 2) ℚ) L (C (p.coeff k)) = algebraMap ℚ L (p.coeff k) from
      (IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) L _).symm]
    have hj : xL j ^ k ≠ 0 := pow_ne_zero _ (xL_ne_zero j)
    change _ * xL i ^ k * xL j ^ (n - k) = _
    field_simp
  have hQ0 : Q = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) L
    rw [hQ, hp, mul_zero, map_zero]
  have hev : MvPolynomial.aeval (fun m : Fin 2 => if m = i then (Polynomial.X : Polynomial ℚ) else 1) Q = p := by
    conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
    rw [hQdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hij.symm, Polynomial.algebraMap_eq]
  rw [← hev, hQ0, map_zero]

def u : L := xL 1 / xL 0

abbrev Ω : Type := ↥(IntermediateField.adjoin ℚ ({u} : Set L))

def gen : Ω := IntermediateField.AdjoinSimple.gen ℚ u

theorem coe_gen : (gen : L) = u := rfl

theorem gen_ne_zero : gen ≠ 0 := by
  intro h
  have : (gen : L) = 0 := by rw [h]; rfl
  rw [coe_gen, u] at this
  exact div_ne_zero (xL_ne_zero 1) (xL_ne_zero 0) this

theorem transcendental_of_coe {a : Ω} (ha : Transcendental ℚ (a : L)) : Transcendental ℚ a := by
  rw [transcendental_iff_injective, injective_iff_map_eq_zero] at ha ⊢
  intro p hp
  apply ha p
  have := congrArg (IntermediateField.val _) hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at this
  exact this

theorem transcendental_gen : Transcendental ℚ gen :=
  transcendental_of_coe (by rw [coe_gen]; exact transcendental_div (by decide))

theorem transcendental_gen_inv : Transcendental ℚ gen⁻¹ := by
  refine transcendental_of_coe ?_
  rw [IntermediateField.coe_inv, coe_gen, u, inv_div]
  exact transcendental_div (by decide)

def yLine : (Σ _ : Unit, Fin 2) → Ω := fun p => if p.2 = 0 then 1 else gen

theorem yLine_zero : yLine ⟨(), 0⟩ = 1 := rfl

theorem yLine_one : yLine ⟨(), 1⟩ = gen := rfl

theorem yLine_ne_zero (p : Σ _ : Unit, Fin 2) : yLine p ≠ 0 := by
  unfold yLine
  split_ifs
  · exact one_ne_zero
  · exact gen_ne_zero

theorem mCoordIdeal_yLine : mCoordIdeal yLine = ⊥ := by
  let ψ : MvPolynomial Unit Ω →ₐ[Ω] L := MvPolynomial.aeval fun _ => xL 0
  let ρ : MRing (PBlk 2) →+* L := (algebraMap (MvPolynomial (Fin 2) ℚ) L).comp
    ((MvPolynomial.map (Int.castRingHom ℚ)).comp
      (rename (fun p : Σ _ : Unit, Fin 2 => p.2)).toRingHom)
  have hcomp : ψ.toRingHom.comp (mConeMap yLine).toRingHom = ρ := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rintro ⟨⟨⟩, i⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        mConeMap, aeval_X, map_mul, ψ, ρ, AlgHom.coe_toRingHom, rename_X, map_X]
      fin_cases i
      · simp [yLine, xL]
      · simp only [yLine]
        rw [if_neg (by decide), MvPolynomial.aeval_C]
        show (gen : L) * xL 0 = xL 1
        rw [coe_gen, u, div_mul_cancel₀ _ (xL_ne_zero 0)]
  have hinj : Function.Injective ρ := by
    refine (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) L).comp
      ((MvPolynomial.map_injective _ (RingHom.injective_int _)).comp (rename_injective _ ?_))
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only at h
    subst h
    rfl
  ext f
  simp only [Ideal.mem_bot]
  constructor
  · intro hf
    have h1 : mConeMap yLine f = 0 := hf
    apply hinj
    rw [map_zero, ← hcomp]
    simp [h1]
  · rintro rfl
    exact zero_mem _

theorem isArithVar_yLine : IsArithVar (mCoordIdeal yLine) 2 := by
  rw [mCoordIdeal_yLine]
  exact Inter.isArithVar_projLine

theorem isMultiHomog_X_line (i : Fin 2) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (PBlk 2)) (fun _ => 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  fin_cases i <;> simp [Finsupp.single_apply]

theorem birational_yLine : Birational yLine := by
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun _ => 1, X ⟨(), 1⟩, X ⟨(), 0⟩, isMultiHomog_X_line 1, isMultiHomog_X_line 0, ?_, ?_⟩
    · rw [aeval_X, yLine_zero]; exact one_ne_zero
    · rw [aeval_X, aeval_X, yLine_zero, yLine_one, mul_one]; rfl
  | algebraMap r =>
    refine ⟨0, C r.num, C (r.den : ℤ), isMultiHomog_C_zero _, isMultiHomog_C_zero _, ?_, ?_⟩
    · rw [aeval_C]; simp [r.den_nz]
    · rw [aeval_C, aeval_C]
      have : (⟨algebraMap ℚ L r, IntermediateField.algebraMap_mem _ r⟩ : Ω) = algebraMap ℚ Ω r := rfl
      rw [this, eq_intCast, eq_intCast, ← map_intCast (algebraMap ℚ Ω),
        ← map_intCast (algebraMap ℚ Ω), ← map_mul]
      congr 1
      push_cast
      exact (Rat.mul_den_eq_num r).symm
  | add x y hx hy ihx ihy =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := ihx
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ihy
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
      isMultiHomog_add (isMultiHomog_mul hg₁ hh₂) (by rw [add_comm]; exact isMultiHomog_mul hg₂ hh₁),
      isMultiHomog_mul hh₁ hh₂, by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : Ω) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, map_mul, map_mul, map_mul, e₁, e₂]
    ring
  | inv x hx ih =>
    obtain ⟨d, g, h, hg, hh, hy, e⟩ := ih
    have hinv : (⟨x⁻¹, inv_mem hx⟩ : Ω) = (⟨x, hx⟩ : Ω)⁻¹ := rfl
    by_cases h0 : (⟨x, hx⟩ : Ω) = 0
    · refine ⟨0, 0, 1, isMultiHomog_zero _, isMultiHomog_one, by simp, ?_⟩
      rw [hinv, h0, inv_zero, zero_mul, map_zero]
    · refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero h0 hy, ?_⟩
      rw [hinv, e]
      field_simp
  | mul x y hx hy ihx ihy =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := ihx
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ihy
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, isMultiHomog_mul hg₁ hg₂, isMultiHomog_mul hh₁ hh₂,
      by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
    have : (⟨x * y, mul_mem hx hy⟩ : Ω) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, map_mul, e₁, e₂]
    ring

theorem smooth_adjoin_of_transcendental {A : Type} [Field A] [Algebra ℚ A] {v : A}
    (hv : Transcendental ℚ v) (s : Set A) (hs : Algebra.adjoin ℚ s = Algebra.adjoin ℚ {v}) :
    Algebra.Smooth ℚ (Algebra.adjoin ℚ s) := by
  have : Algebra.Smooth ℚ (Polynomial ℚ) := {}
  have e2 : (Polynomial.aeval v).range = Algebra.adjoin ℚ s := by
    rw [hs, Algebra.adjoin_singleton_eq_range_aeval]
  exact Algebra.Smooth.of_equiv ((AlgEquiv.ofInjective (Polynomial.aeval v)
    (transcendental_iff_injective.mp hv)).trans (Subalgebra.equivOfEq _ _ e2))

theorem smoothGenericFibreM_yLine : SmoothGenericFibreM yLine := by
  intro c _
  obtain ⟨a, ha⟩ : ∃ a, c () = a := ⟨_, rfl⟩
  fin_cases a
  · refine smooth_adjoin_of_transcendental transcendental_gen _ (le_antisymm ?_ ?_)
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      simp only [Fin.zero_eta, Fin.isValue] at ha
      simp only [ha]
      fin_cases i
      · simp [yLine_zero]
      · simp only [Fin.mk_one, yLine_one, yLine_zero, div_one]
        exact Algebra.subset_adjoin rfl
    · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      refine Algebra.subset_adjoin ⟨⟨(), 1⟩, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue] at ha
      simp [ha, yLine_one, yLine_zero]
  · refine smooth_adjoin_of_transcendental transcendental_gen_inv _ (le_antisymm ?_ ?_)
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      simp only [Fin.mk_one, Fin.isValue] at ha
      simp only [ha]
      fin_cases i
      · simp only [Fin.zero_eta, yLine_one, yLine_zero, one_div]
        exact Algebra.subset_adjoin rfl
      · simp [yLine_one, div_self gen_ne_zero]
    · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      refine Algebra.subset_adjoin ⟨⟨(), 0⟩, ?_⟩
      simp only [Fin.mk_one, Fin.isValue] at ha
      simp [ha, yLine_one, yLine_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
