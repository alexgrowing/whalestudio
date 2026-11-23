import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.FlagFrame

variable {n : ℕ}

def stepIdx (i : Fin n) : Fin i ⊕ Unit → Fin n := Sum.elim (Fin.castLE i.2.le) fun _ => i

def stepIncl (i : Fin n) : Matrix (Fin n) (Fin i ⊕ Unit) ℂ :=
  of fun a b => if stepIdx i b = a then 1 else 0

theorem stepIdx_injective (i : Fin n) : Function.Injective (stepIdx i) := by
  rintro (a | a) (b | b) hab
  · exact congrArg _ (Fin.castLE_injective i.2.le hab)
  · exact absurd (congrArg Fin.val hab) a.2.ne
  · exact absurd (congrArg Fin.val hab) b.2.ne'
  · rfl

theorem stepIncl_gram (i : Fin n) (K : Matrix (Fin n) (Fin n) ℂ) :
    (stepIncl i)ᵀ * K * (stepIncl i)ᴴᵀ = stepGram K i := by
  ext b c
  simp [stepIncl, mul_apply, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases b with b | b <;> rcases c with c | c <;> rfl

theorem form_stepIncl (i : Fin n) (K : Matrix (Fin n) (Fin n) ℂ) (u w : Fin i ⊕ Unit → ℂ) :
    form K (stepIncl i *ᵥ u) (stepIncl i *ᵥ w) = form (stepGram K i) u w := by
  rw [form_mulVec, stepIncl_gram]; rfl

theorem posDef_stepGram {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) (i : Fin n) :
    (stepGram K i).PosDef := h.submatrix (stepIdx_injective i)

theorem isUnit_subGram_stepGram {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) (i : Fin n) :
    IsUnit (subGram (stepGram K i)).det :=
  (isUnit_iff_isUnit_det _).1 (posDef_subGram (posDef_stepGram h i)).isUnit

def gsVec (K : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin n → ℂ :=
  stepIncl i *ᵥ (orthLift (stepGram K i) *ᵥ fun _ => 1)

theorem form_gsVec_self {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) (i : Fin n) :
    form K (gsVec K i) (gsVec K i) = gradedGram K i () () := by
  rw [gsVec, form_stepIncl, form_orthLift (isUnit_subGram_stepGram h i), gradedGram]
  simp [form_eq_sum]

theorem stepIncl_single (i : Fin n) (j : Fin i) :
    stepIncl i *ᵥ (incl (Fin i) Unit *ᵥ Pi.single j 1) = Pi.single (Fin.castLE i.2.le j) 1 := by
  ext a
  simp [stepIncl, incl, mulVec, dotProduct, Pi.single_apply, stepIdx, Fintype.sum_sum_type,
    one_apply, eq_comm]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem form_gsVec_single {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) {i j : Fin n}
    (hj : j < i) : form K (gsVec K i) (Pi.single j 1) = 0 := by
  have : Pi.single j (1 : ℂ) = stepIncl i *ᵥ (incl (Fin i) Unit *ᵥ Pi.single ⟨j, hj⟩ 1) := by
    rw [stepIncl_single]; rfl
  rw [this, gsVec, form_stepIncl, form_orthLift_incl (isUnit_subGram_stepGram h i)]

theorem gsVec_eq_zero (K : Matrix (Fin n) (Fin n) ℂ) {i b : Fin n} (hb : i < b) :
    gsVec K i b = 0 := by
  simp only [gsVec, mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  have : stepIdx i c ≠ b := by
    rcases c with c | c
    · intro e; have := congrArg Fin.val e; simp [stepIdx] at this; omega
    · intro e; exact hb.ne e
  simp [stepIncl, this]

theorem form_expand (K : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    form K v w = ∑ b, form K v (Pi.single b 1) * conj (w b) := by
  simp only [form_eq_sum, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq', mul_ite]

theorem form_gsVec_lt {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) {k l : Fin n} (hlk : l < k) :
    form K (gsVec K k) (gsVec K l) = 0 := by
  rw [form_expand]
  refine Finset.sum_eq_zero fun b _ => ?_
  rcases lt_or_ge b k with hb | hb
  · rw [form_gsVec_single h hb, zero_mul]
  · rw [gsVec_eq_zero K (lt_of_lt_of_le hlk hb)]; simp

end GlobalTheory.FlagFrame

namespace GlobalTheory.FlagFrame

section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ}

theorem gradedGram_pos {K : Matrix (Fin n) (Fin n) ℂ} (h : K.PosDef) (i : Fin n) :
    0 < (gradedGram K i () ()).re ∧ (gradedGram K i () ()).im = 0 := by
  have := (posDef_iff.1 (posDef_gradedGram h i)).2 (fun _ => 1)
    (by intro e; simpa using congrFun e ())
  simp only [form_eq_sum, Finset.univ_unique, Finset.sum_singleton, one_mul, map_one,
    mul_one] at this
  exact ⟨(Complex.pos_iff.1 this).1, (Complex.pos_iff.1 this).2.symm⟩

theorem posDef_adaptedGram {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    {Y : Set E} {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : IsPosFrame U H) (hA : IsFlagFamily Y U π A) {y : E} (hy : y ∈ Y) :
    (adaptedGram H π A y).PosDef := by
  have hB : ((A y)ᴴᵀ)ᴴ = (A y)ᵀ := by ext a b; simp
  have hu : IsUnit (A y)ᴴᵀ := by
    rw [isUnit_iff_isUnit_det, det_transpose, det_conjTranspose]
    exact (hA.isUnit y hy).star
  have := (hH.posDef _ (hA.mapsTo hy)).conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hu)
  rwa [hB] at this

theorem form_adapted (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (y : E) (u w : Fin n → ℂ) :
    form (H (π y)) (A y *ᵥ u) (A y *ᵥ w) = form (adaptedGram H π A y) u w := by
  rw [form_mulVec]; rfl

theorem mContDiffAt_orthLift {m l : Type} [Fintype m] [DecidableEq m] [Fintype l]
    [DecidableEq l] {S : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {y : E} {k : WithTop ℕ∞}
    (h : MContDiffAt k S y) (hu : IsUnit (subGram (S y)).det) :
    MContDiffAt k (fun x => orthLift (S x)) y := by
  have hc : MContDiffAt k (fun x => orthCoeff (S x)) y := by
    show MContDiffAt k (fun x => ((S x).submatrix Sum.inl Sum.inl)ᵀ⁻¹ *
      ((S x).submatrix Sum.inr Sum.inl)ᵀ) y
    exact ((h.submatrix Sum.inl Sum.inl).transpose.inv (by rw [det_transpose]; exact hu)).mul
      (h.submatrix Sum.inr Sum.inl).transpose
  rintro (a | a) b
  · exact (hc a b).neg
  · exact contDiffAt_const

theorem mContDiffAt_quotGram {m l : Type} [Fintype m] [DecidableEq m] [Fintype l]
    [DecidableEq l] {S : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {y : E} {k : WithTop ℕ∞}
    (h : MContDiffAt k S y) (hu : IsUnit (subGram (S y)).det) :
    MContDiffAt k (fun x => quotGram (S x)) y := by
  show MContDiffAt k (fun x => (S x).submatrix Sum.inr Sum.inr -
    (S x).submatrix Sum.inr Sum.inl * ((S x).submatrix Sum.inl Sum.inl)⁻¹ *
      (S x).submatrix Sum.inl Sum.inr) y
  exact (h.submatrix _ _).sub (((h.submatrix _ _).mul ((h.submatrix _ _).inv hu)).mul
    (h.submatrix _ _))

def gsFrame (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (y : E) : Matrix (Fin n) (Fin n) ℂ :=
  of fun a i => (((√(gradedGram (adaptedGram H π A y) i () ()).re)⁻¹ : ℝ) : ℂ) *
    (A y *ᵥ gsVec (adaptedGram H π A y) i) a

theorem gsFrame_col (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (y : E) (i : Fin n) :
    (fun a => gsFrame H π A y a i) =
      (((√(gradedGram (adaptedGram H π A y) i () ()).re)⁻¹ : ℝ) : ℂ) •
        (A y *ᵥ gsVec (adaptedGram H π A y) i) := by
  ext a; rfl

theorem isUnitaryFlagFrame_gsFrame {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ}
    {Y : Set E} {π : E → ι → ℂ} {A : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : IsPosFrame U H) (hA : IsFlagFamily Y U π A) :
    IsUnitaryFlagFrame Y H π A (gsFrame H π A) := by
  have hAd : ∀ y ∈ Y, MContDiffAt ∞ A y := fun y hy a b =>
    ((hA.hol_frame a b).restrict_scalars ℝ).contDiffAt (hA.isOpen.mem_nhds hy)
  have hHπ : ∀ y ∈ Y, MContDiffAt ∞ (fun x => H (π x)) y := fun y hy a b =>
    ((hH.smooth a b).contDiffAt (hH.isOpen.mem_nhds (hA.mapsTo hy))).comp y
      ((hA.hol_proj.restrict_scalars ℝ).contDiffAt (hA.isOpen.mem_nhds hy))
  have hG : ∀ y ∈ Y, MContDiffAt ∞ (adaptedGram H π A) y := fun y hy =>
    ((hAd y hy).transpose.mul (hHπ y hy)).mul (hAd y hy).conjTranspose.transpose
  have hS : ∀ y ∈ Y, ∀ i : Fin n,
      MContDiffAt ∞ (fun x => stepGram (adaptedGram H π A x) i) y :=
    fun y hy i => (hG y hy).submatrix _ _
  have hE : ∀ y ∈ Y, ∀ a i, ContDiffAt ℝ ∞ (fun x => gsFrame H π A x a i) y := by
    intro y hy a i
    have hP := posDef_adaptedGram hH hA hy
    have hu := isUnit_subGram_stepGram hP i
    have hL := mContDiffAt_orthLift (hS y hy i) hu
    have hw : ∀ b, ContDiffAt ℝ ∞ (fun x => gsVec (adaptedGram H π A x) i b) y := fun b => by
      simp only [gsVec, mulVec, dotProduct]
      exact ContDiffAt.sum fun c _ => contDiffAt_const.mul
        (ContDiffAt.sum fun u _ => (hL c u).mul contDiffAt_const)
    have hq : ContDiffAt ℝ ∞ (fun x => gradedGram (adaptedGram H π A x) i () ()) y :=
      mContDiffAt_quotGram (hS y hy i) hu () ()
    have hre : ContDiffAt ℝ ∞ (fun x => (gradedGram (adaptedGram H π A x) i () ()).re) y :=
      reCLM.contDiff.contDiffAt.comp y hq
    have hpos := (gradedGram_pos hP i).1
    have hd : ContDiffAt ℝ ∞
        (fun x => (((√(gradedGram (adaptedGram H π A x) i () ()).re)⁻¹ : ℝ) : ℂ)) y :=
      ofRealCLM.contDiff.contDiffAt.comp y
        ((hre.sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne')
    simp only [gsFrame, of_apply, mulVec, dotProduct]
    exact hd.mul (ContDiffAt.sum fun b _ => (hAd y hy a b).mul (hw b))
  refine ⟨fun a b y hy => (hE y hy a b).contDiffWithinAt, fun y hy k l => ?_,
    fun y hy i => ?_, fun y hy i j hji => ?_⟩
  · have hP := posDef_adaptedGram hH hA hy
    rw [gsFrame_col, gsFrame_col, form_smul_left, form_smul_right, form_adapted]
    split_ifs with hkl
    · subst hkl
      rw [form_gsVec_self hP]
      obtain ⟨hpos, him⟩ := gradedGram_pos hP k
      set g := gradedGram (adaptedGram H π A y) k () ()
      set r := g.re
      have hge : g = (r : ℂ) := Complex.ext rfl (by simp [him])
      rw [conj_ofReal, hge, ← ofReal_mul, ← ofReal_mul]
      have : (√r)⁻¹ * ((√r)⁻¹ * r) = 1 := by
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
      exact_mod_cast this
    · rcases lt_or_gt_of_ne hkl with h | h
      · rw [← conj_form hP.isHermitian, form_gsVec_lt hP h, map_zero, mul_zero, mul_zero]
      · rw [form_gsVec_lt hP h, mul_zero, mul_zero]
  · rw [gsFrame_col]
    refine Submodule.smul_mem _ _ ?_
    have : A y *ᵥ gsVec (adaptedGram H π A y) i =
        ∑ b, gsVec (adaptedGram H π A y) i b • fun a => A y a b := by
      ext a; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    refine Submodule.sum_mem _ fun b _ => ?_
    rcases le_or_gt b i with hb | hb
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [gsVec_eq_zero _ hb, zero_smul]; exact Submodule.zero_mem _
  · have hP := posDef_adaptedGram hH hA hy
    have hc : (fun a => A y a j) = A y *ᵥ Pi.single j 1 := by rw [mulVec_single_one]; rfl
    rw [gsFrame_col, form_smul_left, hc, form_adapted, form_gsVec_single hP hji, mul_zero]

theorem exists_unitaryFlagFrame :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → ∃ e, IsUnitaryFlagFrame Y H π A e :=
  by
  intro E _ _ _ _ _ ι _ n U H Y π A hH hA
  exact ⟨_, isUnitaryFlagFrame_gsFrame hH hA⟩

end Main

end GlobalTheory.FlagFrame
