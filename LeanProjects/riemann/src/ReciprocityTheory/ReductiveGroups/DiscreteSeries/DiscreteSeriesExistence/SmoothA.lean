import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothBr

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace SmDerA

variable {n : ℕ}
theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  first
    | (unfold Jm
       rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
       congr 1
       funext a
       split_ifs <;> norm_num)
    | (ext i j
       by_cases h : i = j <;> by_cases hε : ε i <;> simp [Jm, Matrix.one_apply, h, hε])

theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  first
    | (unfold Jm
       rw [Matrix.diagonal_conjTranspose]
       congr 1
       funext a
       simp only [Pi.star_apply]
       split_ifs <;> simp)
    | (ext i j
       by_cases h : i = j <;> by_cases hε : ε i <;> simp [Jm, Matrix.diagonal_apply, h, hε])

private theorem Jm_mul_Jm_mulDiscreteSeriesExistence (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem J_conj_J_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem inG_of_J {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : Jm ε * Xᴴ * Jm ε = -X) :
    inG ε X := by
  show Xᴴ * Jm ε + Jm ε * X = 0
  have e : Xᴴ * Jm ε = Jm ε * (Jm ε * Xᴴ * Jm ε) := by
    simp only [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  rw [e, h, Matrix.mul_neg, neg_add_cancel]

theorem inG_add {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc _ = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
    _ = 0 := by rw [hX', hY', add_zero]

theorem inG_neg {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε (-X) := by
  show (-X)ᴴ * Jm ε + Jm ε * (-X) = 0
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX', neg_zero]

theorem inG_sub {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X - Y) := by
  rw [sub_eq_add_neg]
  exact inG_add hX (inG_neg hY)

theorem inG_zero (ε : Fin n → Bool) : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
  show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε + Jm ε * 0 = 0
  simp

theorem inG_rsmul {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (r : ℝ) :
    inG ε ((r : ℂ) • X) := by
  show ((r : ℂ) • X)ᴴ * Jm ε + Jm ε * ((r : ℂ) • X) = 0
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hs : star (r : ℂ) = r := Complex.conj_ofReal r
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero]

theorem inG_bracket {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X * Y - Y * X) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Jm ε * (A * B) * Jm ε = (Jm ε * A * Jm ε) * (Jm ε * B * Jm ε) := by
    intro A B
    simp only [Matrix.mul_assoc, Jm_mul_Jm_mulDiscreteSeriesExistence]
  apply inG_of_J
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_sub,
    Matrix.sub_mul, key, key, J_conj_J_of_inG hX, J_conj_J_of_inG hY]
  noncomm_ring

theorem inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (S7.cpart1 ε Z) := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    first | (rw [one_div, star_inv₀, star_ofNat]) | simp
  apply inG_of_J
  unfold S7.cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one, Jm_mul_Jm_mulDiscreteSeriesExistence, hs]
  module

theorem inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (S7.cpart2 ε Z) := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first
      | (rw [one_div, star_inv₀, star_mul', hI, star_ofNat, mul_neg, inv_neg])
      | simp [hI]
  apply inG_of_J
  unfold S7.cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one, Jm_mul_Jm_mulDiscreteSeriesExistence, hs]
  module

theorem cpart_decomp (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Z = S7.cpart1 ε Z + Complex.I • S7.cpart2 ε Z := by
  unfold S7.cpart1 S7.cpart2
  rw [smul_smul]
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    first | (field_simp; done) | (field_simp; ring)
  rw [h]
  module

theorem cpart1_of {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    S7.cpart1 ε (A + Complex.I • B) = A := by
  have eA := J_conj_J_of_inG hA
  have eB := J_conj_J_of_inG hB
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have e : Jm ε * (A + Complex.I • B)ᴴ * Jm ε = -A + Complex.I • B := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hI, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, eA, eB]
    module
  unfold S7.cpart1
  rw [e]
  module

theorem cpart2_of {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    S7.cpart2 ε (A + Complex.I • B) = B := by
  have eA := J_conj_J_of_inG hA
  have eB := J_conj_J_of_inG hB
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have e : Jm ε * (A + Complex.I • B)ᴴ * Jm ε = -A + Complex.I • B := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hI, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, eA, eB]
    module
  unfold S7.cpart2
  rw [e]
  have h2 : (A + Complex.I • B) + (-A + Complex.I • B) = (2 * Complex.I) • B := by module
  rw [h2, smul_smul, one_div_mul_cancel (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_smul]

section ActM

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)

theorem actM_add (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actM_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X - Y) = actM E X - actM E Y := by
  unfold actM
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem actM_single (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by
      simp [Matrix.single_apply, hx, Ne.symm hx]) (fun h => absurd (Finset.mem_univ a) h),
    Finset.sum_eq_single b (fun y _ hy => by simp [Matrix.single_apply, hy, Ne.symm hy])
      (fun h => absurd (Finset.mem_univ b) h)]
  simp [Matrix.single_apply]

end ActM

section Op

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

variable (ε σ) in

def smSub : Submodule ℂ H where
  carrier := {v | IsSmoothVecU ε σ v}
  add_mem' hv hw := IsSmoothVecU.add hv hw
  zero_mem' := isSmoothVecU_zero
  smul_mem' c _ hv := IsSmoothVecU.smul c hv

theorem dS_zero_mat (v : H) : dS σ 0 v = 0 := by
  simp [dS]

def dSlin (hσ : IsURepOn (UJset ε) σ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) :
    Module.End ℂ (smSub ε σ) where
  toFun v := ⟨dS σ X v, IsSmoothVecU.dS hσ hX v.2⟩
  map_add' v w := Subtype.ext (dS_add_vec hσ hX v.2 w.2)
  map_smul' c v := Subtype.ext (dS_smul_vec (σ := σ) c X (v : H))

open Classical in

def Tm (hσ : IsURepOn (UJset ε) σ) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (smSub ε σ) :=
  if h : inG ε X then dSlin hσ X h else 0

theorem Tm_apply (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : smSub ε σ) : ((Tm hσ X v : smSub ε σ) : H) = dS σ X v := by
  first
    | (simp only [Tm, dif_pos hX]; done)
    | (simp only [Tm, dif_pos hX]; rfl)
    | (rw [Tm, dif_pos hX]; rfl)

theorem Tm_add (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hY : inG ε Y) : Tm hσ (X + Y) = Tm hσ X + Tm hσ Y := by
  ext v
  rw [LinearMap.add_apply, Submodule.coe_add, Tm_apply hσ (inG_add hX hY), Tm_apply hσ hX, Tm_apply hσ hY]
  have := dS_add_smul hσ hX hY 1 v.2
  simpa using this

private theorem dS_real_smul (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) {v : H} (hv : IsSmoothVecU ε σ v) (r : ℝ) :
    dS σ ((r : ℂ) • X) v = (r : ℂ) • dS σ X v := by
  have hg' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dS σ X v) (r * 0) := by
    rw [mul_zero]
    exact hasDerivAt_dS hσ hX hv
  have hh : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have hc : HasDerivAt ((fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) ∘ (fun t : ℝ => r * t))
      (r • dS σ X v) 0 := by
    first | exact HasDerivAt.scomp (0 : ℝ) hg' hh | exact hg'.scomp hh | exact hg'.scomp (0 : ℝ) hh
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • ((r : ℂ) • X))) v) =
      (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) ∘ (fun t : ℝ => r * t) := by
    funext t
    simp only [Function.comp_apply]
    rw [smul_smul, mul_comm (t : ℂ), Complex.ofReal_mul]
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • ((r : ℂ) • X))) v) 0 = _
  rw [e, hc.deriv]
  first
    | exact (Complex.coe_smul r _).symm
    | exact RCLike.real_smul_eq_coe_smul (K := ℂ) r _
    | simp

theorem Tm_rsmul (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (r : ℝ) :
    Tm hσ ((r : ℂ) • X) = (r : ℂ) • Tm hσ X := by
  have hrX := inG_rsmul hX r
  refine LinearMap.ext fun v => Subtype.ext ?_
  exact (Tm_apply hσ hrX v).trans ((dS_real_smul hσ hX v.2 r).trans
    (congrArg (fun w => (r : ℂ) • w) (Tm_apply hσ hX v).symm))

theorem Tm_zero (hσ : IsURepOn (UJset ε) σ) : Tm hσ (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  exact (Tm_apply hσ (inG_zero ε) v).trans (dS_zero_mat _)

theorem Tm_sub (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hY : inG ε Y) : Tm hσ (X - Y) = Tm hσ X - Tm hσ Y := by
  have hY' : inG ε (((-1 : ℝ) : ℂ) • Y) := inG_rsmul hY (-1)
  have e : X - Y = X + ((-1 : ℝ) : ℂ) • Y := by
    rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_eq_add_neg]
  rw [e, Tm_add hσ hX hY', Tm_rsmul hσ hY, Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul,
    sub_eq_add_neg]

theorem Tm_br (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hY : inG ε Y) : Tm hσ X * Tm hσ Y - Tm hσ Y * Tm hσ X = Tm hσ (X * Y - Y * X) := by
  have hXY := inG_bracket hX hY
  refine LinearMap.ext fun v => Subtype.ext ?_
  show ((Tm hσ X (Tm hσ Y v) : smSub ε σ) : H) - ((Tm hσ Y (Tm hσ X v) : smSub ε σ) : H) =
    ((Tm hσ (X * Y - Y * X) v : smSub ε σ) : H)
  simp only [Tm_apply hσ hX, Tm_apply hσ hY, Tm_apply hσ hXY]
  exact dS_bracket hσ hX hY v.2

end Op

section Ec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def EcL (hσ : IsURepOn (UJset ε) σ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smSub ε σ) where
  toFun Z := Tm hσ (S7.cpart1 ε Z) + Complex.I • Tm hσ (S7.cpart2 ε Z)
  map_add' Z W := by
    have e : Z + W = (S7.cpart1 ε Z + S7.cpart1 ε W) + Complex.I • (S7.cpart2 ε Z + S7.cpart2 ε W) := by
      conv_lhs => rw [cpart_decomp ε Z, cpart_decomp ε W]
      module
    rw [e, cpart1_of (inG_add (inG_cpart1 ε Z) (inG_cpart1 ε W)) (inG_add (inG_cpart2 ε Z) (inG_cpart2 ε W)),
      cpart2_of (inG_add (inG_cpart1 ε Z) (inG_cpart1 ε W)) (inG_add (inG_cpart2 ε Z) (inG_cpart2 ε W)),
      Tm_add hσ (inG_cpart1 ε Z) (inG_cpart1 ε W), Tm_add hσ (inG_cpart2 ε Z) (inG_cpart2 ε W)]
    module
  map_smul' c Z := by
    obtain ⟨A, hA, B, hB, rfl⟩ : ∃ A, inG ε A ∧ ∃ B, inG ε B ∧ Z = A + Complex.I • B :=
      ⟨_, inG_cpart1 ε Z, _, inG_cpart2 ε Z, cpart_decomp ε Z⟩
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    have e : c • (A + Complex.I • B) =
        ((c.re : ℂ) • A - (c.im : ℂ) • B) + Complex.I • ((c.im : ℂ) • A + (c.re : ℂ) • B) := by
      conv_lhs => rw [hc]
      simp only [add_smul, smul_add, smul_smul, add_mul, mul_assoc, Complex.I_mul_I]
      module
    have h1 : inG ε ((c.re : ℂ) • A - (c.im : ℂ) • B) := inG_sub (inG_rsmul hA _) (inG_rsmul hB _)
    have h2 : inG ε ((c.im : ℂ) • A + (c.re : ℂ) • B) := inG_add (inG_rsmul hA _) (inG_rsmul hB _)
    simp only [RingHom.id_apply]
    rw [e, cpart1_of h1 h2, cpart2_of h1 h2, cpart1_of hA hB, cpart2_of hA hB,
      Tm_sub hσ (inG_rsmul hA _) (inG_rsmul hB _),
      Tm_add hσ (inG_rsmul hA _) (inG_rsmul hB _), Tm_rsmul hσ hA, Tm_rsmul hσ hB, Tm_rsmul hσ hA,
      Tm_rsmul hσ hB]
    conv_rhs => rw [hc]
    simp only [add_smul, smul_add, smul_smul, add_mul, mul_assoc, Complex.I_mul_I]
    module

theorem EcL_apply (hσ : IsURepOn (UJset ε) σ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcL hσ Z = Tm hσ (S7.cpart1 ε Z) + Complex.I • Tm hσ (S7.cpart2 ε Z) := rfl

theorem EcL_of (hσ : IsURepOn (UJset ε) σ) {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    EcL hσ (A + Complex.I • B) = Tm hσ A + Complex.I • Tm hσ B := by
  rw [EcL_apply, cpart1_of hA hB, cpart2_of hA hB]

theorem EcL_inG (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    EcL hσ X = Tm hσ X := by
  simpa [Tm_zero] using EcL_of hσ hX (inG_zero ε)

theorem EcL_br (hσ : IsURepOn (UJset ε) σ) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcL hσ Z * EcL hσ W - EcL hσ W * EcL hσ Z = EcL hσ (Z * W - W * Z) := by
  obtain ⟨A, hA, B, hB, rfl⟩ : ∃ A, inG ε A ∧ ∃ B, inG ε B ∧ Z = A + Complex.I • B :=
    ⟨_, inG_cpart1 ε Z, _, inG_cpart2 ε Z, cpart_decomp ε Z⟩
  obtain ⟨C, hC, D, hD, rfl⟩ : ∃ C, inG ε C ∧ ∃ D, inG ε D ∧ W = C + Complex.I • D :=
    ⟨_, inG_cpart1 ε W, _, inG_cpart2 ε W, cpart_decomp ε W⟩
  have hP : inG ε ((A * C - C * A) - (B * D - D * B)) :=
    inG_sub (inG_bracket hA hC) (inG_bracket hB hD)
  have hQ : inG ε ((A * D - D * A) + (B * C - C * B)) :=
    inG_add (inG_bracket hA hD) (inG_bracket hB hC)
  have e : (A + Complex.I • B) * (C + Complex.I • D) - (C + Complex.I • D) * (A + Complex.I • B) =
      ((A * C - C * A) - (B * D - D * B)) + Complex.I • ((A * D - D * A) + (B * C - C * B)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I]
    match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> ring_nf
  rw [e, EcL_of hσ hP hQ, EcL_of hσ hA hB, EcL_of hσ hC hD,
    Tm_sub hσ (inG_bracket hA hC) (inG_bracket hB hD), Tm_add hσ (inG_bracket hA hD) (inG_bracket hB hC),
    ← Tm_br hσ hA hC, ← Tm_br hσ hB hD, ← Tm_br hσ hA hD, ← Tm_br hσ hB hC]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> ring_nf

private theorem single_one_mul_single_one' (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single b
    (fun k _ hk => by simp [Matrix.single_apply, hk, Ne.symm hk])
    (fun h => absurd (Finset.mem_univ b) h)]
  by_cases hbc : b = c
  · subst hbc
    simp [Matrix.single_apply]
    split_ifs <;> simp_all
  · simp [Matrix.single_apply, hbc, Ne.symm hbc]

theorem EcL_glRep (hσ : IsURepOn (UJset ε) σ) :
    IsGlRep (fun a b : Fin n => EcL hσ (Matrix.single a b 1)) := by
  intro a b c d
  try dsimp only
  rw [EcL_br, single_one_mul_single_one', single_one_mul_single_one']
  split_ifs <;> simp

theorem actM_EcL (hσ : IsURepOn (UJset ε) σ) (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (fun a b : Fin n => EcL hσ (Matrix.single a b 1)) X = EcL hσ X := by
  have hX : X = ∑ a : Fin n, ∑ b : Fin n, X a b • Matrix.single a b (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i (fun k _ hk => Finset.sum_eq_zero fun l _ => by simp [hk, Ne.symm hk])
        (fun h => absurd (Finset.mem_univ i) h),
      Finset.sum_eq_single j (fun l _ hl => by simp [hl, Ne.symm hl])
        (fun h => absurd (Finset.mem_univ j) h)]
    simp
  unfold actM
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul]

end Ec

theorem inG_of_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0) :
    inG ε X := by
  show Xᴴ * Jm ε + Jm ε * X = 0
  ext i j
  simp only [Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply]
  exact h i j

theorem inG_casGen (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (casGen ε p) := by
  obtain ⟨a, b⟩ := p
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  apply inG_of_entry
  intro i j
  simp only [casGen, casSg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  rcases lt_trichotomy a b with hab | hab | hab <;>
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;> by_cases hbj : b = j <;>
  by_cases ha : ε a = true <;> by_cases hb : ε b = true <;>
  simp_all [hI, ne_of_lt, ne_of_gt, not_lt_of_gt] <;> ring_nf

section Cas

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)

theorem smulI_sq (u : Module.End ℂ M) : (Complex.I • u) * (Complex.I • u) = -(u * u) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]

theorem cas_pair_alg (x y : Module.End ℂ M) (s : ℂ) (hs : s = 1 ∨ s = -1) :
    -((1 / 2 * s) • ((x - s • y) * (x - s • y))) +
      -((1 / 2 * s) • ((Complex.I • (x + s • y)) * (Complex.I • (x + s • y)))) = x * y + y * x := by
  rw [smulI_sq]
  rcases hs with rfl | rfl <;>
  · simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
    module

theorem casSg_cases (ε : Fin n → Bool) (p : Fin n × Fin n) : casSg ε p = 1 ∨ casSg ε p = -1 := by
  unfold casSg
  split_ifs <;> simp

theorem cas_pair_lt (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    -((casWt (a, b) * casSg ε (a, b)) • (actM E (casGen ε (a, b)) * actM E (casGen ε (a, b)))) +
      -((casWt (b, a) * casSg ε (b, a)) • (actM E (casGen ε (b, a)) * actM E (casGen ε (b, a)))) =
      E a b * E b a + E b a * E a b := by
  have hne : a ≠ b := ne_of_lt hab
  have hnlt : ¬ b < a := not_lt.mpr hab.le
  have hsym : casSg ε (b, a) = casSg ε (a, b) := by
    unfold casSg
    by_cases h : ε a = ε b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hw1 : casWt (a, b) = 1 / 2 := by simp [casWt, hne]
  have hw2 : casWt (b, a) = 1 / 2 := by simp [casWt, Ne.symm hne]
  have hg1 : casGen ε (a, b) = Matrix.single a b 1 - casSg ε (a, b) • Matrix.single b a 1 := by
    simp [casGen, hne, hab]
  have hg2 : casGen ε (b, a) =
      Complex.I • (Matrix.single a b 1 + casSg ε (a, b) • Matrix.single b a 1) := by
    simp [casGen, Ne.symm hne, hnlt, hsym]
  rw [hw1, hw2, hsym, hg1, hg2]
  simp only [actM_sub, actM_smul, actM_add, actM_single]
  exact cas_pair_alg (E a b) (E b a) (casSg ε (a, b)) (casSg_cases ε (a, b))

theorem cas_pair (ε : Fin n → Bool) (p : Fin n × Fin n) :
    -((casWt p * casSg ε p) • (actM E (casGen ε p) * actM E (casGen ε p))) +
      -((casWt p.swap * casSg ε p.swap) • (actM E (casGen ε p.swap) * actM E (casGen ε p.swap))) =
      E p.1 p.2 * E p.2 p.1 + E p.2 p.1 * E p.1 p.2 := by
  obtain ⟨a, b⟩ := p
  rcases lt_trichotomy a b with h | rfl | h
  · exact cas_pair_lt E ε h
  · have hw : casWt (a, a) = 1 := by simp [casWt]
    have hs : casSg ε (a, a) = 1 := by simp [casSg]
    have hg : casGen ε (a, a) = Complex.I • Matrix.single a a 1 := by simp [casGen]
    simp only [Prod.swap_prod_mk, hw, hs, hg, actM_smul, actM_single, smulI_sq, one_mul, mul_one,
      one_smul, neg_neg]
  · have := cas_pair_lt E ε h
    simp only [Prod.swap_prod_mk]
    exact (add_comm _ _).trans (this.trans (add_comm _ _))

theorem casimir_eq (ε : Fin n → Bool) :
    casimir E = -∑ p : Fin n × Fin n, (casWt p * casSg ε p) • (actM E (casGen ε p) * actM E (casGen ε p)) := by
  have hsum : ∑ p : Fin n × Fin n,
      (-((casWt p * casSg ε p) • (actM E (casGen ε p) * actM E (casGen ε p))) +
        -((casWt p.swap * casSg ε p.swap) • (actM E (casGen ε p.swap) * actM E (casGen ε p.swap)))) =
      ∑ p : Fin n × Fin n, (E p.1 p.2 * E p.2 p.1 + E p.2 p.1 * E p.1 p.2) :=
    Finset.sum_congr rfl fun p _ => cas_pair E ε p
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hs1 : ∑ p : Fin n × Fin n, -((casWt p.swap * casSg ε p.swap) •
      (actM E (casGen ε p.swap) * actM E (casGen ε p.swap))) =
      ∑ p : Fin n × Fin n, -((casWt p * casSg ε p) • (actM E (casGen ε p) * actM E (casGen ε p))) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  have hs2 : ∑ p : Fin n × Fin n, E p.2 p.1 * E p.1 p.2 = ∑ p : Fin n × Fin n, E p.1 p.2 * E p.2 p.1 :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  rw [hs1, hs2] at hsum
  have hcas : casimir E = ∑ p : Fin n × Fin n, E p.1 p.2 * E p.2 p.1 :=
    (Fintype.sum_prod_type (fun p : Fin n × Fin n => E p.1 p.2 * E p.2 p.1)).symm
  rw [hcas, ← Finset.sum_neg_distrib]
  have h2 := congrArg (fun x : Module.End ℂ M => (2 : ℂ)⁻¹ • x) hsum
  simp only [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul] at h2
  exact h2.symm

end Cas

end SmDerA

end ReciprocityTheory.ChartRestriction.DS
