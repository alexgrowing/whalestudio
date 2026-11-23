import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCCB

noncomputable section

open Matrix
open scoped ContDiff ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma CkOn_Lw (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) (m : ℕ) {f : Mat k r → ℂ}
    (hf : CkOn ((m + q.length : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (q.foldr LdV f) := by
  induction q generalizing m with
  | nil => simpa using hf
  | cons X q ih =>
    rw [List.foldr_cons]
    have hq' : ∀ Y ∈ q, inLie k r Y := fun Y hY => hq Y (List.mem_cons_of_mem X hY)
    have h1 : CkOn ((m + 1 + q.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : m + 1 + q.length = m + (X :: q).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact CkOn_LdV (ih hq' (m + 1) h1) (hq X (by simp))

lemma CkOn_Rw (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) (m : ℕ) {f : Mat k r → ℂ}
    (hf : CkOn ((m + q.length : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (q.foldr RdV f) := by
  induction q generalizing m with
  | nil => simpa using hf
  | cons X q ih =>
    rw [List.foldr_cons]
    have hq' : ∀ Y ∈ q, inLie k r Y := fun Y hY => hq Y (List.mem_cons_of_mem X hY)
    have h1 : CkOn ((m + 1 + q.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : m + 1 + q.length = m + (X :: q).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact CkOn_RdV (ih hq' (m + 1) h1) (hq X (by simp))

lemma Lw_congr (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) {f₁ f₂ : Mat k r → ℂ}
    (h : ∀ g ∈ GV k r, f₁ g = f₂ g) : ∀ g ∈ GV k r, q.foldr LdV f₁ g = q.foldr LdV f₂ g := by
  induction q with
  | nil => simpa using h
  | cons X q ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    exact LdV_congr (ih (fun Y hY => hq Y (List.mem_cons_of_mem X hY))) (hq X (by simp)) hg

lemma Rw_congr (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) {f₁ f₂ : Mat k r → ℂ}
    (h : ∀ g ∈ GV k r, f₁ g = f₂ g) : ∀ g ∈ GV k r, q.foldr RdV f₁ g = q.foldr RdV f₂ g := by
  induction q with
  | nil => simpa using h
  | cons X q ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    exact RdV_congr (ih (fun Y hY => hq Y (List.mem_cons_of_mem X hY))) (hq X (by simp)) hg

lemma comm1 (Y : Mat k r) (hY : inLie k r Y) (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X)
    (f : Mat k r → ℂ) (hf : CkOn ((q.length + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, RdV Y (q.foldr LdV f) g = q.foldr LdV (RdV Y f) g := by
  induction q with
  | nil => intro g _; rfl
  | cons X q ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    have hq' : ∀ Z ∈ q, inLie k r Z := fun Z hZ => hq Z (List.mem_cons_of_mem X hZ)
    have h2 : CkOn ((2 : ℕ) : ℕ∞) (GV k r) (q.foldr LdV f) := by
      apply CkOn_Lw q hq' 2
      have e : 2 + q.length = (X :: q).length + 1 := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    rw [← LR_comm h2 (hq X (by simp)) hY hg]
    exact LdV_congr (ih hq' (CkOn_mono (by simp only [List.length_cons]; omega) hf)) (hq X (by simp)) hg

lemma comm (p q : List (Mat k r)) (hp : ∀ X ∈ p, inLie k r X) (hq : ∀ X ∈ q, inLie k r X)
    (f : Mat k r → ℂ) (hf : CkOn ((p.length + q.length : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, p.foldr RdV (q.foldr LdV f) g = q.foldr LdV (p.foldr RdV f) g := by
  induction p with
  | nil => intro g _; rfl
  | cons Y p ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    have hp' : ∀ Z ∈ p, inLie k r Z := fun Z hZ => hp Z (List.mem_cons_of_mem Y hZ)
    rw [RdV_congr (ih hp' (CkOn_mono (by simp only [List.length_cons]; omega) hf)) (hp Y (by simp)) hg]
    apply comm1 Y (hp Y (by simp)) q hq (p.foldr RdV f) _ g hg
    apply CkOn_Rw p hp' (q.length + 1)
    have e : q.length + 1 + p.length = (Y :: p).length + q.length := by simp only [List.length_cons]; omega
    rw [e]; exact hf

lemma LdV_rsmul (c : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : LdV ((c : ℂ) • X) f = c • LdV X f := by
  funext g
  simp only [LdV, Pi.smul_apply]
  have e : (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • ((c : ℂ) • X))) * g)) =
      fun t => (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X)) * g)) (c * t) := by
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm]
  rw [e]
  exact (deriv_comp_mul_left c (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X)) * g)) 0).trans
    (by rw [mul_zero])

lemma RdV_rsmul (c : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : RdV ((c : ℂ) • X) f = c • RdV X f := by
  funext g
  simp only [RdV, Pi.smul_apply]
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • ((c : ℂ) • X)))) =
      fun t => (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (c * t) := by
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm]
  rw [e]
  exact (deriv_comp_mul_left c (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) 0).trans
    (by rw [mul_zero])

lemma LdV_fsmul (a : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : LdV X (a • f) = a • LdV X f := by
  funext g
  simp only [LdV, Pi.smul_apply]
  exact deriv_const_smul_field (f := fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) a

lemma RdV_fsmul (a : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : RdV X (a • f) = a • RdV X f := by
  funext g
  simp only [RdV, Pi.smul_apply]
  exact deriv_const_smul_field (f := fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) a

lemma Lw_fsmul (a : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) : q.foldr LdV (a • f) = a • q.foldr LdV f := by
  induction q with
  | nil => rfl
  | cons X q ih => simp only [List.foldr_cons, ih, LdV_fsmul]

lemma Rw_fsmul (a : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) : q.foldr RdV (a • f) = a • q.foldr RdV f := by
  induction q with
  | nil => rfl
  | cons X q ih => simp only [List.foldr_cons, ih, RdV_fsmul]

lemma Lw_scale (c : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) :
    (q.map (fun X => (c : ℂ) • X)).foldr LdV f = c ^ q.length • q.foldr LdV f := by
  induction q with
  | nil => simp
  | cons X q ih =>
    simp only [List.map_cons, List.foldr_cons, ih, LdV_rsmul, LdV_fsmul, List.length_cons, smul_smul,
      pow_succ']
    rw [mul_comm (c ^ q.length) c]

lemma Rw_scale (c : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) :
    (q.map (fun X => (c : ℂ) • X)).foldr RdV f = c ^ q.length • q.foldr RdV f := by
  induction q with
  | nil => simp
  | cons X q ih =>
    simp only [List.map_cons, List.foldr_cons, ih, RdV_rsmul, RdV_fsmul, List.length_cons, smul_smul,
      pow_succ']
    rw [mul_comm (c ^ q.length) c]

section th

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det)
include hE

lemma LdV_th (f : Mat k r → ℂ) (X : Mat k r) : LdV X (f ∘ th k r γ) = RdV (gbar k r γ X) f ∘ th k r γ := by
  funext g
  simp only [Function.comp]
  unfold LdV RdV
  congr 1
  funext t
  rw [Function.comp_apply, th_mul hE, th_exp hE, gbar_neg, gbar_rsmul, neg_neg]

lemma RdV_th (f : Mat k r → ℂ) (X : Mat k r) : RdV X (f ∘ th k r γ) = LdV (gbar k r γ X) f ∘ th k r γ := by
  funext g
  simp only [Function.comp]
  unfold LdV RdV
  congr 1
  funext t
  rw [Function.comp_apply, th_mul hE, th_exp hE, gbar_rsmul]

lemma Rw_th (v : List (Mat k r)) (f : Mat k r → ℂ) :
    v.foldr RdV (f ∘ th k r γ) = (v.map (gbar k r γ)).foldr LdV f ∘ th k r γ := by
  induction v with
  | nil => rfl
  | cons X v ih => rw [List.foldr_cons, ih, RdV_th hE, List.map_cons, List.foldr_cons]

lemma Lw_th (u : List (Mat k r)) (f : Mat k r → ℂ) :
    u.foldr LdV (f ∘ th k r γ) = (u.map (gbar k r γ)).foldr RdV f ∘ th k r γ := by
  induction u with
  | nil => rfl
  | cons X u ih => rw [List.foldr_cons, ih, LdV_th hE, List.map_cons, List.foldr_cons]

end th

lemma norm_le_gN (A : Mat k r) : ‖A‖ ≤ gN A := by
  rw [Matrix.norm_le_iff (by unfold gN; exact Real.sqrt_nonneg _)]
  intro i j
  unfold gN
  calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := by
      apply Real.sqrt_le_sqrt
      rw [← Complex.normSq_eq_norm_sq]
      exact (Finset.single_le_sum (f := fun j => Complex.normSq (A i j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (A i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))

lemma gN_le_norm (A : Mat k r) : gN A ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ := by
  unfold gN
  have hN : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ := by positivity
  rw [← Real.sqrt_sq hN]
  apply Real.sqrt_le_sqrt
  have hij : ∀ i j, Complex.normSq (A i j) ≤ ‖A‖ ^ 2 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.norm_entry_le_entrywise_sup_norm A) 2
  calc ∑ i, ∑ j, Complex.normSq (A i j)
      ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), ‖A‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma gN_nonneg (A : Mat k r) : 0 ≤ gN A := by
  unfold gN
  exact Real.sqrt_nonneg _

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have hne : g ≠ 0 := by
    rintro rfl
    have h := isUnit_of_uh hg
    rw [Matrix.det_zero] at h
    exact not_isUnit_zero h
  exact lt_of_lt_of_le (norm_pos_iff.mpr hne) (norm_le_gN g)

lemma lin_bound (T : Mat k r →ₗ[ℝ] Mat k r) : ∃ C, ∀ z, ‖T z‖ ≤ C * ‖z‖ := by
  obtain ⟨C, -, hC⟩ := (LinearMap.toContinuousLinearMap T).isBoundedLinearMap.bound
  exact ⟨C, fun z => hC z⟩

lemma rpow_cmp {x y C A : ℝ} (hx : 0 < x) (hy : 0 < y) (hC : 1 ≤ C) (h1 : x ≤ C * y) (h2 : y ≤ C * x) :
    x ^ A ≤ C ^ |A| * y ^ A := by
  have hC0 : 0 < C := by linarith
  rcases le_or_gt 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hC0.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · rw [abs_of_neg hA]
    have h3 : y / C ≤ x := by
      rw [div_le_iff₀ hC0]
      linarith
    have hpos : 0 < (y / C) ^ (-A) := Real.rpow_pos_of_pos (div_pos hy hC0) _
    have key : (y / C) ^ (-A) ≤ x ^ (-A) := Real.rpow_le_rpow (div_pos hy hC0).le h3 (by linarith)
    calc x ^ A = (x ^ (-A))⁻¹ := by rw [← Real.rpow_neg hx.le, neg_neg]
      _ ≤ ((y / C) ^ (-A))⁻¹ := inv_anti₀ hpos key
      _ = C ^ (-A) * y ^ A := by
        rw [← Real.rpow_neg (div_pos hy hC0).le, neg_neg, Real.div_rpow hy.le hC0.le,
          Real.rpow_neg hC0.le]
        ring

def gbarL (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r →ₗ[ℝ] Mat k r where
  toFun := gbar k r γ
  map_add' := gbar_add
  map_smul' := by
    intro c A
    have e1 : c • A = (c : ℂ) • A := (Complex.coe_smul c A).symm
    rw [RingHom.id_apply, e1, gbar_rsmul, Complex.coe_smul]

def TL (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r →ₗ[ℝ] Mat k r where
  toFun A := Hpk k r * (gbar k r γ A)ᴴ * Hpk k r
  map_add' := by
    intro A B
    show Hpk k r * (gbar k r γ (A + B))ᴴ * Hpk k r =
      Hpk k r * (gbar k r γ A)ᴴ * Hpk k r + Hpk k r * (gbar k r γ B)ᴴ * Hpk k r
    rw [gbar_add, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c A
    show Hpk k r * (gbar k r γ (c • A))ᴴ * Hpk k r = c • (Hpk k r * (gbar k r γ A)ᴴ * Hpk k r)
    have e1 : c • A = (c : ℂ) • A := (Complex.coe_smul c A).symm
    rw [e1, gbar_rsmul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mul_smul,
      Matrix.smul_mul, Complex.coe_smul]

lemma TL_apply (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (A : Mat k r) :
    TL k r γ A = Hpk k r * (gbar k r γ A)ᴴ * Hpk k r := rfl

section main

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (hEG : embWb k r γ ∈ GV k r)
include hE hEG

lemma th_bound : ∃ C, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g := by
  obtain ⟨C, hC⟩ := lin_bound (TL k r γ)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * max C 0, fun g hg => ?_⟩
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  rw [th_eq hE hEG hg]
  calc gN (Hpk k r * (gbar k r γ g)ᴴ * Hpk k r) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖TL k r γ g‖ := gN_le_norm _
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (max C 0 * ‖g‖) :=
        mul_le_mul_of_nonneg_left ((hC g).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hn
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (max C 0 * gN g) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_le_gN g) (le_max_right _ _)) hn
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * max C 0 * gN g := by ring

lemma CkOn_th {m : ℕ} {F : Mat k r → ℂ} (hF : CkOn (m : ℕ∞) (GV k r) F) :
    CkOn (m : ℕ∞) (GV k r) (F ∘ th k r γ) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hF (th k r γ g₀) (th_mem hE hEG hg₀)
  have hT : Continuous (TL k r γ) := (TL k r γ).continuous_of_finiteDimensional
  refine ⟨(TL k r γ) ⁻¹' U, f' ∘ (TL k r γ), hU.preimage hT, ?_, ?_, ?_⟩
  · show TL k r γ g₀ ∈ U
    rw [TL_apply, ← th_eq hE hEG hg₀]
    exact h0
  · exact hc.comp ((LinearMap.toContinuousLinearMap (TL k r γ)).contDiff).contDiffOn (Set.mapsTo_preimage _ _)
  · intro g hgU hgG
    show F (th k r γ g) = f' (TL k r γ g)
    rw [TL_apply, ← th_eq hE hEG hgG]
    exact he _ (by rw [th_eq hE hEG hgG]; exact hgU) (th_mem hE hEG hgG)

end main

theorem main (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hγ : IsZFrame k r z γ) :
    (∃ C : ℝ, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g) ∧
    ∀ (A : ℝ) (m : ℕ) (F : Mat k r → ℂ), InCC A m F → InCC A m (F ∘ th k r γ) := by
  have hEG : embWb k r γ ∈ GV k r := emb_mem hγ.1
  have hE : IsUnit (embWb k r γ).det := isUnit_of_uh hEG
  refine ⟨th_bound hE hEG, ?_⟩
  rintro A m F ⟨c, hCk, hb⟩
  obtain ⟨C0, hC0⟩ := th_bound hE hEG
  obtain ⟨B, hB⟩ := lin_bound (gbarL k r γ)
  set C := max C0 1 with hCdef
  set M := max B 1 with hMdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hC0' : 0 < C := by linarith
  set Yb : Mat k r → Mat k r := fun X => ((M⁻¹ : ℝ) : ℂ) • gbar k r γ X with hYb
  have hgb : ∀ X, gbar k r γ X = ((M : ℝ) : ℂ) • Yb X := by
    intro X
    simp only [hYb, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hM0.ne', Complex.ofReal_one, one_smul]
  have hunit : ∀ X, unitLie k r X → unitLie k r (Yb X) := by
    intro X hX
    refine ⟨lie_rsmul _ (lie_gbar hE hEG hX.1), fun i j => ?_⟩
    have hXn : ‖X‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).mpr hX.2
    have h1 : ‖gbar k r γ X‖ ≤ M := by
      have := hB X
      calc ‖gbar k r γ X‖ = ‖gbarL k r γ X‖ := rfl
        _ ≤ B * ‖X‖ := this
        _ ≤ M * 1 := mul_le_mul (le_max_left _ _) hXn (norm_nonneg _) hM0.le
        _ = M := mul_one M
    simp only [hYb, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM0)]
    calc M⁻¹ * ‖gbar k r γ X i j‖ ≤ M⁻¹ * M :=
          mul_le_mul_of_nonneg_left ((Matrix.norm_entry_le_entrywise_sup_norm _).trans h1) (inv_pos.mpr hM0).le
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  refine ⟨M ^ m * C ^ |A| * max c 0, CkOn_th hE hEG hCk, ?_⟩
  intro u v hu hv hlen g hg
  have hthg := th_mem hE hEG hg
  have huY : ∀ X ∈ u.map Yb, unitLie k r X := by
    intro X hX; obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX; exact hunit Y (hu Y hY)
  have hvY : ∀ X ∈ v.map Yb, unitLie k r X := by
    intro X hX; obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX; exact hunit Y (hv Y hY)
  have eu : u.map (gbar k r γ) = (u.map Yb).map (fun X => ((M : ℝ) : ℂ) • X) := by
    rw [List.map_map]; exact List.map_congr_left (fun X _ => hgb X)
  have ev : v.map (gbar k r γ) = (v.map Yb).map (fun X => ((M : ℝ) : ℂ) • X) := by
    rw [List.map_map]; exact List.map_congr_left (fun X _ => hgb X)
  have hFk : CkOn (((u.map Yb).length + (v.map Yb).length : ℕ) : ℕ∞) (GV k r) F :=
    CkOn_mono (by simp only [List.length_map]; omega) hCk
  have key : dLR u v (F ∘ th k r γ) g =
      (M ^ (u.length + v.length) : ℝ) • dLR (v.map Yb) (u.map Yb) F (th k r γ g) := by
    unfold dLR Rw
    rw [Rw_th hE, Lw_th hE, eu, ev, Rw_scale, Lw_scale, Rw_fsmul, smul_smul, Function.comp_apply,
      Pi.smul_apply, comm _ _ (fun X hX => (huY X hX).1) (fun X hX => (hvY X hX).1) F hFk _ hthg,
      List.length_map, List.length_map, pow_add]
  have hD := hb (v.map Yb) (u.map Yb) hvY huY (by simp only [List.length_map]; omega) _ hthg
  have h2 : gN (th k r γ g) ≤ C * gN g :=
    (hC0 g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gN_nonneg g))
  have h1 : gN g ≤ C * gN (th k r γ g) := by
    have h := hC0 _ hthg
    rw [th_th hE (isUnit_of_uh hg)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gN_nonneg _))
  have hcmp := rpow_cmp (A := A) (gN_pos hg) (gN_pos hthg) hC1 h1 h2
  have hMp : (0 : ℝ) ≤ M ^ (u.length + v.length) := pow_nonneg hM0.le _
  have hCA : (0 : ℝ) ≤ C ^ |A| := Real.rpow_nonneg hC0'.le _
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg hMp]
  calc gN g ^ A * (M ^ (u.length + v.length) * ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖)
      ≤ (C ^ |A| * gN (th k r γ g) ^ A) * (M ^ (u.length + v.length) *
          ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖) :=
        mul_le_mul_of_nonneg_right hcmp (mul_nonneg hMp (norm_nonneg _))
    _ = M ^ (u.length + v.length) * C ^ |A| *
          (gN (th k r γ g) ^ A * ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖) := by ring
    _ ≤ M ^ (u.length + v.length) * C ^ |A| * max c 0 :=
        mul_le_mul_of_nonneg_left (hD.trans (le_max_left _ _)) (mul_nonneg hMp hCA)
    _ ≤ M ^ m * C ^ |A| * max c 0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hlen) hCA)
          (le_max_right _ _)

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stInvCC : StInvCC := by
  intro k r Wp _ _ _ D X _ _ γ hγ
  exact InvCC.main k r D.z γ hγ

end ReciprocityTheory.ChartRestriction.DS.Mult1
