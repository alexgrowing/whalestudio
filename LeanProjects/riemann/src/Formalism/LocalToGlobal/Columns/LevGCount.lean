import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound

noncomputable section

open Matrix Finset IsDedekindDomain NumberField

namespace Formalism.L2.Col

theorem add_add_sum_replicate_eq_add_mul_succ (k t j : ℕ) : (k + j) + (List.replicate j t).sum = k + j * (t + 1) := by
  rw [List.sum_replicate, smul_eq_mul]; ring

theorem add_sum_replicate_eq_add_mul (r t j : ℕ) : r + (List.replicate j t).sum = r + j * t := by
  rw [List.sum_replicate, smul_eq_mul]

theorem blkIdx_replicate_of_le (t j i : ℕ) (h : j * t ≤ i) : blkIdx (List.replicate j t) i = j := by
  induction j generalizing i with
  | zero => simp only [List.replicate_zero, blkIdx]
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    rw [if_neg (by omega), ih (i - t) (by omega)]

theorem blkIdx_replicate_lt (t j i : ℕ) (h : i < j * t) : blkIdx (List.replicate j t) i < j := by
  induction j generalizing i with
  | zero => simp at h
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    split_ifs with hit
    · omega
    · have := ih (i - t) (by omega)
      omega

section

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem SX_zero (k m : ℕ) : SX k m 0 = Finset.range (k - 1) := by
  unfold SX
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, add_zero]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, Or.inl (by omega)⟩

theorem SX_top (k j : ℕ) : SX k (j + 1) j = Finset.range (k + j - 1) := by
  unfold SX
  ext i
  simp

theorem lamGen_nil (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n a : ℕ) (S : Finset ℕ) :
    lamGen ψ χ n a [] S = supChar ψ n a [] S := by
  unfold lamGen detChar
  simp

theorem HX_zero (k t : ℕ) : HX κ k k t 0 = HU κ k := rfl

theorem lamX_zero (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (k m t : ℕ) : lamX ψ χ k k m t 0 = psiU ψ k := by
  unfold lamX psiU
  rw [SX_zero]
  exact lamGen_nil ψ χ k k _

theorem HX_top (n k t j : ℕ) : HX κ n k t j = HJ κ n (k + j) t j := rfl

theorem lamX_top (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k t j : ℕ) : lamX ψ χ n k (j + 1) t j = lamJ ψ χ n (k + j) t j := by
  unfold lamX lamJ
  rw [SX_top]

theorem lamJ_zero (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t : ℕ) : lamJ ψ χ r r t 0 = psiU ψ r := by
  unfold lamJ psiU
  exact lamGen_nil ψ χ r r _

theorem diagEmb_mem_uniUT {s : ℕ} (h : s ≤ n) {a : ℕ} {bl : List ℕ} {g : GL (Fin s) κ} (hg : g ∈ uniUT s κ a bl) :
    diagEmb κ h g ∈ uniUT n κ a bl := by
  have hv : ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = diagMat s n (g : Matrix (Fin s) (Fin s) κ) := rfl
  obtain ⟨h1, h2⟩ := hg
  show diagEmb κ h g ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i hi => ?_⟩
  · show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
    intro i j hij
    rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h1 (i := ⟨i.val, hs.1⟩) (j := ⟨j.val, hs.2⟩) hij
    · exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  · rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h2 ⟨i.val, hs.1⟩ hi
    · exact Matrix.one_apply_eq i

theorem diagEmb_mem_fixCol {s : ℕ} (h : s ≤ n) {c : ℕ} (hc : s ≤ c) (g : GL (Fin s) κ) : diagEmb κ h g ∈ fixCol n κ c := by
  show ∀ i j : Fin n, j.val = c → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  intro i j hj
  show diagMat s n (g : Matrix (Fin s) (Fin s) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · exact absurd hs.2 (by omega)
  · rfl

theorem sub_mul {s : ℕ} (A B : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (hA : ∀ i : Fin s, A i.castSucc (Fin.last s) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, hA i, zero_mul, add_zero]

theorem exists_diagEmb {s : ℕ} (M : GL (Fin (s + 1)) κ) (hc : M ∈ fixCol (s + 1) κ s)
    (hr : ∀ j : Fin (s + 1), j.val < s → (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (Fin.last s) j = 0) :
    ∃ g : GL (Fin s) κ, diagEmb κ (Nat.le_succ s) g = M ∧
      ∀ i j : Fin s, (g : Matrix (Fin s) (Fin s) κ) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc j.castSucc := by
  have hcol : ∀ i : Fin (s + 1), (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc i (Fin.last s) rfl
  have hc' : M⁻¹ ∈ fixCol (s + 1) κ s := Subgroup.inv_mem _ hc
  have hcol' : ∀ i : Fin (s + 1), ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc' i (Fin.last s) rfl
  have hA : ∀ i : Fin s, (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hA' : ∀ i : Fin s, ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol', Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hmul : (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  have hmul' : ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA', ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  refine ⟨⟨_, _, hmul, hmul'⟩, ?_, fun i j => rfl⟩
  apply Units.ext
  ext i j
  show diagMat s (s + 1) ((M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · rfl
  · have hi2 := i.2
    have hj2 := j.2
    by_cases hj : j.val = s
    · have hjl : j = Fin.last s := Fin.ext hj
      subst hjl
      exact (hcol i).symm
    · have hil : i = Fin.last s := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hil
      rw [hr j (by omega)]
      exact Matrix.one_apply_ne (fun e => hj (by rw [← e]; rfl))

theorem HXm_eq_map (r t m : ℕ) :
    HXm κ (r + m * t + 1) r t m = (HJ κ (r + m * t) r t m).map (diagEmb κ (Nat.le_succ (r + m * t))) := by
  ext M
  constructor
  · intro hM
    obtain ⟨hJ, hF⟩ := hM
    have hlast : fine r (List.replicate m t) (r + m * t) = r + m := by
      unfold fine
      by_cases h0 : r + m * t < r
      · omega
      · rw [if_neg h0, Nat.add_sub_cancel_left, blkIdx_replicate_of_le t m (m * t) le_rfl]
    have hr : ∀ j : Fin (r + m * t + 1), j.val < r + m * t →
        (M : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) (Fin.last (r + m * t)) j = 0 := by
      intro j hj
      apply hJ.1
      show fine r (List.replicate m t) j.val < fine r (List.replicate m t) (Fin.last (r + m * t)).val
      rw [Fin.val_last, hlast]
      unfold fine
      split_ifs with h0
      · omega
      · have := blkIdx_replicate_lt t m (j.val - r) (by omega)
        omega
    obtain ⟨g, hg, hge⟩ := exists_diagEmb M hF hr
    have hgm : g ∈ HJ κ (r + m * t) r t m := by
      show g ∈ btG (r + m * t) κ (fine r (List.replicate m t)) ∧
        ∀ i : Fin (r + m * t), i.val < r → (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i i = 1
      refine ⟨?_, fun i hi => ?_⟩
      · show (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ).BlockTriangular (fun i => fine r (List.replicate m t) i.val)
        intro i j hij
        rw [hge]
        exact hJ.1 (i := i.castSucc) (j := j.castSucc) hij
      · rw [hge]
        exact hJ.2 i.castSucc hi
    exact ⟨g, hgm, hg⟩
  · rintro ⟨g, hg, rfl⟩
    show diagEmb κ (Nat.le_succ (r + m * t)) g ∈ HJ κ (r + m * t + 1) r t m ⊓ fixCol (r + m * t + 1) κ (r + m * t)
    exact Subgroup.mem_inf.mpr ⟨diagEmb_mem_uniUT _ hg, diagEmb_mem_fixCol _ le_rfl g⟩

theorem HXm_comap (r t m : ℕ) :
    (HXm κ (r + m * t + 1) r t m).comap (diagEmb κ (Nat.le_succ (r + m * t))) = HJ κ (r + m * t) r t m := by
  have h1 : ∀ (X : GL (Fin (r + m * t)) κ) (i j : Fin (r + m * t)),
      ((diagEmb κ (Nat.le_succ (r + m * t)) X : GL (Fin (r + m * t + 1)) κ) : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) i.castSucc j.castSucc =
        (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i j := by
    intro X i j
    show diagMat (r + m * t) (r + m * t + 1) (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i.castSucc j.castSucc = _
    simp [diagMat]
  have inj : Function.Injective (diagEmb κ (Nat.le_succ (r + m * t))) := by
    intro g g' he
    apply Units.ext
    ext i j
    rw [← h1 g i j, ← h1 g' i j, he]
  rw [HXm_eq_map, Subgroup.comap_map_eq_self_of_injective inj]

end

section Uni

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

def uMat (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    Matrix (Fin n) (Fin n) κ :=
  fun i j => if i = j then 1 else if h : P i j then f ⟨(i, j), h⟩ else 0

theorem uMat_diag (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) (i : Fin n) :
    uMat P f i i = 1 := by
  simp [uMat]

theorem uMat_pos {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : P i j) : uMat P f i j = f ⟨(i, j), h⟩ := by
  simp only [uMat, if_neg hne, dif_pos h]

theorem uMat_neg {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : ¬ P i j) : uMat P f i j = 0 := by
  simp only [uMat, if_neg hne, dif_neg h]

theorem uMat_det {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uMat P f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [uMat_diag]
  · intro i j hji
    have hne : i ≠ j := (ne_of_lt hji).symm
    exact uMat_neg f hne (fun h => absurd hji (not_lt.mpr (le_of_lt (hP i j h))))

def uGL {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : GL (Fin n) κ :=
  Matrix.GeneralLinearGroup.mk'' (uMat P f) (by rw [uMat_det hP]; exact isUnit_one)

theorem uGL_val {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uGL hP f : Matrix (Fin n) (Fin n) κ) = uMat P f := rfl

def uSet (κ : Type) [CommRing κ] (P : Fin n → Fin n → Prop) : Set (GL (Fin n) κ) :=
  {M | (∀ i, (M : Matrix (Fin n) (Fin n) κ) i i = 1) ∧ ∀ i j, i ≠ j → ¬ P i j → (M : Matrix (Fin n) (Fin n) κ) i j = 0}

def uEquiv {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    ↥(uSet κ P) ≃ ({p : Fin n × Fin n // P p.1 p.2} → κ) where
  toFun M p := (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2
  invFun f := ⟨uGL hP f, fun i => uMat_diag P f i, fun _ _ hne h => uMat_neg f hne h⟩
  left_inv M := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    show uMat P (fun p => (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2) i j = _
    by_cases hne : i = j
    · rw [hne, uMat_diag, M.2.1]
    · by_cases h : P i j
      · rw [uMat_pos _ hne h]
      · rw [uMat_neg _ hne h, M.2.2 i j hne h]
  right_inv f := by
    funext p
    show uMat P f p.1.1 p.1.2 = _
    rw [uMat_pos f (ne_of_lt (hP _ _ p.2)) p.2]

theorem card_uSet {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    Nat.card ↥(uSet κ P) = Nat.card κ ^ Nat.card {p : Fin n × Fin n // P p.1 p.2} := by
  rw [Nat.card_congr (uEquiv hP), Nat.card_fun]

theorem uniUT_full_eq : ((uniUT n κ n [] : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) = uSet κ (fun i j : Fin n => i < j) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  constructor
  · intro hM
    obtain ⟨h1, h2⟩ := hM
    refine ⟨fun i => h2 i i.2, fun i j hne hlt => ?_⟩
    have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    exact h1 ((fine_lt_right i.2).mpr hji)
  · rintro ⟨h1, h2⟩
    show M ∈ btG n κ (fine n []) ∧ ∀ i : Fin n, i.val < n → (M : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i _ => h1 i⟩
    show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine n [] i.val)
    intro i j hji
    have hji' : j.val < i.val := (fine_lt_right i.2).mp hji
    exact h2 i j (fun e => by subst e; exact lt_irrefl _ hji') (fun h => absurd hji' (not_lt.mpr (le_of_lt h)))

theorem card_lt_pairs (k : ℕ) : Nat.card {p : Fin k × Fin k // p.1 < p.2} = k * (k - 1) / 2 := by
  have e : {p : Fin k × Fin k // p.1 < p.2} ≃ Σ j : Fin k, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2.val, lt_trans q.2.2 q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h2 : ∑ j : Fin k, (j : ℕ) = ∑ i ∈ Finset.range k, i := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h2, Finset.sum_range_id]

theorem card_HU (κ : Type) [CommRing κ] (k : ℕ) : Nat.card ↥(HU κ k) = Nat.card κ ^ (k * (k - 1) / 2) := by
  have h1 : Nat.card ↥(HU κ k) = Nat.card ↥(uSet κ (fun i j : Fin k => i < j)) := by
    rw [← uniUT_full_eq]; rfl
  rw [h1, card_uSet (fun _ _ h => h)]
  congr 1
  exact card_lt_pairs k

theorem uGL_mem_uniUT {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    uGL hP f ∈ uniUT n κ a bl := by
  show uGL hP f ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → (uGL hP f : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i _ => by rw [uGL_val]; exact uMat_diag P f i⟩
  show (uGL hP f : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
  intro i j hij
  rw [uGL_val]
  have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
  refine uMat_neg f hne (fun hp => ?_)
  have h1 := hP i j hp
  have h2 := hPa i j hp
  have h3 : i.val < a := lt_trans (show i.val < j.val from h1) h2
  have hij' := (fine_lt_right (bl := bl) h3).mp hij
  exact absurd hij' (not_lt.mpr (le_of_lt h1))

theorem detChar_uGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    detChar χ n a bl ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply]
  apply Finset.prod_eq_one
  intro s _
  rw [MonoidHom.comp_apply]
  have hb : blkDet n κ (coarse a bl) (s + 1) ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
    apply Units.ext
    change Matrix.det ((uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1)) = (1 : κ)
    have hI : (uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply, uGL_val, Matrix.one_apply]
      split_ifs with h
      · rw [h]; exact uMat_diag P f _
      · refine uMat_neg f (fun e => h (Subtype.ext e)) (fun hp => ?_)
        have h1 := hPa _ _ hp
        have h3 : coarse a bl (j : Fin n).val = 0 := by simp only [coarse, blkIdx, if_pos h1]
        have h4 : coarse a bl (j : Fin n).val = s + 1 := j.2
        omega
    rw [hI, Matrix.det_one]
  rw [hb, map_one]

theorem lamGen_val_of_det (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (M : ↥(uniUT n κ a bl))
    (hd : detChar χ n a bl ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ = 1) :
    ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hi : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) M = ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ := rfl
  rw [hi, hd, mul_one]
  rfl

theorem supSum_elem {a : ℕ} (S : Finset ℕ) (i₀ j₀ : Fin n) (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    supSum a S (uMat (fun i j : Fin n => i = i₀ ∧ j = j₀) (fun _ => c)) = c := by
  unfold supSum
  rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
  · rw [if_pos ⟨h₀, ha, hS⟩, uMat_pos _ (fun e => by rw [e] at h₀; omega) ⟨rfl, rfl⟩]
  · intro j _ hj
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hj hp.2)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hi hp.1)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lamGen_elem (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (i₀ j₀ : Fin n)
    (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    ∃ M : ↥(uniUT n κ a bl), ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ c := by
  have hP : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → i < j := by
    rintro i j ⟨rfl, rfl⟩; show i.val < j.val; omega
  have hPa : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → j.val < a := by
    rintro i j ⟨rfl, rfl⟩; exact ha
  refine ⟨⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩, ?_⟩
  rw [lamGen_val_of_det ψ χ bl S ⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩ (detChar_uGL χ bl hP hPa _)]
  congr 1
  exact supSum_elem S i₀ j₀ h₀ ha hS c

theorem lamGen_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {S : Finset ℕ} {i₀ : ℕ}
    (hS : i₀ ∈ S) (ha : i₀ + 1 < a) (han : a ≤ n) : lamGen ψ χ n a bl S ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hψ (DFunLike.ext _ _ fun x => (hcon x).trans (AddChar.one_apply x).symm)
  obtain ⟨M, hM⟩ := lamGen_elem ψ χ bl S (⟨i₀, by omega⟩ : Fin n) (⟨i₀ + 1, by omega⟩ : Fin n) rfl ha hS c
  rw [h, MonoidHom.one_apply, Units.val_one] at hM
  exact hc hM.symm

theorem lamX_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {k : ℕ} (m t j : ℕ) (hk : 2 ≤ k) (hn : k + j ≤ n) :
    lamX ψ χ n k m t j ≠ 1 := by
  unfold lamX
  refine lamGen_ne_one hψ χ _ (i₀ := 0) ?_ (by omega) hn
  unfold SX
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Or.inl (by omega)⟩

theorem lamJ_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (t j : ℕ) (hr : 2 ≤ r) (hn : r ≤ n) :
    lamJ ψ χ n r t j ≠ 1 := by
  unfold lamJ
  exact lamGen_ne_one hψ χ _ (i₀ := 0) (Finset.mem_range.mpr (by omega)) (by omega) hn

end Uni

theorem char_pow_card {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) : lam x ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem char_norm_one {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) (φ : K →+* ℂ) :
    ‖φ (lam x : K)‖ = 1 := by
  have h1 : (φ (lam x : K)) ^ Nat.card G = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, char_pow_card, Units.val_one, map_one]
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 : ‖φ (lam x : K)‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2

private theorem prod_one_sub_lemma {ι : Type} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) ∧ ∏ i ∈ s, (1 - f i) ≤ 1 ∧ 0 ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    obtain ⟨i1, i2, i3⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have fa0 := h0 a (Finset.mem_insert_self a s)
    have fa1 := h1 a (Finset.mem_insert_self a s)
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_nonneg fa0 (sub_nonneg.mpr i2)]
    · nlinarith [mul_nonneg fa0 i3]
    · exact mul_nonneg (by linarith) i3

private theorem card_GL_eq_card_pow_mul_theta (F : Type) [Field F] [Fintype F] (n : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Nat.card (GL (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (n * n) * θ := by
  have hq3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hqn : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos hqpos n
  have hx0 : ∀ i : Fin n, 0 ≤ (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n := fun i => by positivity
  have hx1 : ∀ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 := by
    intro i
    rw [div_le_one hqn]
    have : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
    exact_mod_cast this
  have hsum : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 / 2 := by
    have hgs : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) = ∑ i ∈ Finset.range n, (Fintype.card F : ℝ) ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (Fintype.card F : ℝ) ^ i) n
    rw [← Finset.sum_div, hgs, geom_sum_eq (by linarith), div_div, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq3) hqn.le]
  have hb := prod_one_sub_lemma Finset.univ (fun i : Fin n => (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n)
    (fun i _ => hx0 i) (fun i _ => hx1 i)
  have b1 : 1 - ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤
      ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) := hb.1
  have b2 : ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) ≤ 1 := hb.2.1
  refine ⟨∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n), by linarith, b2, ?_⟩
  have hrhs : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i : Fin n, (Fintype.card F : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod, hrhs, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hle : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
  have hcan : (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) =
      (Fintype.card F : ℝ) ^ (i : ℕ) := by
    field_simp
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one, hcan]

theorem index_HU (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HU F k).index : ℝ) = (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ := by
  obtain ⟨θ, h1, h2, hc⟩ := card_GL_eq_card_pow_mul_theta F k h3
  refine ⟨θ, h1, h2, ?_⟩
  have hH : Nat.card ↥(HU F k) = Fintype.card F ^ (k * (k - 1) / 2) := by
    rw [card_HU, Nat.card_eq_fintype_card (α := F)]
  have hmul := Subgroup.card_mul_index (HU F k)
  rw [hH] at hmul
  have hexp : k * k = k * (k - 1) / 2 + k * (k + 1) / 2 := by
    cases k with
    | zero => rfl
    | succ k =>
      have hA : (k + 1) * (k + 1 - 1) = (k + 1) * k := by simp
      have hB : (k + 1) * (k + 1 + 1) = (k + 1) * k + 2 * (k + 1) := by ring
      have hC : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      have hE : (k + 1) * k % 2 = 0 := by
        rcases Nat.even_mul_succ_self k with ⟨t, ht⟩
        rw [Nat.mul_comm, ht]
        omega
      rw [hA, hB, hC, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      generalize (k + 1) * k = A at hE ⊢
      omega
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
      linarith
    positivity
  have hR : (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((HU F k).index : ℝ) =
      (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ) := by
    have hm := congrArg (fun x : ℕ => (x : ℝ)) hmul
    push_cast at hm
    rw [hm, hc, hexp, pow_add, mul_assoc]
  exact mul_left_cancel₀ hpos.ne' hR

section Diag

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

def dGL (i₀ : Fin n) (u : κˣ) : GL (Fin n) κ :=
  Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom (MulEquiv.piUnits.symm (Function.update 1 i₀ u))

theorem dGL_val (i₀ : Fin n) (u : κˣ) :
    (dGL i₀ u : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ) := rfl

theorem dGL_mem_btG (β : ℕ → ℕ) (i₀ : Fin n) (u : κˣ) : dGL i₀ u ∈ btG n κ β := by
  show (dGL i₀ u : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => β i.val)
  rw [dGL_val]
  exact Matrix.blockTriangular_diagonal _

theorem blkDet_dGL (β : ℕ → ℕ) (c : ℕ) (i₀ : Fin n) (u : κˣ) :
    blkDet n κ β c ⟨dGL i₀ u, dGL_mem_btG β i₀ u⟩ = if β i₀.val = c then u else 1 := by
  apply Units.ext
  change Matrix.det ((dGL i₀ u : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c) = _
  rw [dGL_val]
  have hd : (Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ)).toSquareBlock (fun i => β i.val) c =
      Matrix.diagonal (fun i : {i : Fin n // β i.val = c} => ((Function.update (1 : Fin n → κˣ) i₀ u i.1 : κˣ) : κ)) := by
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [hd, Matrix.det_diagonal]
  split_ifs with hc
  · rw [Finset.prod_eq_single ⟨i₀, hc⟩]
    · simp
    · intro b _ hb
      rw [Function.update_apply, if_neg (fun e => hb (Subtype.ext e))]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Units.val_one]
    apply Finset.prod_eq_one
    intro b _
    rw [Function.update_apply, if_neg (fun e => hc (by rw [← e]; exact b.2))]
    simp

theorem dGL_mem_HK {r : ℕ} (bl : List ℕ) (i₀ : Fin n) (h₀ : r ≤ i₀.val) (u : κˣ) : dGL i₀ u ∈ HK n κ r bl := by
  refine ⟨⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext i j
  rw [blkHom_apply, dGL_val]
  have hi : (i.1 : Fin n).val < r := by
    by_contra hh
    exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
  by_cases hij : i = j
  · subst hij
    have hne : (i.1 : Fin n) ≠ i₀ := fun e => by rw [← e] at h₀; omega
    simp [Function.update_apply, hne]
  · have hne : (i.1 : Fin n) ≠ j.1 := fun e => hij (Subtype.ext e)
    simp [hij, hne]

theorem detChar_dGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse a bl i₀.val = s + 1) (u : κˣ) : detChar χ n a bl ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ = χ s u := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply, Finset.prod_eq_single s]
  · rw [MonoidHom.comp_apply, blkDet_dGL, if_pos h₀]
  · intro c _ hc
    rw [MonoidHom.comp_apply, blkDet_dGL, if_neg (by omega), map_one]
  · intro h; exact absurd (Finset.mem_range.mpr hs) h

theorem lamK_ne_one (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse r bl i₀.val = s + 1) (hχ : χ s ≠ 1) : lamK χ n r bl ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, χ s u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hχ (MonoidHom.ext hcon)
  have hr : r ≤ i₀.val := by
    by_contra hh
    have : coarse r bl i₀.val = 0 := by simp only [coarse, blkIdx, if_pos (by omega : i₀.val < r)]
    omega
  have h1 := congrArg (fun f => f ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamK at h1
  rw [MonoidHom.comp_apply] at h1
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩ = ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ := rfl
  rw [e, detChar_dGL χ bl i₀ hs h₀ u] at h1
  exact hu h1

theorem coarse_replicate {r t j s : ℕ} (ht : 0 < t) (hs : s < j) : coarse r (List.replicate j t) (r + s * t) = s + 1 := by
  unfold coarse
  simp only [blkIdx]
  rw [if_neg (by omega)]
  congr 1
  rw [Nat.add_sub_cancel_left]
  induction s generalizing j with
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [List.replicate_succ, blkIdx, zero_mul, if_pos ht]
  | succ s ih =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul, if_neg (by omega), Nat.add_sub_cancel, ih (by omega)]

theorem lamKJ_ne_one (χ : ℕ → κˣ →* Kˣ) {r t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : r + j * t ≤ n) (hχ : χ s ≠ 1) :
    lamKJ χ n r t j ≠ 1 := by
  unfold lamKJ
  have hst : s * t < j * t := Nat.mul_lt_mul_of_pos_right hs ht
  exact lamK_ne_one χ (List.replicate j t) (⟨r + s * t, by omega⟩ : Fin n) (by simpa using hs) (coarse_replicate ht hs) hχ

theorem lamQ_ne_one {ξ : κˣ →* Kˣ} {a b : ℕ} (hb : 0 < b) (hn : a + b ≤ n) (hξ : ξ ≠ 1) : lamQ ξ n a b ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, ξ u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hξ (MonoidHom.ext hcon)
  have hc : coarse a [b] (⟨a, by omega⟩ : Fin n).val = 0 + 1 := by
    simp [coarse, blkIdx, hb]
  have h1 := congrArg (fun f => f ⟨dGL (⟨a, by omega⟩ : Fin n) u, dGL_mem_btG _ _ u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamQ at h1
  rw [detChar_dGL (fun _ => ξ) [b] _ (by simp) hc u] at h1
  exact hu h1

theorem HK_conj_diagEmb {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) {M : GL (Fin n) κ} (hM : M ∈ HK n κ r bl) :
    diagEmb κ h g * M * (diagEmb κ h g)⁻¹ ∈ HK n κ r bl := by
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  unfold HK at hM ⊢
  rw [Subgroup.mem_map] at hM ⊢
  obtain ⟨M', hM', hMe⟩ := hM
  refine ⟨⟨diagEmb κ h g, hD⟩ * M' * ⟨diagEmb κ h g, hD⟩⁻¹, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hM' ⊢
    rw [map_mul, map_mul, hM', mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [← hMe, map_mul, map_mul, map_inv]
    rfl

theorem lamK_conj_diagEmb (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) (M : ↥(HK n κ r bl)) :
    lamK χ n r bl ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ = lamK χ n r bl M := by
  unfold lamK
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ =
      ⟨diagEmb κ h g, hD⟩ * Subgroup.inclusion (HK_le_blockUT n κ r bl) M * ⟨diagEmb κ h g, hD⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

end Diag

instance finite_res (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ w.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot

instance finite_GLs (E : Type) [Field E] [NumberField E] (SG : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) : Finite (GLs E SG n) :=
  Pi.finite

example : Nat.card ↥(HU (ZMod 3) 2) = 3 := by rw [card_HU]; simp

example : Nat.card ↥(HU (ZMod 5) 4) = 5 ^ 6 := by rw [card_HU]; simp

theorem stdAddChar_ne_one : (ZMod.stdAddChar (N := 3)) ≠ 1 := by
  have hp := ZMod.isPrimitive_stdAddChar 3
  have h := hp (a := 1) (by decide)
  rwa [AddChar.mulShift_one] at h

example : lamX (ZMod.stdAddChar (N := 3)) (fun _ => 1) 8 3 2 4 1 ≠ 1 :=
  lamX_ne_one stdAddChar_ne_one _ 2 4 1 (by norm_num) (by norm_num)

section DiagChar

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem supSum_diagMat {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (S : Finset ℕ) (g : Matrix (Fin s) (Fin s) κ) :
    supSum a S (diagMat s n g) = supSum a S g := by
  unfold supSum
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    have his : s ≤ i.val := by
      by_contra hh
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hc
    have := hc.1
    have := hc.2.1
    omega
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro j hj
      have hjs : s ≤ j.val := by
        by_contra hh
        exact hj ⟨⟨j.val, by omega⟩, rfl⟩
      rw [if_neg]
      intro hc
      have := hc.2.1
      omega
    · intro j
      simp only [Fin.coe_castLE]
      split_ifs
      · simp [diagMat]
      · rfl

theorem blkDet_diagEmb {s : ℕ} (h : s ≤ n) (β : ℕ → ℕ) (c : ℕ) (hc : ∀ i : ℕ, s ≤ i → β i ≠ c) (g : GL (Fin s) κ)
    (hg : g ∈ btG s κ β) (hg' : diagEmb κ h g ∈ btG n κ β) :
    blkDet n κ β c ⟨diagEmb κ h g, hg'⟩ = blkDet s κ β c ⟨g, hg⟩ := by
  apply Units.ext
  change Matrix.det ((diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c) =
    Matrix.det ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c)
  let e : {i : Fin s // β i.val = c} ≃ {i : Fin n // β i.val = c} :=
    { toFun := fun i => ⟨⟨i.1.val, lt_of_lt_of_le i.1.2 h⟩, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, by
        by_contra hh
        exact hc i.1.val (by omega) i.2⟩, i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  have hb : (diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c =
      ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c).submatrix e.symm e.symm := by
    ext i j
    have hi : (i.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) i.2
    have hj : (j.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) j.2
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.submatrix_apply, diagMat]
    rw [dif_pos ⟨hi, hj⟩]
    rfl
  rw [hb, Matrix.det_submatrix_equiv_self]

theorem lamGen_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (bl : List ℕ) (S : Finset ℕ)
    (hs : ∀ i : ℕ, s ≤ i → bl.length < coarse a bl i) (g : ↥(uniUT s κ a bl)) :
    lamGen ψ χ n a bl S ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ = lamGen ψ χ s a bl S g := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply]
  congr 1
  · apply Units.ext
    show ψ (supSum a S (diagMat s n (g.1 : Matrix (Fin s) (Fin s) κ))) = ψ (supSum a S (g.1 : Matrix (Fin s) (Fin s) κ))
    rw [supSum_diagMat h ha]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    have e1 : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ =
        ⟨diagEmb κ h g.1, uniUT_le_blockUT n κ a bl (diagEmb_mem_uniUT h g.2)⟩ := rfl
    have e2 : Subgroup.inclusion (uniUT_le_blockUT s κ a bl) g = ⟨g.1, uniUT_le_blockUT s κ a bl g.2⟩ := rfl
    rw [e1, e2]
    unfold detChar
    rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply]
    apply Finset.prod_congr rfl
    intro c hc
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    have hcl := Finset.mem_range.mp hc
    exact blkDet_diagEmb h (coarse a bl) (c + 1) (fun i hi => by have := hs i hi; omega) g.1 _ _

theorem lamXm_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t m : ℕ) (g : ↥(HJ κ (r + m * t) r t m)) :
    lamXm ψ χ (r + m * t + 1) r t m
      ⟨diagEmb κ (Nat.le_succ (r + m * t)) g.1, ⟨diagEmb_mem_uniUT _ g.2, diagEmb_mem_fixCol _ le_rfl g.1⟩⟩ =
      lamJ ψ χ (r + m * t) r t m g := by
  unfold lamXm lamJ
  rw [MonoidHom.comp_apply]
  refine lamGen_diagEmb ψ χ (Nat.le_succ _) (by omega) _ _ (fun i hi => ?_) g
  have h1 : coarse r (List.replicate m t) i = m + 1 := by
    unfold coarse
    simp only [blkIdx]
    rw [if_neg (by omega), blkIdx_replicate_of_le t m (i - r) (by omega)]
  rw [h1, List.length_replicate]
  omega

end DiagChar

section Sym

variable {n : ℕ} {κ : Type} [CommRing κ]

theorem HPsym_eq (k rS : ℕ) : ((HPsym κ n k rS : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) =
    uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  have hU := Set.ext_iff.mp (uniUT_full_eq (n := n) (κ := κ)) M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq] at hU
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨d, o⟩ := hU.mp h1
    refine ⟨d, fun i j hne hP => ?_⟩
    by_cases hlt : i < j
    · have hh : rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k := by
        by_contra hc
        exact hP ⟨hlt, hc⟩
      exact h2 i j hh.1 hh.2.1 hh.2.2
    · exact o i j hne hlt
  · rintro ⟨d, o⟩
    show M ∈ uniUT n κ n [] ∧ ∀ i j : Fin n, rS ≤ i.val → i.val < rS + k → j.val = rS + k → (M : Matrix (Fin n) (Fin n) κ) i j = 0
    refine ⟨hU.mpr ⟨d, fun i j hne hlt => o i j hne (fun h => hlt h.1)⟩, fun i j h1 h2 h3 => ?_⟩
    have hlt : i < j := by
      show i.val < j.val
      omega
    exact o i j (ne_of_lt hlt) (fun h => h.2 ⟨h1, h2, h3⟩)

theorem card_sym_pairs (k rS : ℕ) (hn : rS + k < n) :
    Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)} = n * (n - 1) / 2 - k := by
  have hA : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := card_lt_pairs n
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hA ⊢
  rw [← hA]
  have hsub : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) ⊆
      Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    show p.1.val < p.2.val
    omega
  have hB : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k).card = k := by
    rw [← Fintype.card_subtype]
    have e : {p : Fin n × Fin n // rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k} ≃ Fin k :=
      { toFun := fun p => ⟨p.1.1.val - rS, by obtain ⟨h1, h2, h3⟩ := p.2; omega⟩
        invFun := fun i => ⟨(⟨rS + i.val, by omega⟩, ⟨rS + k, hn⟩), Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨a, b⟩, h1, h2, h3⟩ := p
          dsimp only at h1 h2 h3
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            show rS + (a.val - rS) = a.val
            omega
          · apply Fin.ext
            show rS + k = b.val
            omega
        right_inv := fun i => by
          apply Fin.ext
          show rS + i.val - rS = i.val
          omega }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hsd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
        (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hsd, Finset.card_sdiff_of_subset hsub, hB]

theorem card_HPsym (κ : Type) [CommRing κ] (n k rS : ℕ) (hn : rS + k < n) :
    Nat.card ↥(HPsym κ n k rS) = Nat.card κ ^ (n * (n - 1) / 2 - k) := by
  have h1 : Nat.card ↥(HPsym κ n k rS) =
      Nat.card ↥(uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k))) := by
    rw [← HPsym_eq]; rfl
  rw [h1, card_uSet (P := fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) (fun _ _ h => h.1)]
  congr 1
  exact card_sym_pairs k rS hn

theorem sym_arith (k s : ℕ) :
    (k + 2 * s + 1) * (k + 2 * s + 1 - 1) / 2 - k =
      ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 + k * (k - 1) / 2 := by
  have e1 : k + 2 * s + 1 - 1 = k + 2 * s := by omega
  have e2 : (k + 2 * s + 1) * (k + 2 * s) = k * (k - 1) + 2 * (k + s * (2 * k + 2 * s + 1)) := by
    cases k with
    | zero => simp; ring
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have e4 : (k + 2 * s + 1) ^ 2 = (k + 1) ^ 2 + 2 * s + 2 * (s * (2 * k + 2 * s + 1)) := by ring
  have e3 : (k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s = 2 * (s * (2 * k + 2 * s + 1)) := by
    rw [e4, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  rw [e1, e2, e3, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  generalize k * (k - 1) / 2 = A
  generalize s * (2 * k + 2 * s + 1) = B
  omega

end Sym

theorem index_HPsym (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ) (hm : 2 ≤ m) (hev : Even m)
    (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) =
      (Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ := by
  obtain ⟨p, hp⟩ := hev
  obtain ⟨θ, h1, h2, hc⟩ := card_GL_eq_card_pow_mul_theta F (k + m - 1) h3
  refine ⟨θ, h1, h2, ?_⟩
  have hlt : m / 2 - 1 + k < k + m - 1 := by omega
  have hH := card_HPsym F (k + m - 1) k (m / 2 - 1) hlt
  rw [Nat.card_eq_fintype_card (α := F)] at hH
  have hmul := Subgroup.card_mul_index (HPsym F (k + m - 1) k (m / 2 - 1))
  rw [hH] at hmul
  have hexp : (k + m - 1) * (k + m - 1) = ((k + m - 1) * (k + m - 1 - 1) / 2 - k) +
      ((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2 := by
    subst hp
    obtain ⟨q', rfl⟩ : ∃ q', p = q' + 1 := ⟨p - 1, by omega⟩
    have hr : k + (q' + 1 + (q' + 1)) - 1 = k + 2 * q' + 1 := by omega
    have hd : (q' + 1 + (q' + 1)) / 2 - 1 = q' := by omega
    rw [hr, hd]
    have e1 : k + 2 * q' + 1 - 1 = k + 2 * q' := by omega
    rw [e1]
    have e2 : (k + 2 * q' + 1) ^ 2 + 3 * k + 1 + 2 * q' = (k + 2 * q' + 1) * (k + 2 * q') + 2 * (k + 2 * q' + 1) + 2 * k := by ring
    have e3 : (k + 2 * q' + 1) * (k + 2 * q' + 1) = (k + 2 * q' + 1) * (k + 2 * q') + (k + 2 * q' + 1) := by ring
    have hE : (k + 2 * q' + 1) * (k + 2 * q') % 2 = 0 := by
      rcases Nat.even_mul_succ_self (k + 2 * q') with ⟨t, ht⟩
      rw [Nat.mul_comm, ht]
      omega
    have hK : 2 * k ≤ (k + 2 * q' + 1) * (k + 2 * q') := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · exact Nat.mul_le_mul (by omega) (by omega)
    rw [e2, e3]
    generalize (k + 2 * q' + 1) * (k + 2 * q') = A at hE hK ⊢
    omega
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
      linarith
    positivity
  have hR : (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) * ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) =
      (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) *
        ((Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ) := by
    have hm := congrArg (fun x : ℕ => (x : ℝ)) hmul
    push_cast at hm
    rw [hm, hc, hexp, pow_add, mul_assoc]
  exact mul_left_cancel₀ hpos.ne' hR

section More

variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem HXm_eq_map' (n' r t m : ℕ) (hn : n' = r + m * t) :
    HXm κ (n' + 1) r t m = (HJ κ n' r t m).map (diagEmb κ (Nat.le_succ n')) := by
  subst hn
  exact HXm_eq_map r t m

theorem lamXm_diag (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n' r t m : ℕ) (hn : n' = r + m * t) (h : ↥(HJ κ n' r t m))
    (hm : diagEmb κ (Nat.le_succ n') h.1 ∈ HXm κ (n' + 1) r t m) :
    lamXm ψ χ (n' + 1) r t m ⟨_, hm⟩ = lamJ ψ χ n' r t m h := by
  subst hn
  exact lamXm_diagEmb ψ χ r t m h

theorem lamJ_on_HKJ (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) (M : ↥(HKJ κ n r t j)) :
    lamJ ψ χ n r t j (Subgroup.inclusion (HK_le_uniUT n κ r _) M) = lamKJ χ n r t j M := by
  unfold lamJ lamKJ lamK lamGen
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hs : supChar ψ n r (List.replicate j t) (Finset.range (r - 1)) (Subgroup.inclusion (HK_le_uniUT n κ r (List.replicate j t)) M) = 1 := by
    apply Units.ext
    change ψ (supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) = 1
    have h0 : supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = 0 := by
      obtain ⟨M', hM', hMe⟩ := M.2
      have hker : blkHom n κ (coarse r (List.replicate j t)) 0 M' = 1 := hM'
      unfold supSum
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j' _
      split_ifs with hc
      · obtain ⟨hc1, hc2, -⟩ := hc
        have hi0 : coarse r (List.replicate j t) i.val = 0 := by
          simp only [coarse, blkIdx, if_pos (show i.val < r by omega)]
        have hj0 : coarse r (List.replicate j t) j'.val = 0 := by
          simp only [coarse, blkIdx, if_pos hc2]
        have hk := congrFun (congrFun hker ⟨i, hi0⟩) ⟨j', hj0⟩
        rw [blkHom_apply, Matrix.one_apply_ne (fun e => by
          have := congrArg (fun x => x.1.val) e
          simp only at this
          omega)] at hk
        rw [← hMe]
        exact hk
      · rfl
    rw [h0, AddChar.map_zero_eq_one]
  rw [hs, one_mul]
  rfl

theorem diagEmb_mulVec_snoc {n : ℕ} (h : GL (Fin n) κ) (v : Fin n → κ) (c : κ) :
    (diagEmb κ (Nat.le_succ n) h).1.mulVec (Fin.snoc (α := fun _ => κ) v c) =
      Fin.snoc (α := fun _ => κ) (h.1.mulVec v) c := by
  show (diagMat n (n + 1) (h : Matrix (Fin n) (Fin n) κ)).mulVec (Fin.snoc (α := fun _ => κ) v c) = Fin.snoc (α := fun _ => κ) ((h : Matrix (Fin n) (Fin n) κ).mulVec v) c
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply, (Fin.castSucc_lt_last i).ne]

end More

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem lambdaAtPrime_eq_of_residueCharacter (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (hχ : Formalism.L2.DIV.IsResChar ξ P χ) (huniq : ∀ χ', Formalism.L2.DIV.IsResChar ξ P χ' → χ' = χ) :
    lamQP ξ P n a b = lamQ χ n a b := by
  unfold lamQP
  congr 1
  unfold Formalism.L2.DIV.resChar
  rw [dif_pos ⟨χ, hχ⟩]
  exact huniq _ (Exists.choose_spec _)

theorem lambdaAtPrime_eq_one_of_no_residueCharacter (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ)
    (hno : ¬ ∃ χ, Formalism.L2.DIV.IsResChar ξ P χ) : lamQP ξ P n a b = 1 := by
  unfold lamQP
  have h1 : Formalism.L2.DIV.resChar ξ P = 1 := by
    unfold Formalism.L2.DIV.resChar
    rw [dif_neg hno]
  rw [h1]
  unfold lamQ detChar
  simp

end Res

section ParId

variable {n : ℕ} {κ : Type} [CommRing κ]

theorem blockUT_self_top (r : ℕ) : blockUT r κ r [] = ⊤ := by
  rw [eq_top_iff]
  intro M _
  show (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => coarse r [] i.val)
  intro i j hij
  exfalso
  simp only [coarse, blkIdx, if_pos i.2, if_pos j.2] at hij
  exact lt_irrefl _ hij

theorem uniUT_eq_HPar {r : ℕ} (h : r ≤ n) (bl : List ℕ) : uniUT n κ r bl = HPar n κ h bl (HU κ r) := by
  ext M
  unfold HPar
  rw [Subgroup.mem_map]
  constructor
  · intro hM
    refine ⟨⟨M, uniUT_le_blockUT n κ r bl hM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    obtain ⟨h1, h2⟩ := id hM
    show blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ ∈ btG r κ (fine r []) ∧
      ∀ i : Fin r, i.val < r → ((blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i i = 1
    refine ⟨?_, fun i _ => ?_⟩
    · show (restr h (M : Matrix (Fin n) (Fin n) κ)).BlockTriangular (fun i => fine r [] i.val)
      intro i j hij
      exact h1 (i := Fin.castLE h i) (j := Fin.castLE h j)
        ((fine_lt_right (bl := bl) (show (Fin.castLE h i).val < r from i.2)).mpr ((fine_lt_right (bl := []) i.2).mp hij))
    · show restr h (M : Matrix (Fin n) (Fin n) κ) i i = 1
      exact h2 (Fin.castLE h i) i.2
  · rintro ⟨M', hM', rfl⟩
    rw [Subgroup.mem_comap] at hM'
    obtain ⟨h1, h2⟩ := hM'
    have hB := M'.2
    show (M' : GL (Fin n) κ) ∈ btG n κ (fine r bl) ∧ ∀ i : Fin n, i.val < r → ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i hi => h2 ⟨i.val, hi⟩ hi⟩
    show ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine r bl i.val)
    intro i j hij
    have hij' : fine r bl j.val < fine r bl i.val := hij
    by_cases hi : i.val < r
    · have hfi : fine r bl i.val = i.val := by simp only [fine, if_pos hi]
      have hj : j.val < r := by
        by_contra hj
        have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        omega
      have hfj : fine r bl j.val = j.val := by simp only [fine, if_pos hj]
      exact h1 (i := ⟨i.val, hi⟩) (j := ⟨j.val, hj⟩)
        (show fine r [] j.val < fine r [] i.val by simp only [fine, if_pos hi, if_pos hj]; omega)
    · apply hB
      show coarse r bl j.val < coarse r bl i.val
      have hfi : fine r bl i.val = r + blkIdx bl (i.val - r) := by simp only [fine, if_neg hi]
      have hci : coarse r bl i.val = blkIdx bl (i.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hi]
      rw [hci]
      by_cases hj : j.val < r
      · have hcj : coarse r bl j.val = 0 := by simp only [coarse, blkIdx, if_pos hj]
        omega
      · have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        have hcj : coarse r bl j.val = blkIdx bl (j.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hj]
        omega

theorem HK_eq_HPar {r : ℕ} (h : r ≤ n) (bl : List ℕ) : HK n κ r bl = HPar n κ h bl ⊥ := by
  unfold HK HPar
  congr 1
  ext M
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro hM
    apply Units.ext
    ext i j
    show restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j
    have hi0 : coarse r bl (Fin.castLE h i).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos i.2]
    have hj0 : coarse r bl (Fin.castLE h j).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos j.2]
    have hk := congrFun (congrFun hM ⟨Fin.castLE h i, hi0⟩) ⟨Fin.castLE h j, hj0⟩
    rw [blkHom_apply] at hk
    have hk' : restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix {x : Fin n // coarse r bl x.val = 0} {x : Fin n // coarse r bl x.val = 0} κ) ⟨Fin.castLE h i, hi0⟩ ⟨Fin.castLE h j, hj0⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]
  · intro hM
    ext i j
    rw [blkHom_apply]
    have hi : (i.1 : Fin n).val < r := by
      by_contra hh
      exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hj : (j.1 : Fin n).val < r := by
      by_contra hh
      exact absurd j.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hk := congrArg (fun X : GL (Fin r) κ => (X : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩) hM
    have hk' : (M.1 : Matrix (Fin n) (Fin n) κ) i.1 j.1 = (1 : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]

end ParId

end Formalism.L2.Col
