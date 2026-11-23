import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

theorem det_LT {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ C2.LTset m) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j h => hL.1 i j (OrderDual.toDual_lt_toDual.1 h))]
  simp [hL.2]

theorem det_UT {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ C2.UTset m) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]

theorem sub_mul_left {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hA : ∀ i : Fin r, A (Fin.castSucc i) (Fin.last r) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hA i, zero_mul, add_zero]

theorem sub_mul_right {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hB : ∀ j : Fin r, B (Fin.last r) (Fin.castSucc j) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hB j, mul_zero, add_zero]

theorem LT_sub {r : ℕ} {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L ∈ C2.LTset (r + 1)) :
    L.submatrix Fin.castSucc Fin.castSucc ∈ C2.LTset r :=
  ⟨fun i j h => hL.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), fun i => hL.2 _⟩

theorem UT_sub {r : ℕ} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU : U ∈ C2.UTset (r + 1)) :
    U.submatrix Fin.castSucc Fin.castSucc ∈ C2.UTset r :=
  ⟨fun i j h => hU.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), fun i => hU.2 _⟩

theorem minorsLU : MinorsLU := by
  unfold MinorsLU
  intro r L M U hL hU
  refine ⟨by rw [Matrix.det_mul, Matrix.det_mul, det_LT hL, det_UT hU, one_mul, mul_one], ?_⟩
  rw [sub_mul_right _ _ (fun j => hU.1 _ _ (Fin.castSucc_lt_last j)),
    sub_mul_left _ _ (fun i => hL.1 _ _ (Fin.castSucc_lt_last i)),
    Matrix.det_mul, Matrix.det_mul, det_LT (LT_sub hL), det_UT (UT_sub hU), one_mul, mul_one]

theorem lowS_eq_low {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) : lowS w x = Dx2.Rad.low w x := rfl

theorem lstLeft : LstLeft := by
  intro m w d hd x0
  have hL : lowS w x0 ∈ C2.LTset m := (Dx2.Rad.low_mem w d hd x0).1
  refine ⟨Dx2.Rad.Tr_mp w (lowS w x0) hL, fun x => ?_⟩
  have hmem := Dx2.Rad.lstg_mul w d hd (Dx2.Rad.low_mem w d hd x0) (Dx2.Rad.low_mem w d hd x)
  exact Dx2.Rad.eq_low w d hd hmem

theorem upper_apply {m : ℕ} (u : G.UT m → ℂ) (i j : Fin m) :
    G.upper u i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : i < j then u ⟨(i, j), h⟩ else 0 := by
  rfl

theorem cont_upper {m : ℕ} : Continuous (G.upper (d := m)) := by
  have hs : Continuous fun v : G.UT m → ℂ => G.strictUpper v := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i < j
    · simp only [G.strictUpper, Matrix.of_apply, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [G.strictUpper, Matrix.of_apply, h, ↓reduceDIte]
      exact continuous_const
  unfold G.upper
  fun_prop

theorem utc_upper {m : ℕ} (u : G.UT m → ℂ) : utc (G.upper u) = u := by
  funext q
  obtain ⟨⟨i, j⟩, h⟩ := q
  have h' : i < j := h
  simp only [utc, upper_apply, h', ↓reduceDIte, Matrix.one_apply_ne (ne_of_lt h'), zero_add]

theorem upper_utc {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M ∈ C2.UTset m) : G.upper (utc M) = M := by
  ext i j
  rw [upper_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, Matrix.one_apply_ne (ne_of_lt h), utc]
  · simp [hM.2]
  · simp [not_lt.2 h.le, Matrix.one_apply_ne (ne_of_gt h), hM.1 i j h]

theorem upper_mem {m : ℕ} (u : G.UT m → ℂ) : G.upper u ∈ C2.UTset m := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [upper_apply]
    simp [not_lt.2 h.le, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [upper_apply]
    simp

theorem utLeft : UTLeft := by
  intro m a ha
  refine ShearMeasurability.shear_mp (fun q : G.UT m => q.1.2.val - q.1.1.val) _ ?_ ?_
  · refine measurable_pi_lambda _ fun q => ?_
    exact ((continuous_const.matrix_mul cont_upper).matrix_elem q.1.1 q.1.2).measurable
  · intro q x y hxy
    simp only [utc, Matrix.mul_apply]
    rw [Dx2.Rad.sum_sub_single _ q.1.1 (x q), Dx2.Rad.sum_sub_single _ q.1.1 (y q)]
    apply Finset.sum_congr rfl
    intro k _
    have hq := q.2
    by_cases hki : k = q.1.1
    · subst hki
      rw [if_pos rfl, if_pos rfl, upper_apply, upper_apply, Matrix.one_apply_ne (ne_of_lt q.2), dif_pos hq,
        dif_pos hq, zero_add, zero_add, ha.2]
      simp
    · rw [if_neg hki, if_neg hki, sub_zero, sub_zero]
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [ha.1 q.1.1 k hk, zero_mul, zero_mul]
      · rw [upper_apply, upper_apply]
        congr 2
        split_ifs with h
        · apply hxy
          show q.1.2.val - k.val < q.1.2.val - q.1.1.val
          have := h; rw [Fin.lt_def] at *; omega
        · rfl

theorem lowOf_coord {m : ℕ} (p : Fin m × Fin m → Prop) [DecidablePred p] (hp : ∀ q, p q → q.2 < q.1)
    (v : {q : Fin m × Fin m // p q} → ℂ) (q : {q : Fin m × Fin m // p q}) :
    C2.lowOf (fun q : {q : Fin m × Fin m // p q} => q.1) v q.1.1 q.1.2 = v q := by
  have hne : q.1.1 ≠ q.1.2 := (ne_of_lt (hp q.1 q.2)).symm
  simp only [C2.lowOf, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne hne, zero_add, Prod.mk.eta]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem LT_ct {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ C2.LTset m) : Lᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hL.1 j i h], fun i => by simp [hL.2 i]⟩

theorem UT_ct {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ C2.UTset m) : Uᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hU.1 j i h], fun i => by simp [hU.2 i]⟩

def swUT {m : ℕ} : G.UT m ≃ C2.Lidx m where
  toFun q := ⟨(q.1.2, q.1.1), q.2⟩
  invFun q := ⟨(q.1.2, q.1.1), q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fSp {m : ℕ} (w : Equiv.Perm (Fin m)) (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) : G.UT m → ℂ :=
  utc ((lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

theorem one_ne {m : ℕ} : ∀ a : Fin m, (fun _ => (1 : ℂ)) a ≠ 0 := fun _ => one_ne_zero

private theorem lowP_apply' {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) (i j : Fin m) :
    lowP w y i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j +
      if h : j < i ∧ w.symm j < w.symm i then y ⟨(i, j), h⟩ else 0 := by
  simp only [lowP, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh
      exact hb (Subtype.ext hh)
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hq
    apply h
    have := q.2
    rw [hq] at this
    exact this

theorem lowerUnipotent_mem {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) :
    lowP w y ∈ C2.LPg (C2.monoP w fun _ => (1 : ℂ)) := by
  have hP : C2.monoP w (fun _ => (1 : ℂ)) = U.wP w.symm := by
    ext i a
    simp [C2.monoP, U.wP, Equiv.symm_apply_eq]
  have hinv : (U.wP w.symm)⁻¹ = U.wP w := by
    rw [Matrix.inv_eq_left_inv]
    ext a b
    simp [U.wP, Matrix.mul_apply, Matrix.one_apply, Equiv.symm_apply_eq]
  have hent : ∀ a b, (U.wP w * lowP w y * U.wP w.symm) a b = lowP w y (w a) (w b) := by
    intro a b
    simp [U.wP, Matrix.mul_apply, Equiv.symm_apply_eq]
  refine ⟨⟨fun i j h => ?_, fun i => ?_⟩, ?_⟩
  · rw [lowP_apply', Matrix.one_apply_ne (ne_of_lt h), dif_neg (fun hh => lt_asymm h hh.1), zero_add]
  · rw [lowP_apply', Matrix.one_apply_eq, dif_neg (fun hh => lt_irrefl _ hh.1), add_zero]
  · rw [hP, hinv]
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · rw [hent, lowP_apply', Matrix.one_apply_ne (w.injective.ne (ne_of_lt h)),
        dif_neg (fun hh => lt_asymm h (by simpa using hh.2)), zero_add]
    · rw [hent, lowP_apply', Matrix.one_apply_eq, dif_neg (fun hh => lt_irrefl _ hh.1), add_zero]

theorem lowS_mem {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) :
    lowS w x ∈ C2.Lstg (C2.monoP w fun _ => (1 : ℂ)) := by
  exact Dx2.Rad.low_mem w (fun _ => 1) one_ne x

private theorem mul_mem_UTset {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA.1 i l h, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij h), mul_zero]
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem prod_UT {m : ℕ} (w : Equiv.Perm (Fin m)) (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) :
    (lowS w p.1)ᴴ * (lowP w p.2)ᴴ ∈ C2.UTset m :=
  mul_mem_UTset (LT_ct (lowS_mem w p.1).1) (LT_ct (lowerUnipotent_mem w p.2).1)

theorem upper_fSp {m : ℕ} (w : Equiv.Perm (Fin m)) (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) :
    G.upper (fSp w p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ :=
  upper_utc (prod_UT w p)

theorem fSp_eq {m : ℕ} (w : Equiv.Perm (Fin m)) :
    fSp w = (fun l : G.UT m → ℂ => star l) ∘ (fun (y : C2.Lidx m → ℂ) (i : G.UT m) => y (swUT i)) ∘
      (fun p : (C2.LPidx w → ℂ) × (C2.Lstidx w → ℂ) => fun q : C2.Lidx m =>
        (C2.lowOf (fun q : C2.LPidx w => q.1) p.1 * C2.lowOf (fun q : C2.Lstidx w => q.1) p.2) q.1.1 q.1.2) ∘
      Prod.swap := by
  funext p i
  show ((lowS w p.1)ᴴ * (lowP w p.2)ᴴ) i.1.1 i.1.2 =
    star ((C2.lowOf (fun q : C2.LPidx w => q.1) p.2 * C2.lowOf (fun q : C2.Lstidx w => q.1) p.1) i.1.2 i.1.1)
  rw [← Matrix.conjTranspose_mul, Matrix.conjTranspose_apply]
  rfl

theorem fSp_mp {m : ℕ} (w : Equiv.Perm (Fin m)) : MeasurePreserving (fSp w) volume volume := by
  rw [fSp_eq]
  exact Dx2.SplitM.vconj_mp.comp ((Dx2.SL.reindex_mp swUT).comp
    ((lower_splitting_measurable m w).comp (Measure.measurePreserving_swap)))

theorem fSp_inj {m : ℕ} (w : Equiv.Perm (Fin m)) : Function.Injective (fSp w) := by
  intro p p' h
  have h1 := congrArg G.upper h
  rw [upper_fSp, upper_fSp, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul] at h1
  have h2 := Matrix.conjTranspose_injective h1
  have hP : C2.IsMonomial (C2.monoP w fun _ => (1 : ℂ)) := ⟨w, _, one_ne, rfl⟩
  have hl : lowP w p.2 * lowS w p.1 ∈ C2.LTset m := C2x2.lt_mul (lowerUnipotent_mem w p.2).1 (lowS_mem w p.1).1
  obtain ⟨q, _, hq⟩ := lower_triangular_splitting m _ hP _ hl
  have e1 := hq (lowP w p.2, lowS w p.1) ⟨lowerUnipotent_mem w p.2, lowS_mem w p.1, rfl⟩
  have e2 := hq (lowP w p'.2, lowS w p'.1) ⟨lowerUnipotent_mem w p'.2, lowS_mem w p'.1, h2⟩
  have hy : lowP w p.2 = lowP w p'.2 := by rw [← e2] at e1; exact congrArg Prod.fst e1
  have hx : lowS w p.1 = lowS w p'.1 := by rw [← e2] at e1; exact congrArg Prod.snd e1
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · have := congrFun (congrFun hx q.1.1) q.1.2
    simp only [lowS] at this
    rwa [lowOf_coord _ (fun q h => h.1), lowOf_coord _ (fun q h => h.1)] at this
  · have := congrFun (congrFun hy q.1.1) q.1.2
    simp only [lowP] at this
    rwa [lowOf_coord _ (fun q h => h.1), lowOf_coord _ (fun q h => h.1)] at this

theorem fSp_surj {m : ℕ} (w : Equiv.Perm (Fin m)) : Function.Surjective (fSp w) := by
  intro u
  have hP : C2.IsMonomial (C2.monoP w fun _ => (1 : ℂ)) := ⟨w, _, one_ne, rfl⟩
  obtain ⟨q, ⟨hq1, hq2, hq⟩, _⟩ := lower_triangular_splitting m _ hP _ (UT_ct (upper_mem u))
  rw [← (lower_parabolic_coordinates m w _ one_ne).1] at hq1
  rw [← (lower_parabolic_coordinates m w _ one_ne).2] at hq2
  obtain ⟨y, hy⟩ := hq1
  obtain ⟨x, hx⟩ := hq2
  refine ⟨(x, y), ?_⟩
  have : (lowS w x)ᴴ * (lowP w y)ᴴ = G.upper u := by
    rw [← Matrix.conjTranspose_mul]
    show (C2.lowOf (fun q : C2.LPidx w => q.1) y * C2.lowOf (fun q : C2.Lstidx w => q.1) x)ᴴ = _
    rw [hy, hx, ← hq, Matrix.conjTranspose_conjTranspose]
  simp only [fSp]; rw [this, utc_upper]

def eSp {m : ℕ} (w : Equiv.Perm (Fin m)) : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT m → ℂ) where
  toEquiv := Equiv.ofBijective (fSp w) ⟨fSp_inj w, fSp_surj w⟩
  measurable_toFun := (fSp_mp w).measurable
  measurable_invFun := by
    intro s hs
    have hemb : MeasurableEmbedding (fSp w) := (fSp_mp w).measurable.measurableEmbedding (fSp_inj w)
    rw [← Equiv.image_eq_preimage_symm]
    exact hemb.measurableSet_image.2 hs

theorem splitUT : SplitUT := fun m w => ⟨eSp w, fSp_mp w, fun p => upper_fSp w p⟩

section cell

variable {m : ℕ} (σ : Equiv.Perm (Fin m))

def iota : C2.LPidx σ.symm ≃ U.LW σ where
  toFun q := ⟨(σ q.1.1, σ q.1.2), by
    obtain ⟨⟨i, j⟩, h1, h2⟩ := q
    simp only [Equiv.symm_symm] at h2
    exact ⟨h2, by simpa using h1⟩⟩
  invFun l := ⟨(σ.symm l.1.1, σ.symm l.1.2), by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := l
    simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
    exact ⟨h2, h1⟩⟩
  left_inv q := by ext <;> simp
  right_inv l := by ext <;> simp

theorem permutationMatrix_mul_apply (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (U.wP σ * M) i j = M (σ i) j := by
  simp [U.wP, Matrix.mul_apply]

theorem mul_wP_apply (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (M * U.wP σ) i j = M i (σ.symm j) := by
  simp [U.wP, Matrix.mul_apply, Equiv.apply_eq_iff_eq_symm_apply]

theorem lowW_apply (v : U.LW σ → ℂ) (a b : Fin m) :
    U.lowW σ v a b = (1 : Matrix (Fin m) (Fin m) ℂ) a b +
      if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0 := by
  rfl

theorem lowerUnipotent_symm_apply (y : C2.LPidx σ.symm → ℂ) (i j : Fin m) :
    lowP σ.symm y i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j +
      if h : j < i ∧ σ.symm.symm j < σ.symm.symm i then y ⟨(i, j), h⟩ else 0 := by
  simp only [lowP, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh
      exact hb (Subtype.ext hh)
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hq
    apply h
    have := q.2
    rw [hq] at this
    exact this

theorem permutationMatrix_mul_lowerUnipotent (y : C2.LPidx σ.symm → ℂ) :
    U.wP σ * U.lowW σ (fun l => y ((iota σ).symm l)) = lowP σ.symm y * U.wP σ := by
  ext i j
  rw [permutationMatrix_mul_apply, mul_wP_apply, lowW_apply, lowerUnipotent_symm_apply]
  congr 1
  · simp only [Matrix.one_apply, Equiv.eq_symm_apply]
  · by_cases h : j < σ i ∧ σ.symm j < σ.symm (σ i)
    · rw [dif_pos h, dif_pos ⟨by simpa using h.2, by simpa using h.1⟩]
      congr 1
      apply Subtype.ext
      simp [iota]
    · rw [dif_neg h, dif_neg]
      rintro ⟨h1, h2⟩
      exact h ⟨by simpa using h2, by simpa using h1⟩

theorem conj_lowW (y : C2.LPidx σ.symm → ℂ) :
    U.wP σ * U.lowW σ (fun l => y ((iota σ).symm l)) * (U.wP σ)⁻¹ = lowP σ.symm y := by
  have hw : U.wP σ = σ.toPEquiv.toMatrix := by
    ext a b
    simp [U.wP, PEquiv.toMatrix_apply]
  have hu : IsUnit (U.wP σ).det := by
    rw [hw, Matrix.det_permutation, isUnit_iff_ne_zero]
    exact_mod_cast (Equiv.Perm.sign σ).ne_zero
  rw [permutationMatrix_mul_lowerUnipotent, Matrix.mul_nonsing_inv_cancel_right _ _ hu]

theorem subS_eq (L : Matrix (Fin m) (Fin m) ℂ) : C2.simpleUp Lᴴ = conj (U.subS L) := by
  simp only [C2.simpleUp, U.subS, map_sum, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem supS_eq (M : Matrix (Fin m) (Fin m) ℂ) : U.supS M = C2.simpleUp M := rfl

theorem psi_conj (x : ℂ) : G.psi U.betaU x = C2.psiC cStd (conj x) := by
  unfold G.psi U.betaU C2.psiC cStd
  congr 3
  simp [Complex.mul_re]

theorem psi_star (x : ℂ) : G.psi U.betaU x = star (C2.psiC cStd x) := by
  simp only [G.psi, U.betaU, C2.psiC]
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [neg_mul]
  ring

end cell

theorem phiTopCoords : PhiTopCoords := by
  intro m σ w d d' V _ _ Φ hd' hM
  have hcol : ∀ a, w a = σ.symm a ∧ d' a = d a := by
    intro a
    have e := congrFun (congrFun hM (w a)) a
    simp only [C2.monoP, Matrix.of_apply, if_true] at e
    rw [U.hMat, permutationMatrix_mul_apply, Matrix.diagonal_apply] at e
    by_cases h : σ (w a) = a
    · refine ⟨?_, ?_⟩
      · rw [Equiv.eq_symm_apply]; exact h
      · rw [h, if_pos rfl] at e; exact e.symm
    · rw [if_neg h] at e; exact absurd e.symm (hd' a)
  have hw : w = σ.symm := Equiv.ext fun a => (hcol a).1
  have hdd : d' = d := funext fun a => (hcol a).2
  subst hw hdd
  unfold U.PhiTop

  set g : (U.LW σ → ℂ) × (G.UT m → ℂ) → V := fun y =>
    (G.psi U.betaU (U.subS (U.wP σ * U.lowW σ y.1 * (U.wP σ)⁻¹)) * G.psi U.betaU (U.supS (G.upper y.2))) •
      Φ (U.headH σ d' y.1 y.2) with hg
  have hT := Dx2.SL.probT m
  have h1 : (fun η : U.XiH m 0 σ => U.psiH U.betaU σ η • Φ (U.ZjH σ d' η (fun x => x.elim0))) =
      g ∘ Dx2.SL.dropE ((Fin 0 → Fin m → ℂ) × (Fin m → Fin 0 → ℂ)) ((U.LW σ → ℂ) × (G.UT m → ℂ)) := by
    funext η
    obtain ⟨⟨a0, b0⟩, v, u⟩ := η
    simp only [Function.comp_apply, Dx2.SL.dropE, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, hg, U.psiH, U.ZjH,
      Dx2.SL.zj_zero, Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero, add_zero, Dx2.SL.psi_add]
  have e1 : ∫ η : U.XiH m 0 σ, U.psiH U.betaU σ η • Φ (U.ZjH σ d' η (fun x => x.elim0)) ∂(U.muXiH m 0 σ) =
      ∫ y, g y := by
    rw [h1]
    unfold U.muXiH
    rw [Measure.volume_eq_prod]
    exact (Dx2.SL.dropE_mp _ _ volume volume).integral_comp' g
  rw [e1]

  set e : ((C2.LPidx σ.symm → ℂ) × (G.UT m → ℂ)) ≃ᵐ ((U.LW σ → ℂ) × (G.UT m → ℂ)) :=
    MeasurableEquiv.prodCongr (Dx2.SL.reE (iota σ).symm) (MeasurableEquiv.refl _) with he
  have hmp : MeasurePreserving e volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact (Dx2.SL.reindex_mp (iota σ).symm).prod (MeasurePreserving.id _)
  rw [← hmp.integral_comp' g]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun q => ?_
  obtain ⟨y, u⟩ := q
  simp only [hg, he, MeasurableEquiv.prodCongr, MeasurableEquiv.coe_mk, Equiv.prodCongr_apply, Prod.map,
    Dx2.SL.reE, MeasurableEquiv.refl_apply, Equiv.coe_fn_mk]
  rw [conj_lowW, psi_conj, supS_eq, psi_star, ← subS_eq]
  congr 1
  have : U.headH σ d' (fun l => y ((iota σ).symm l)) u = lowP σ.symm y * C2.monoP σ.symm d' * G.upper u := by
    rw [U.headH, permutationMatrix_mul_lowerUnipotent, ← hM, U.hMat]
    simp only [Matrix.mul_assoc]
  exact congrArg Φ this

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.UC

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

theorem minorsLU : MinorsLU := UC.minorsLU
theorem lstLeft : LstLeft := UC.lstLeft
theorem utLeft : UTLeft := UC.utLeft
theorem splitUT : SplitUT := UC.splitUT
theorem phiTopCoords : PhiTopCoords := UC.phiTopCoords

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
