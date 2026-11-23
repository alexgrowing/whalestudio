import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

namespace RowTypeInv

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE

section Alg

variable {R : Type*} [CommRing R]

theorem superdiag_add (n r : ℕ) (hr : r ≤ n) (m m' : ℕ → ℕ → R)
    (hm : ∀ s < r, ∀ p, s ≤ p → p < n → m p s = if p = s then 1 else 0)
    (hm' : ∀ s < r, ∀ p, s ≤ p → p < n → m' p s = if p = s then 1 else 0)
    (h : ∀ p < n, ∀ p' < n, ∑ l ∈ Finset.range n, m p l * m' l p' = if p = p' then 1 else 0)
    (i : ℕ) (hi : i + 1 < r) : m i (i + 1) + m' i (i + 1) = 0 := by
  have h1 := h i (by omega) (i + 1) (by omega)
  rw [if_neg (by omega), Finset.sum_eq_add_of_mem i (i + 1) (by simp; omega) (by simp; omega) (by omega)] at h1
  · rw [hm i (by omega) i le_rfl (by omega), hm' (i + 1) hi (i + 1) le_rfl (by omega)] at h1
    simp only [if_true, one_mul, mul_one] at h1
    rw [add_comm]
    exact h1
  · intro l hl hne
    rw [Finset.mem_range] at hl
    rcases lt_or_gt_of_ne hne.1 with h2 | h2
    · rw [hm l (by omega) i h2.le (by omega), if_neg (by omega), zero_mul]
    · rw [hm' (i + 1) hi l h2 hl, if_neg hne.2, mul_zero]

theorem block_mul (n a t : ℕ) (ha : a + t ≤ n) (m m' : ℕ → ℕ → R)
    (hm : ∀ p p', p' < a → a ≤ p → p < n → m p p' = 0)
    (hm' : ∀ p p', p' < a + t → a + t ≤ p → p < n → m' p p' = 0)
    (h : ∀ p < n, ∀ p' < n, ∑ l ∈ Finset.range n, m p l * m' l p' = if p = p' then 1 else 0) :
    (Matrix.of fun s s' : Fin t => m (a + s.1) (a + s'.1)) *
      (Matrix.of fun s s' : Fin t => m' (a + s.1) (a + s'.1)) = 1 := by
  ext s s'
  have hs := s.2
  have hs' := s'.2
  have h1 := h (a + s.1) (by omega) (a + s'.1) (by omega)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a),
    Finset.sum_eq_zero (s := Finset.range b), zero_add, add_zero] at h1
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun u => m (a + s.1) (a + u) * m' (a + u) (a + s'.1)) t, h1]
    simp [Fin.ext_iff]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hm' _ _ (by omega) (by omega) (by omega), mul_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hm _ _ hl (by omega) (by omega), zero_mul]

end Alg

section Red

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_one : IntAt P (1 : E) := by simpa using IntAt.coe P 1

theorem intAt_zero : IntAt P (0 : E) := by simpa using IntAt.coe P 0

theorem reduction_one₂ : redP P (1 : E) = 1 := by simpa using reduction_coe P 1

theorem reduction_zero : redP P (0 : E) = 0 := by simpa using reduction_coe P 0

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := intAt_one P
  add_mem' := IntAt.add
  zero_mem' := intAt_zero P
  neg_mem' := fun {a} ha => by
    have := (IntAt.coe P (-1)).mul ha
    simpa using this

noncomputable def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := reduction_one₂ P
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := reduction_zero P
  map_add' a b := reduction_add a.2 b.2

theorem reduction_sum₂ {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h := map_sum (redHom P) (fun i => (⟨f i, hf i⟩ : intRing P)) s
  have h2 : ((∑ i ∈ s, (⟨f i, hf i⟩ : intRing P) : intRing P) : E) = ∑ i ∈ s, f i := by
    simp
  rw [← h2]
  exact h

theorem reduction_det {t : ℕ} (A : Matrix (Fin t) (Fin t) E) (hA : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let B : Matrix (Fin t) (Fin t) (intRing P) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have h1 : (B.det : E) = A.det := by
    have := (intRing P).subtype.map_det B
    exact this
  have h2 := (redHom P).map_det B
  rw [← h1]
  exact h2

theorem reduction_eq_zero_of_integral_inv_mul {q : ℕ} (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {a : E}
    (h : IntAt P ((q : E)⁻¹ * a)) : redP P a = 0 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : a = algebraMap (𝓞 E) E (q : 𝓞 E) * ((q : E)⁻¹ * a) := by
    rw [map_natCast, mul_inv_cancel_left₀ hq']
  rw [e, reduction_mul (IntAt.coe P _) h, reduction_coe, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul]

variable {P} in
theorem unitV_mul {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a * redP P b = 1) : unitV χ a * unitV χ b = 1 := by
  have ha : IsUnit (redP P a) := IsUnit.of_mul_eq_one _ h
  have hb : IsUnit (redP P b) := IsUnit.of_mul_eq_one_right _ h
  unfold unitV
  rw [dif_pos ha, dif_pos hb, ← Units.val_mul, ← map_mul]
  have : ha.unit * hb.unit = 1 := Units.ext (by simpa using h)
  rw [this, map_one, Units.val_one]

end Red

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem mem_sclLat (N : ℕ) (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  simp

theorem fIdx_zero (k₀ n s : ℕ) : fIdx k₀ 0 n s = s := by
  unfold fIdx
  split_ifs <;> omega

theorem fPos_zero (k₀ n l : ℕ) (hl : l < n) : fPos k₀ 0 n l = l := by
  unfold fPos
  split_ifs <;> omega

theorem scE_lt (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) (hl : l < n) : scE n ex l = 0 := if_pos hl

theorem mem_lamY (n : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + 0)) :
    v ∈ lamY P q n 0 ex ↔ ∀ l : Fin (n + 0), IntAt P (v l) := by
  unfold lamY
  rw [mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [scE_lt n ex l.1 l.2]
  simp

theorem mem_flagG (k₀ n s : ℕ) (v : Sp E (n + 0)) :
    v ∈ flagG P q k₀ n 0 s ↔
      ∀ l : Fin (n + 0), IntAt P (((q : E) ^ (if s ≤ l.1 then 1 else 0 : ℤ))⁻¹ * v l) := by
  unfold flagG
  rw [mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [scE_lt n _ l.1 l.2, fPos_zero k₀ n l.1 l.2, zero_add]

noncomputable def ent {N : ℕ} (g : HomE E N N) (p p' : ℕ) : E := atN (g (eN E N p')) p

omit [NumberField E] [StarRing E] in
theorem entB_eq (k₀ n : ℕ) (ex : ℕ → ℕ) (g : HomE E (n + 0) (n + 0)) (p p' : ℕ) (hp : p < n) (hp' : p' < n) :
    entB q k₀ 0 n 0 n ex ex g p p' = ent g p p' := by
  unfold entB ent
  rw [fIdx_zero, fIdx_zero, scE_lt n ex p hp, scE_lt n ex p' hp']
  simp

omit [NumberField E] [StarRing E] in
theorem ent_mul {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N) (p p' : ℕ) (hp : p < N) (hp' : p' < N) :
    ∑ l ∈ Finset.range N, ent g.toLinearMap p l * ent (g⁻¹).toLinearMap l p' = if p = p' then 1 else 0 := by
  have e : ∀ v : Sp E N, v = ∑ l ∈ Finset.range N, atN v l • eN E N l := by
    intro v
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i.1]
    · simp [atN, eN]
    · intro l _ hl
      simp [eN, hl.symm]
    · intro h
      exact absurd (Finset.mem_range.2 i.2) h
  have h1 : g (g⁻¹ (eN E N p')) = eN E N p' := LinearEquiv.apply_symm_apply g _
  rw [e (g⁻¹ (eN E N p')), map_sum] at h1
  have h2 := congrFun h1 ⟨p, hp⟩
  rw [Finset.sum_apply] at h2
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (h2.trans ?_)
  · rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    congr 1
    unfold ent atN
    rw [dif_pos hp]
    rfl
  · simp [eN]

variable {P q} {k₀ r t n : ℕ} {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)}

theorem intAt_ent (hg : g ∈ JG P q k₀ r t n 0) (p p' : ℕ) : IntAt P (ent g.toLinearMap p p') := by
  have h1 : eN E (n + 0) p' ∈ lamY P q n 0 fun i => i + 1 := by
    rw [mem_lamY]
    intro l
    unfold eN
    split_ifs
    exacts [intAt_one P, intAt_zero P]
  have h2 := (mem_lamY P q n _ _).1 ((hg.1 _).2 h1)
  unfold ent atN
  split_ifs
  exacts [h2 _, intAt_zero P]

theorem red_ent_block (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) (hg : g ∈ JG P q k₀ r t n 0) (i p p' : ℕ)
    (h : p' < r + i * t) (h' : r + i * t ≤ p) (hp : p < n) : redP P (ent g.toLinearMap p p') = 0 := by
  have h1 : eN E (n + 0) p' ∈ flagG P q k₀ n 0 (r + i * t) := by
    rw [mem_flagG]
    intro l
    unfold eN
    by_cases hl : l.1 = p'
    · rw [if_pos hl, if_neg (by omega)]
      simpa using intAt_one P
    · rw [if_neg hl, mul_zero]
      exact intAt_zero P
  have h2 := (mem_flagG P q k₀ n _ _).1 ((hg.2.1 _ ⟨i, rfl⟩ _).2 h1) ⟨p, hp⟩
  rw [if_pos h', zpow_one] at h2
  have h3 := reduction_eq_zero_of_integral_inv_mul P hq hP h2
  unfold ent atN
  rw [dif_pos (show p < n + 0 from hp)]
  exact h3

theorem red_ent_uni (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) (hg : g ∈ JG P q k₀ r t n 0) (hr : r ≤ n) (s : ℕ)
    (hs : s < r) (p : ℕ) (h : s ≤ p) (hp : p < n) :
    redP P (ent g.toLinearMap p s) = if p = s then 1 else 0 := by
  have hb : bvecG E q k₀ n 0 s = eN E (n + 0) s := by
    unfold bvecG
    rw [fIdx_zero, scE_lt n _ s (by omega)]
    simp
  have h1 := (hg.2.2 s hs).2
  rw [hb] at h1
  have h2 := (mem_flagG P q k₀ n _ _).1 h1 ⟨p, hp⟩
  rw [if_pos h, zpow_one] at h2
  have h3 := reduction_eq_zero_of_integral_inv_mul P hq hP h2
  have h4 : ent g.toLinearMap p s = g (eN E (n + 0) s) ⟨p, hp⟩ := by
    unfold ent atN
    rw [dif_pos (show p < n + 0 from hp)]
    rfl
  have h5 : IntAt P (if p = s then 1 else 0 : E) := by
    split_ifs
    exacts [intAt_one P, intAt_zero P]
  have h6 : IntAt P (ent g.toLinearMap p s - if p = s then 1 else 0) :=
    (intRing P).sub_mem (intAt_ent hg p s) h5
  have h7 : redP P (ent g.toLinearMap p s - if p = s then 1 else 0) = 0 := by
    rw [h4]
    exact h3
  rw [← sub_add_cancel (ent g.toLinearMap p s) (if p = s then 1 else 0), reduction_add h6 h5, h7, zero_add]
  split_ifs
  exacts [reduction_one₂ P, reduction_zero P]

theorem red_ent_mul (hg : g ∈ JG P q k₀ r t n 0) (p : ℕ) (hp : p < n) (p' : ℕ) (hp' : p' < n) :
    ∑ l ∈ Finset.range n, redP P (ent g.toLinearMap p l) * redP P (ent (g⁻¹).toLinearMap l p') =
      if p = p' then 1 else 0 := by
  have hg' := Subgroup.inv_mem _ hg
  have h1 := congrArg (redP P) (ent_mul g p p' hp hp')
  rw [reduction_sum₂ P _ _ fun l => (intAt_ent hg p l).mul (intAt_ent hg' l p')] at h1
  refine Eq.trans (Finset.sum_congr rfl fun l _ => (reduction_mul (intAt_ent hg p l) (intAt_ent hg' l p')).symm)
    (h1.trans ?_)
  split_ifs
  exacts [reduction_one₂ P, reduction_zero P]

end Ent

end RowTypeInv

open RowTypeInv Formalism.L2.Col.LocE in

theorem lamGB_mul_lamGB_inv (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j n : ℕ)
    (hn : r + j * t ≤ n) (g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) (hg : g ∈ LocE.JG P q k₀ r t n 0) :
    LocE.lamGB q ψ₀ χ k₀ r t j n 0 g.toLinearMap * LocE.lamGB q ψ₀ χ k₀ r t j n 0 (g⁻¹).toLinearMap = 1 := by
  have hg' := Subgroup.inv_mem _ hg
  have hr : r ≤ n := by omega
  have e1 : ∀ h ∈ LocE.JG P q k₀ r t n 0,
      redP P (∑ i ∈ Finset.range (r - 1),
        entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) h.toLinearMap i (i + 1)) =
      ∑ i ∈ Finset.range (r - 1), redP P (ent h.toLinearMap i (i + 1)) := by
    intro h hh
    rw [← reduction_sum₂ P _ _ fun i => intAt_ent hh i (i + 1)]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact entB_eq q k₀ n _ _ _ _ (by omega) (by omega)
  have hb : ∀ i < j, r + i * t + t ≤ n := by
    intro i hi
    have : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi
    rw [add_mul, one_mul] at this
    omega
  have e2 : ∀ h ∈ LocE.JG P q k₀ r t n 0, ∀ i < j,
      redP P (Matrix.det (Matrix.of fun s s' : Fin t =>
        entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) h.toLinearMap (r + i * t + s.1) (r + i * t + s'.1))) =
      Matrix.det (Matrix.of fun s s' : Fin t => redP P (ent h.toLinearMap (r + i * t + s.1) (r + i * t + s'.1))) := by
    intro h hh i hi
    have hi' := hb i hi
    have e : (Matrix.of fun s s' : Fin t =>
        entB q k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) h.toLinearMap (r + i * t + s.1) (r + i * t + s'.1)) =
        Matrix.of fun s s' : Fin t => ent h.toLinearMap (r + i * t + s.1) (r + i * t + s'.1) := by
      ext s s'
      have := s.2
      have := s'.2
      exact entB_eq q k₀ n _ _ _ _ (by omega) (by omega)
    rw [e]
    exact reduction_det P _ fun s s' => intAt_ent hh _ _
  unfold lamGB lamGv
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul, e1 g hg, e1 _ hg', ← Finset.sum_add_distrib,
    Finset.sum_eq_zero, AddChar.map_zero_eq_one, one_mul, ← Finset.prod_mul_distrib]
  · refine Finset.prod_eq_one fun i hi => unitV_mul _ ?_
    rw [Finset.mem_range] at hi
    rw [e2 g hg i hi, e2 _ hg' i hi, ← Matrix.det_mul,
      block_mul n (r + i * t) t (hb i hi) (fun p p' => redP P (ent g.toLinearMap p p'))
        (fun p p' => redP P (ent (g⁻¹).toLinearMap p p'))
        (fun p p' h h' hp => red_ent_block hq hP hg i p p' h h' hp)
        (fun p p' h h' hp => red_ent_block hq hP hg' (i + 1) p p' (by rw [add_mul, one_mul]; omega)
          (by rw [add_mul, one_mul]; omega) hp)
        (red_ent_mul hg), Matrix.det_one]
  · intro i hi
    rw [Finset.mem_range] at hi
    exact superdiag_add n r hr (fun p p' => redP P (ent g.toLinearMap p p'))
      (fun p p' => redP P (ent (g⁻¹).toLinearMap p p')) (red_ent_uni hq hP hg hr) (red_ent_uni hq hP hg' hr)
      (red_ent_mul hg) i (by omega)

end GlobalTheory
