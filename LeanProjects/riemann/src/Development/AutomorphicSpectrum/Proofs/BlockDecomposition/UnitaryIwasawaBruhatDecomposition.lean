import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.BruhatIw

section Mat

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

abbrev mat (g : GU σ n) : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem mat_mul_apply (g h : GU σ n) (i j : Fin n) :
    mat (g * h) i j = ∑ l, mat g i l * mat h l j := by
  show ((mat g) * (mat h)) i j = _
  rw [Matrix.mul_apply]

theorem mat_one_apply (i j : Fin n) : mat (1 : GU σ n) i j = if i = j then 1 else 0 := by
  show (1 : Matrix (Fin n) (Fin n) L) i j = _
  rw [Matrix.one_apply]

theorem mat_inv_apply (g : GU σ n) (i j : Fin n) : mat g⁻¹ i j = σ (mat g j.rev i.rev) :=
  (GlobalTheory.LGrp.mem_GU_iff σ n g.1).1 g.2 i j

theorem sum_mul_inv (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g i l * mat g⁻¹ l j = if i = j then 1 else 0 := by
  rw [← mat_mul_apply, mul_inv_cancel, mat_one_apply]

theorem sum_inv_mul (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g⁻¹ i l * mat g l j = if i = j then 1 else 0 := by
  rw [← mat_mul_apply, inv_mul_cancel, mat_one_apply]

theorem row_form (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g i l * σ (mat g j.rev l.rev) = if i = j then 1 else 0 := by
  rw [← sum_mul_inv g i j]
  exact Finset.sum_congr rfl fun l _ => by rw [mat_inv_apply]

theorem row_isotropic (g : GU σ n) {a : Fin n} (ha : a ≠ a.rev) :
    ∑ l, mat g a l * σ (mat g a l.rev) = 0 := by
  have h := row_form g a a.rev
  rwa [if_neg ha, Fin.rev_rev] at h

theorem row_ne_zero (g : GU σ n) (a : Fin n) : ∃ j, mat g a j ≠ 0 := by
  by_contra h
  push_neg at h
  have := sum_mul_inv g a a
  simp [h] at this

theorem exists_GU (T S : Matrix (Fin n) (Fin n) L) (h : T * S = 1)
    (hS : ∀ i j, S i j = σ (T j.rev i.rev)) : ∃ g : GU σ n, mat g = T :=
  ⟨⟨⟨T, S, h, mul_eq_one_comm.1 h⟩, (GlobalTheory.LGrp.mem_GU_iff σ n _).2 fun i j => hS i j⟩, rfl⟩

def trU (g : GU σ n) : GU σ n :=
  ⟨⟨(mat g).transpose, (mat g⁻¹).transpose,
    by rw [← Matrix.transpose_mul]
       show (mat (g⁻¹ * g)).transpose = 1
       rw [inv_mul_cancel]; exact Matrix.transpose_one,
    by rw [← Matrix.transpose_mul]
       show (mat (g * g⁻¹)).transpose = 1
       rw [mul_inv_cancel]; exact Matrix.transpose_one⟩,
   (GlobalTheory.LGrp.mem_GU_iff σ n _).2 fun i j => mat_inv_apply g j i⟩

theorem trU_trU (g : GU σ n) : trU (trU g) = g := by
  apply Subtype.ext; apply Units.ext; rfl

theorem trU_mul (g h : GU σ n) : trU (g * h) = trU h * trU g := by
  apply Subtype.ext; apply Units.ext
  show (mat g * mat h).transpose = (mat h).transpose * (mat g).transpose
  rw [Matrix.transpose_mul]

theorem trU_one : trU (1 : GU σ n) = 1 := by
  apply Subtype.ext; apply Units.ext
  exact Matrix.transpose_one

def eichM (σ : L →+* L) (p : Fin n) (z : Fin n → L) : Matrix (Fin n) (Fin n) L := fun i j =>
  if i = p then z j
  else if j = p.rev then (if i = p.rev then 1 else - σ (z i.rev))
  else if i = j then 1 else 0

theorem eich_dual (hσ : ∀ x, σ (σ x) = x) (p : Fin n) (z : Fin n → L) (i j : Fin n) :
    σ (eichM σ p z j.rev i.rev) =
      if j = p.rev then σ (z i.rev)
      else if i = p then (if j = p then 1 else - z j)
      else if i = j then 1 else 0 := by
  unfold eichM
  by_cases hj : j = p.rev
  · subst hj; simp
  · have h1 : ¬ j.rev = p := fun h => hj (by rw [← h, Fin.rev_rev])
    rw [if_neg h1, if_neg hj]
    by_cases hi : i = p
    · subst hi
      by_cases hj' : j = i
      · subst hj'; simp
      · have h2 : ¬ j.rev = i.rev := fun h => hj' (Fin.rev_injective h)
        simp [h2, hj', hσ]
    · have h2 : ¬ i.rev = p.rev := fun h => hi (Fin.rev_injective h)
      rw [if_neg h2, if_neg hi]
      by_cases hij : i = j
      · subst hij; simp
      · have h3 : ¬ j.rev = i.rev := fun h => hij (Fin.rev_injective h).symm
        simp [h3, hij]

theorem exists_eich (hσ : ∀ x, σ (σ x) = x) {p : Fin n} (hp : p ≠ p.rev) {z : Fin n → L} (hz : z p = 1)
    (hiso : ∑ c, z c * σ (z c.rev) = 0) : ∃ T : GU σ n, mat T = eichM σ p z := by
  refine exists_GU _ (Matrix.of fun i j => σ (eichM σ p z j.rev i.rev)) ?_ fun _ _ => rfl
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, eich_dual hσ]
  by_cases hi : i = p
  · subst hi
    simp only [eichM, if_true]
    by_cases hk : k = i.rev
    · simp only [hk, if_true]
      rw [hiso, if_neg hp]
    · simp only [if_neg hk]
      by_cases hki : k = i
      · subst hki
        rw [Finset.sum_eq_single k]
        · simp [hz]
        · intro j _ hj; simp [hj]
        · simp
      · have e : ∀ j, z j * (if j = i then (if k = i then 1 else - z k) else if j = k then 1 else 0) =
            (if j = i then z i * (- z k) else 0) + (if j = k then z k else 0) := by
          intro j
          by_cases h1 : j = i
          · subst h1; simp [hki, Ne.symm hki]
          · by_cases h2 : j = k
            · subst h2; simp [h1]
            · simp [h1, h2]
        simp only [e, Finset.sum_add_distrib]
        simp [hz, Ne.symm hki]
  · have e : ∀ j, eichM σ p z i j = (if i = j then 1 else 0) +
        (if j = p.rev then (if i = p.rev then 0 else - σ (z i.rev)) else 0) := by
      intro j
      unfold eichM
      rw [if_neg hi]
      by_cases h1 : j = p.rev
      · subst h1
        by_cases h2 : i = p.rev
        · simp [h2]
        · simp [h2]
      · simp [h1]
    simp only [e, add_mul, Finset.sum_add_distrib]
    have hpr : p.rev ≠ p := Ne.symm hp
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_neg hpr,
      Fin.rev_rev, hz, map_one]
    by_cases hk : k = p.rev
    · subst hk
      by_cases hi' : i = p.rev
      · subst hi'; simp [hz]
      · simp [hi', hi]
    · simp [hk, hi, Ne.symm hk]

theorem eich_row_pivot (σ : L →+* L) (p : Fin n) (z : Fin n → L) (j : Fin n) : eichM σ p z p j = z j := by
  simp [eichM]

theorem eich_col_pivot (σ : L →+* L) {p : Fin n} (hp : p ≠ p.rev) {z : Fin n → L} (hz : z p = 1) (i : Fin n) :
    eichM σ p z i p = if i = p then 1 else 0 := by
  unfold eichM
  by_cases hi : i = p
  · subst hi; simp [hz]
  · simp [hi, hp]

theorem eich_fix (σ : L →+* L) {p c : Fin n} {z : Fin n → L} (hz : z p = 1) (hc : z c = 0) (hc' : z c.rev = 0) :
    (∀ j, eichM σ p z c j = if c = j then 1 else 0) ∧ (∀ i, eichM σ p z i c = if i = c then 1 else 0) := by
  have h1 : c ≠ p := by
    rintro rfl; rw [hz] at hc; exact one_ne_zero hc
  have h2 : c ≠ p.rev := by
    rintro rfl; rw [Fin.rev_rev, hz] at hc'; exact one_ne_zero hc'
  constructor
  · intro j
    unfold eichM
    rw [if_neg h1]
    by_cases hj : j = p.rev
    · subst hj; simp [h2, hc']
    · simp [hj]
  · intro i
    unfold eichM
    by_cases hi : i = p
    · subst hi; simp [hc, Ne.symm h1]
    · simp [hi, h2]

theorem eich_lower (σ : L →+* L) {p : Fin n} {z : Fin n → L} (hz : ∀ c, p < c → z c = 0) {i j : Fin n} (hij : i < j) :
    eichM σ p z i j = 0 := by
  unfold eichM
  by_cases hi : i = p
  · subst hi; rw [if_pos rfl]; exact hz j hij
  · rw [if_neg hi]
    by_cases hj : j = p.rev
    · subst hj
      rw [if_pos rfl, if_neg hij.ne, hz i.rev (Fin.lt_rev_iff.2 hij), map_zero, neg_zero]
    · rw [if_neg hj, if_neg hij.ne]

theorem inv_fix {T : GU σ n} {c : Fin n} (hr : ∀ j, mat T c j = if c = j then 1 else 0)
    (hc : ∀ i, mat T i c = if i = c then 1 else 0) :
    (∀ j, mat T⁻¹ c j = if c = j then 1 else 0) ∧ (∀ i, mat T⁻¹ i c = if i = c then 1 else 0) := by
  constructor
  · intro j
    rw [← sum_mul_inv T c j]
    simp [hr]
  · intro i
    rw [← sum_inv_mul T i c]
    simp [hc]

def IsoAt (M : Matrix (Fin n) (Fin n) L) (a c : Fin n) : Prop :=
  M a c ≠ 0 ∧ (∀ j, j ≠ c → M a j = 0) ∧ ∀ i, i ≠ a → M i c = 0

theorem IsoAt.trU {g : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c) : IsoAt (mat (trU g)) c a :=
  ⟨h.1, h.2.2, h.2.1⟩

theorem IsoAt.mul_fix {g S : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c)
    (hr : ∀ j, mat S c j = if c = j then 1 else 0) (hc : ∀ i, mat S i c = if i = c then 1 else 0) :
    IsoAt (mat (g * S)) a c := by
  have e1 : ∀ j, mat (g * S) a j = mat g a c * (if c = j then 1 else 0) := by
    intro j
    rw [mat_mul_apply, Finset.sum_eq_single c, hr]
    · intro l _ hl; rw [h.2.1 l hl, zero_mul]
    · simp
  have e2 : ∀ i, mat (g * S) i c = mat g i c := by
    intro i
    rw [mat_mul_apply]
    simp [hc]
  refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
  · rw [e1]; simpa using h.1
  · rw [e1, if_neg (Ne.symm hj), mul_zero]
  · rw [e2, h.2.2 i hi]

theorem IsoAt.rev {g : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c) : IsoAt (mat g) a.rev c.rev := by
  have e1 : ∀ y, mat g⁻¹ y a * mat g a c = if y = c then 1 else 0 := by
    intro y
    rw [← sum_inv_mul g y c, Finset.sum_eq_single a]
    · intro l _ hl; rw [h.2.2 l hl, mul_zero]
    · simp
  have e2 : ∀ x, mat g a c * mat g⁻¹ c x = if a = x then 1 else 0 := by
    intro x
    rw [← sum_mul_inv g a x, Finset.sum_eq_single c]
    · intro l _ hl; rw [h.2.1 l hl, zero_mul]
    · simp
  have e3 : ∀ j, σ (mat g a.rev j) = mat g⁻¹ j.rev a := by
    intro j; rw [mat_inv_apply, Fin.rev_rev]
  have e4 : ∀ i, σ (mat g i c.rev) = mat g⁻¹ c i.rev := by
    intro i; rw [mat_inv_apply, Fin.rev_rev]
  refine ⟨fun h0 => ?_, fun j hj => ?_, fun i hi => ?_⟩
  · have h1 := e3 c.rev
    rw [Fin.rev_rev, h0, map_zero] at h1
    have h2 := e1 c
    rw [← h1, zero_mul, if_pos rfl] at h2
    exact zero_ne_one h2
  · have h2 := e1 j.rev
    have hne : j.rev ≠ c := fun hh => hj (by rw [← hh, Fin.rev_rev])
    rw [if_neg hne] at h2
    have h3 : mat g⁻¹ j.rev a = 0 := (mul_eq_zero.1 h2).resolve_right h.1
    rw [← e3] at h3
    exact (map_eq_zero σ).1 h3
  · have h2 := e2 i.rev
    have hne : a ≠ i.rev := fun hh => hi (by rw [hh, Fin.rev_rev])
    rw [if_neg hne] at h2
    have h3 : mat g⁻¹ c i.rev = 0 := (mul_eq_zero.1 h2).resolve_left h.1
    rw [← e4] at h3
    exact (map_eq_zero σ).1 h3

theorem clear_row {h T : GU σ n} {a p : Fin n} {u : L} (hrow : ∀ l, mat h a l = u * mat T p l) (j : Fin n) :
    mat (h * T⁻¹) a j = if p = j then u else 0 := by
  rw [mat_mul_apply]
  simp only [hrow, mul_assoc]
  rw [← Finset.mul_sum, sum_mul_inv]
  simp

def RedU (g : GU σ n) (k : ℕ) : Prop :=
  ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → ∃ c, IsoAt (mat g) b c

theorem iso_last (g : GU σ n) (a : Fin n) (h : ∀ b, b ≠ a → ∃ c, IsoAt (mat g) b c) :
    ∃ c, IsoAt (mat g) a c := by
  have hcol : ∀ c, mat g a c ≠ 0 → ∀ i, i ≠ a → mat g i c = 0 := by
    intro c hc i hi
    obtain ⟨d, hd⟩ := h i hi
    by_cases hcd : c = d
    · subst hcd; exact absurd (hd.2.2 a (Ne.symm hi)) hc
    · exact hd.2.1 c hcd
  obtain ⟨c, hc⟩ := row_ne_zero g a
  have hmul : ∀ j, mat g a j ≠ 0 → mat g⁻¹ c a * mat g a j = if c = j then 1 else 0 := by
    intro j hj
    rw [← sum_inv_mul g c j, Finset.sum_eq_single a]
    · intro l _ hl; rw [hcol j hj l hl, mul_zero]
    · simp
  refine ⟨c, ⟨hc, fun j hj => ?_, hcol c hc⟩⟩
  by_contra h0
  have h1 := hmul j h0
  rw [if_neg (Ne.symm hj)] at h1
  have h2 := hmul c hc
  rw [if_pos rfl] at h2
  have h3 : mat g⁻¹ c a = 0 := (mul_eq_zero.1 h1).resolve_right h0
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2

theorem mono_end (g : GU σ n) (h : ∀ a, ∃ c, IsoAt (mat g) a c) :
    ∃ (d w : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU d ∧ IsPermW w π ∧ g = d * w := by
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have := (hf a).2.2 b (Ne.symm hne)
    rw [hab] at this
    exact (hf b).1 this
  have hrev : ∀ a, f a.rev = (f a).rev := by
    intro a
    by_contra hne
    exact (hf a).rev.1 ((hf a.rev).2.1 _ (Ne.symm hne))
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : ∀ a, π a = f a := fun _ => rfl
  obtain ⟨w, hw⟩ := exists_GU (σ := σ) (Matrix.of fun a c => if c = f a then 1 else 0)
    (Matrix.of fun i j => σ (if i.rev = f j.rev then 1 else 0)) (by
      ext i k
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      rw [Finset.sum_eq_single (f i)]
      · have : (f i).rev.rev = f i := Fin.rev_rev _
        simp only [if_true, one_mul, hrev k, Fin.rev_injective.eq_iff, hinj.eq_iff]
        by_cases hik : i = k
        · simp [hik]
        · simp [hik, Ne.symm hik]
      · intro j _ hj; simp [hj]
      · simp) (by
      intro i j
      simp)
  have hw' : ∀ a c, mat w a c = if c = f a then 1 else 0 := by
    intro a c; rw [hw]; rfl
  refine ⟨g * w⁻¹, w, π, ?_, fun a c => hw' a c, by simp⟩
  intro i j hji
  show mat (g * w⁻¹) i j = 0
  rw [mat_mul_apply, Finset.sum_eq_single (f i)]
  · rw [mat_inv_apply, hw', if_neg, map_zero, mul_zero]
    intro hh
    rw [hrev] at hh
    exact hji.ne' (hinj (Fin.rev_injective hh))
  · intro l _ hl; rw [(hf i).2.1 l hl, zero_mul]
  · simp

end Mat

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem val_div_le {x u : L} (hu : u ≠ 0) (h : Valued.v x ≤ Valued.v u) : Valued.v (x / u) ≤ 1 := by
  rw [map_div₀]
  exact div_le_one_of_le₀ h zero_le'

theorem val_div_lt {x u : L} (hu : u ≠ 0) (h : Valued.v x < Valued.v u) : Valued.v (x / u) < 1 := by
  rw [map_div₀]
  exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hu))).2 h

theorem exists_pivot (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : Fin n → L) (hx : ∃ c, x c ≠ 0)
    (hiso : ∑ c, x c * σ (x c.rev) = 0) :
    ∃ p, x p ≠ 0 ∧ p ≠ p.rev ∧ (∀ c, Valued.v (x c) ≤ Valued.v (x p)) ∧
      ∀ c, c < p → Valued.v (x c) < Valued.v (x p) := by
  classical
  obtain ⟨c0, hc0⟩ := hx
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun c => Valued.v (x c)) ⟨c0, Finset.mem_univ _⟩
  let P : Finset (Fin n) := Finset.univ.filter (fun c => Valued.v (x c) = Valued.v (x m))
  have hP : P.Nonempty := ⟨m, by simp [P]⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = P.min' hP := ⟨_, rfl⟩
  have hpP : Valued.v (x p) = Valued.v (x m) := by
    rw [hpdef]; exact (Finset.mem_filter.1 (P.min'_mem hP)).2
  have hmax : ∀ c, Valued.v (x c) ≤ Valued.v (x p) := fun c => hpP ▸ hm c (Finset.mem_univ c)
  have hlt : ∀ c, c < p → Valued.v (x c) < Valued.v (x p) := by
    intro c hc
    refine lt_of_le_of_ne (hmax c) fun h => ?_
    have : p ≤ c := by
      rw [hpdef]; exact P.min'_le c (by simp [P, h, hpP])
    exact absurd hc (not_lt.2 this)
  have hne : x p ≠ 0 := by
    intro h0
    have := hmax c0
    rw [h0, map_zero, le_zero_iff] at this
    exact hc0 ((Valuation.zero_iff _).1 this)
  refine ⟨p, hne, fun hp => ?_, hmax, hlt⟩
  have hM : 0 < Valued.v (x p) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have hMM : Valued.v (x p) * Valued.v (x p) ≠ 0 := mul_ne_zero hM.ne' hM.ne'
  have hstrict : ∀ A B : WithZero (Multiplicative ℤ), A < Valued.v (x p) → B ≤ Valued.v (x p) →
      A * B < Valued.v (x p) * Valued.v (x p) := fun A B hA hB =>
    lt_of_le_of_lt (mul_le_mul' le_rfl hB) (mul_lt_mul_of_pos_right hA hM)
  have hrest : Valued.v (∑ c ∈ Finset.univ.erase p, x c * σ (x c.rev)) <
      Valued.v (x p) * Valued.v (x p) := by
    refine Valuation.map_sum_lt _ hMM fun c hc => ?_
    rw [map_mul, hσv]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with h | h
    · exact hstrict _ _ (hlt c h) (hmax _)
    · have h' : c.rev < p := by
        have := Fin.rev_lt_rev.2 h
        rwa [← hp] at this
      rw [mul_comm]
      exact hstrict _ _ (hlt _ h') (hmax _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← hp] at hiso
  have e : x p * σ (x p) = - ∑ c ∈ Finset.univ.erase p, x c * σ (x c.rev) := eq_neg_of_add_eq_zero_left hiso
  have h2 : Valued.v (x p * σ (x p)) = Valued.v (x p) * Valued.v (x p) := by rw [map_mul, hσv]
  rw [e, Valuation.map_neg] at h2
  exact hrest.ne h2

theorem iso_scale {u : L} (hu : u ≠ 0) {x : Fin n → L} (h : ∑ c, x c * σ (x c.rev) = 0) :
    ∑ c, (x c / u) * σ (x c.rev / u) = 0 := by
  have hsu : σ u ≠ 0 := (map_ne_zero σ).2 hu
  have e : ∀ c, (x c / u) * σ (x c.rev / u) = (u * σ u)⁻¹ * (x c * σ (x c.rev)) := by
    intro c
    rw [map_div₀]
    field_simp
  simp only [e, ← Finset.mul_sum, h, mul_zero]

theorem eich_mem_iw (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {p : Fin n} {z : Fin n → L} {T : GU σ n}
    (hT : mat T = eichM σ p z) (h1 : ∀ c, Valued.v (z c) ≤ 1) (h2 : ∀ c, c < p → Valued.v (z c) < 1) :
    T ∈ IwU σ n := by
  refine (mem_iwU_iff hσv T).2 ⟨fun i j => ?_, fun i j hji => ?_⟩
  · show Valued.v (mat T i j) ≤ 1
    rw [hT]
    unfold eichM
    split_ifs
    · exact h1 j
    · simp
    · rw [Valuation.map_neg, hσv]; exact h1 _
    · simp
    · simp
  · show Valued.v (mat T i j) < 1
    rw [hT]
    unfold eichM
    by_cases hi : i = p
    · subst hi; rw [if_pos rfl]; exact h2 j hji
    · rw [if_neg hi]
      by_cases hj : j = p.rev
      · subst hj
        rw [if_pos rfl, if_neg hji.ne', Valuation.map_neg, hσv]
        exact h2 _ (Fin.rev_lt_iff.2 hji)
      · rw [if_neg hj, if_neg hji.ne']
        simp

theorem step (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) {k : ℕ}
    (hk : 2 * k + 1 < n) (hr : RedU g k) :
    ∃ b i g' : GU σ n, IsBorelU b ∧ i ∈ IwU σ n ∧ g = b * g' * i ∧ RedU g' (k + 1) := by
  classical
  obtain ⟨a, hav⟩ : ∃ a : Fin n, a.val = n - 1 - k := ⟨⟨n - 1 - k, by omega⟩, rfl⟩
  have ha : a ≠ a.rev := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_rev] at this
    omega
  have hfinA : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → a ≠ b := by
    rintro b hb rfl
    omega
  have hfinR : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → (b.rev.val < k ∨ n ≤ b.rev.val + k) := by
    intro b hb
    have := b.isLt
    rw [Fin.val_rev]
    omega
  obtain ⟨p, hxp, hp, hmax, hlt⟩ := exists_pivot hσv (mat g a) (row_ne_zero g a) (row_isotropic g ha)
  obtain ⟨u, hu⟩ : ∃ u, u = mat g a p := ⟨_, rfl⟩
  rw [← hu] at hxp
  rw [← hu] at hmax hlt
  obtain ⟨z, hz⟩ : ∃ z : Fin n → L, z = fun c => mat g a c / u := ⟨_, rfl⟩
  have hzp : z p = 1 := by rw [hz]; show mat g a p / u = 1; rw [← hu]; exact div_self hxp
  have hziso : ∑ c, z c * σ (z c.rev) = 0 := by
    rw [hz]; exact iso_scale hxp (row_isotropic g ha)
  obtain ⟨T, hT⟩ := exists_eich hσ hp hzp hziso
  have hTI : T ∈ IwU σ n := eich_mem_iw hσv hT (fun c => by rw [hz]; exact val_div_le hxp (hmax c))
    (fun c hc => by rw [hz]; exact val_div_lt hxp (hlt c hc))
  have hrow1 : ∀ l, mat g a l = u * mat T p l := by
    intro l
    rw [hT, eich_row_pivot, hz]
    show mat g a l = u * (mat g a l / u)
    field_simp
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g * T⁻¹ := ⟨_, rfl⟩
  have h1 : ∀ j, mat g₁ a j = if p = j then u else 0 := by
    rw [hg₁]; exact clear_row hrow1
  have hfin : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c →
      mat g a c = 0 ∧ mat g a c.rev = 0 := fun b c hb hbc =>
    ⟨hbc.2.2 a (hfinA b hb), hbc.rev.2.2 a (hfinA b.rev (hfinR b hb))⟩
  have hpne : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → p ≠ c := by
    rintro b c hb hbc rfl
    exact hxp (hu.trans (hfin b p hb hbc).1)
  have hiso1 : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → IsoAt (mat g₁) b c := by
    intro b c hb hbc
    obtain ⟨e1, e2⟩ := hfin b c hb hbc
    have hf := eich_fix σ (c := c) hzp (by rw [hz]; simp [e1]) (by rw [hz]; simp [e2])
    rw [← hT] at hf
    obtain ⟨r, s⟩ := inv_fix hf.1 hf.2
    rw [hg₁]
    exact hbc.mul_fix r s
  obtain ⟨G, hG⟩ : ∃ G, G = trU g₁ := ⟨_, rfl⟩
  have hGe : ∀ i j, mat G i j = mat g₁ j i := by intro i j; rw [hG]; rfl
  have hGa : mat G p a = u := by rw [hGe, h1]; simp
  obtain ⟨z', hz'⟩ : ∃ z' : Fin n → L, z' = fun c => mat G p c / u := ⟨_, rfl⟩
  have hz'a : z' a = 1 := by rw [hz']; show mat G p a / u = 1; rw [hGa]; exact div_self hxp
  have hz'iso : ∑ c, z' c * σ (z' c.rev) = 0 := by
    rw [hz']; exact iso_scale hxp (row_isotropic G hp)
  have hz'0 : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → z' b = 0 := by
    intro b hb
    obtain ⟨c, hbc⟩ := hr b hb
    rw [hz']
    show mat G p b / u = 0
    rw [hGe, (hiso1 b c hb hbc).2.1 p (hpne b c hb hbc), zero_div]
  obtain ⟨T', hT'⟩ := exists_eich hσ ha hz'a hz'iso
  have hrow2 : ∀ l, mat G p l = u * mat T' a l := by
    intro l
    rw [hT', eich_row_pivot, hz']
    show mat G p l = u * (mat G p l / u)
    field_simp
  obtain ⟨G₂, hG₂⟩ : ∃ G₂, G₂ = G * T'⁻¹ := ⟨_, rfl⟩
  have h2 : ∀ j, mat G₂ p j = if a = j then u else 0 := by
    rw [hG₂]; exact clear_row hrow2
  have hinvcol : ∀ i, mat T'⁻¹ i a = if i = a then 1 else 0 := by
    intro i
    rw [← sum_inv_mul T' i a]
    simp [hT', eich_col_pivot σ ha hz'a]
  have h3 : ∀ i, mat G₂ i a = mat G i a := by
    intro i
    rw [hG₂, mat_mul_apply]
    simp [hinvcol]
  obtain ⟨g₂, hg₂⟩ : ∃ g₂, g₂ = trU G₂ := ⟨_, rfl⟩
  have hg₂e : ∀ i j, mat g₂ i j = mat G₂ j i := by intro i j; rw [hg₂]; rfl
  have hIso : IsoAt (mat g₂) a p := by
    refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [hg₂e, h2, if_pos rfl]; exact hxp
    · rw [hg₂e, h3, hGe, h1, if_neg (Ne.symm hj)]
    · rw [hg₂e, h2, if_neg (Ne.symm hi)]
  have hiso2 : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → IsoAt (mat g₂) b c := by
    intro b c hb hbc
    have hf := eich_fix σ (c := b) hz'a (hz'0 b hb) (hz'0 b.rev (hfinR b hb))
    rw [← hT'] at hf
    obtain ⟨r, s⟩ := inv_fix hf.1 hf.2
    have i1 : IsoAt (mat G) c b := by rw [hG]; exact (hiso1 b c hb hbc).trU
    have i2 := i1.mul_fix r s
    rw [← hG₂] at i2
    rw [hg₂]
    exact i2.trU
  have hB : IsBorelU (trU T') := by
    intro i j hji
    show mat T' j i = 0
    rw [hT']
    refine eich_lower σ (fun c hc => hz'0 c (Or.inr ?_)) hji
    have := Fin.lt_def.1 hc
    omega
  refine ⟨trU T', T, g₂, hB, hTI, ?_, fun b hb => ?_⟩
  · have e : trU T' * g₂ = g₁ := by
      rw [hg₂, hG₂, trU_mul, ← mul_assoc, ← trU_mul, inv_mul_cancel, trU_one, one_mul, hG, trU_trU]
    rw [e, hg₁, inv_mul_cancel_right]
  · by_cases hbk : b.val < k ∨ n ≤ b.val + k
    · obtain ⟨c, hc⟩ := hr b hbk
      exact ⟨c, hiso2 b c hbk hc⟩
    · have : b = a ∨ b = a.rev := by
        have := b.isLt
        simp only [Fin.ext_iff, Fin.val_rev]
        omega
      rcases this with rfl | rfl
      · exact ⟨p, hIso⟩
      · exact ⟨p.rev, hIso.rev⟩

theorem reduce (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) (k : ℕ)
    (hk : 2 * k ≤ n) : ∃ b i g' : GU σ n, IsBorelU b ∧ i ∈ IwU σ n ∧ g = b * g' * i ∧ RedU g' k := by
  induction k with
  | zero =>
    refine ⟨1, 1, g, Formalism.UG.P.fSatake_borel_one, one_mem _, by simp, fun b hb => ?_⟩
    have := b.isLt
    omega
  | succ k ih =>
    obtain ⟨b, i, g', hb, hi, e, hr⟩ := ih (by omega)
    obtain ⟨b', i', g'', hb', hi', e', hr'⟩ := step hσ hσv g' (by omega) hr
    refine ⟨b * b', i' * i, g'', Formalism.UG.P.fSatake_borel_mul hb hb', mul_mem hi' hi, ?_, hr'⟩
    rw [e, e']
    simp only [mul_assoc]

end Val

theorem bruhat_iwasawa : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n,
    ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  intro L _ _ σ n hσ hσv g
  obtain ⟨b, i, g', hb, hi, e, hr⟩ := reduce hσ hσv g (n / 2) (by omega)
  have hall : ∀ a, ∃ c, IsoAt (mat g') a c := by
    intro a
    by_cases ha : a.val < n / 2 ∨ n ≤ a.val + n / 2
    · exact hr a ha
    · refine iso_last g' a fun b hb => hr b ?_
      have h1 : b.val ≠ a.val := fun h => hb (Fin.ext h)
      have := b.isLt
      omega
  obtain ⟨d, w, π, hd, hw, e'⟩ := mono_end g' hall
  refine ⟨b * d, w, i, π, Formalism.UG.P.fSatake_borel_mul hb hd, hw, hi, ?_⟩
  rw [e, e']
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.BruhatIw

end
