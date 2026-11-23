import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PrimGood

section Norm

variable {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

theorem val_norm (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) {Δ : L} (hΔ : w Δ = 1)
    (hn : ¬ IsSquare Δ) (a c : L) : w (a ^ 2 - Δ * c ^ 2) = max (w a) (w c) ^ 2 := by
  have ha2 : w (a ^ 2) = w a ^ 2 := map_pow _ _ _
  have hb2 : w (Δ * c ^ 2) = w c ^ 2 := by rw [map_mul, hΔ, one_mul, map_pow]
  rcases lt_trichotomy (w a) (w c) with h | h | h
  · have hlt : w (a ^ 2) < w (Δ * c ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_right hlt, hb2, max_eq_right h.le]
  · rw [← h, max_self]
    by_cases ha : a = 0
    · have hc : c = 0 := by
        rw [ha, map_zero] at h
        exact (Valuation.zero_iff w).1 h.symm
      simp [ha, hc]
    have ha0 : w a ≠ 0 := (Valuation.ne_zero_iff w).2 ha
    have hc : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact ha0 h
    have hle : w (a ^ 2 - Δ * c ^ 2) ≤ w a ^ 2 := by
      refine (w.map_sub _ _).trans (max_le ha2.le ?_)
      rw [hb2, h]
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      apply hn
      have e : Δ * (c / a) ^ 2 - 1 = -((a ^ 2 - Δ * c ^ 2) / a ^ 2) := by
        field_simp; ring
      have hs : IsSquare (Δ * (c / a) ^ 2) := by
        apply hsq
        rw [e, Valuation.map_neg, map_div₀, ha2, div_lt_one₀ (pow_pos (zero_lt_iff.2 ha0) 2)]
        exact hlt
      obtain ⟨r, hr⟩ := hs
      refine ⟨r * a / c, ?_⟩
      have : Δ = (Δ * (c / a) ^ 2) * (a / c) ^ 2 := by field_simp
      rw [this, hr]; ring
    · exact heq
  · have hlt : w (Δ * c ^ 2) < w (a ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_left hlt, ha2, max_eq_left h.le]

end Norm

section Quad

variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)

theorem repr_coord (s t : L) :
    B.repr (s • B 0 + t • B 1) 0 = s ∧ B.repr (s • B 0 + t • B 1) 1 = t := by
  simp [Finsupp.single_apply]

variable {B} {Δ : L}

theorem coord_eq (h0 : B 0 = 1) (x : K) :
    x = algebraMap L K (B.repr x 0) + algebraMap L K (B.repr x 1) * B 1 := by
  have h := (B.sum_repr x).symm
  rw [Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact h

theorem repr_one (h0 : B 0 = 1) : B.repr 1 0 = 1 ∧ B.repr 1 1 = 0 := by
  rw [← h0]; simp [Finsupp.single_apply]

theorem repr_mul (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x y : K) :
    B.repr (x * y) 0 = B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1) ∧
    B.repr (x * y) 1 = B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0 := by
  have hx := coord_eq h0 x
  have hy := coord_eq h0 y
  have e : x * y = (B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1)) • B 0 +
      (B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0) • B 1 := by
    have e1 : x * y = (algebraMap L K (B.repr x 0) + algebraMap L K (B.repr x 1) * B 1) *
        (algebraMap L K (B.repr y 0) + algebraMap L K (B.repr y 1) * B 1) :=
      congrArg₂ (· * ·) hx hy
    rw [e1, Algebra.smul_def, Algebra.smul_def, h0]
    simp only [map_add, map_mul]
    linear_combination (algebraMap L K (B.repr x 1) * algebraMap L K (B.repr y 1)) * h1
  have := repr_coord B (B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1))
    (B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0)
  rw [← e] at this
  exact this

variable (B Δ) in

def nrm (x : K) : L := B.repr x 0 ^ 2 - Δ * B.repr x 1 ^ 2

theorem nrm_mul (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x y : K) :
    nrm B Δ (x * y) = nrm B Δ x * nrm B Δ y := by
  obtain ⟨e0, e1⟩ := repr_mul h0 h1 x y
  unfold nrm
  rw [e0, e1]; ring

theorem nrm_one (h0 : B 0 = 1) : nrm B Δ (1 : K) = 1 := by
  obtain ⟨e0, e1⟩ := repr_one h0
  unfold nrm
  rw [e0, e1]; ring

theorem exists_inv (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x : K)
    (hN : nrm B Δ x ≠ 0) : ∃ x', x * x' = 1 := by
  refine ⟨(nrm B Δ x)⁻¹ • (B.repr x 0 • B 0 + (-B.repr x 1) • B 1), ?_⟩
  have hc := repr_coord B (B.repr x 0) (-B.repr x 1)
  obtain ⟨e0, e1⟩ := repr_mul h0 h1 x (B.repr x 0 • B 0 + (-B.repr x 1) • B 1)
  rw [hc.1, hc.2] at e0 e1
  have hxx : x * (B.repr x 0 • B 0 + (-B.repr x 1) • B 1) = algebraMap L K (nrm B Δ x) := by
    rw [coord_eq h0 (x * (B.repr x 0 • B 0 + (-B.repr x 1) • B 1)), e0, e1]
    have : B.repr x 0 * B.repr x 0 + Δ * (B.repr x 1 * -B.repr x 1) = nrm B Δ x := by
      unfold nrm; ring
    have h' : B.repr x 0 * -B.repr x 1 + B.repr x 1 * B.repr x 0 = 0 := by ring
    rw [this, h']; simp
  rw [mul_smul_comm, hxx, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN, map_one]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)

theorem le_one_of_sq {a : Γ} (h : a ^ 2 ≤ 1) : a ≤ 1 := by
  by_contra hc
  exact absurd h (not_le.2 (one_lt_pow₀ (not_le.1 hc) two_ne_zero))

theorem inert_case (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) (hΔ : w Δ = 1) (hn : ¬ IsSquare Δ)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  have h10 : (1 : K) ≠ 0 := h0 ▸ B.ne_zero 0
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
    by_contra! hall
    apply h10
    rw [← hz]
    simp [dotProduct, hall]
  haveI : Nonempty (Fin M) := ⟨i₀⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => w (nrm B Δ (y k)))
  have hNv (x : K) : w (nrm B Δ x) = max (w (B.repr x 0)) (w (B.repr x 1)) ^ 2 :=
    val_norm w hsq hΔ hn _ _
  have hne (x : K) (hx : x ≠ 0) : nrm B Δ x ≠ 0 := by
    intro hN
    have h := hNv x
    rw [hN, map_zero] at h
    have hm := (pow_eq_zero_iff two_ne_zero).1 h.symm
    have ha : w (B.repr x 0) = 0 := le_antisymm (hm ▸ le_max_left _ _) zero_le
    have hc : w (B.repr x 1) = 0 := le_antisymm (hm ▸ le_max_right _ _) zero_le
    apply hx
    rw [coord_eq h0 x, (Valuation.zero_iff w).1 ha, (Valuation.zero_iff w).1 hc]
    simp
  have hNi : nrm B Δ (y i) ≠ 0 := by
    intro hN
    have h := hi i₀
    simp only [hN, map_zero] at h
    exact hne _ hi₀ ((Valuation.zero_iff w).1 (le_antisymm h zero_le))
  obtain ⟨x', hx'⟩ := exists_inv h0 h1 (y i) hNi
  refine ⟨⟨x', y i, by rw [mul_comm]; exact hx', hx'⟩, Pi.single i 1, ?_, ?_, ?_⟩
  · intro k l
    have hn' : w (nrm B Δ (x' * y k)) ≤ 1 := by
      have e1 : nrm B Δ x' * nrm B Δ (y i) = 1 := by
        rw [← nrm_mul h0 h1, mul_comm, hx', nrm_one h0]
      rw [nrm_mul h0 h1, map_mul]
      calc w (nrm B Δ x') * w (nrm B Δ (y k)) ≤ w (nrm B Δ x') * w (nrm B Δ (y i)) :=
            mul_le_mul' le_rfl (hi k)
        _ = 1 := by rw [← map_mul, e1, map_one]
    rw [hNv] at hn'
    have hm := le_one_of_sq hn'
    fin_cases l
    · exact (le_max_left _ _).trans hm
    · exact (le_max_right _ _).trans hm
  · intro k l
    by_cases hk : k = i
    · subst hk
      obtain ⟨e0, e1⟩ := repr_one (B := B) h0
      fin_cases l <;> simp [e0, e1]
    · simp [Pi.single_apply, hk]
  · simp only [Units.val_mk]
    simp [Pi.single_apply, mul_comm x', hx']

theorem mul_ef {e f : K} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (α β γ δ : L) :
    (α • e + β • f) * (γ • e + δ • f) = (α * γ) • e + (β * δ) • f := by
  simp only [Algebra.smul_def, map_mul]
  linear_combination (algebraMap L K α * algebraMap L K γ) * he +
    (algebraMap L K β * algebraMap L K δ) * hf +
    (algebraMap L K α * algebraMap L K δ + algebraMap L K β * algebraMap L K γ) * hef

theorem int_ef {e f : K} (he : ∀ l, w (B.repr e l) ≤ 1) (hf : ∀ l, w (B.repr f l) ≤ 1) {α β : L}
    (hα : w α ≤ 1) (hβ : w β ≤ 1) (l : Fin 2) : w (B.repr (α • e + β • f) l) ≤ 1 := by
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  refine (w.map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' hα (he l)
  · rw [map_mul]; exact mul_le_one' hβ (hf l)

variable (B) in

def idm (s : L) : K := (2⁻¹ : L) • B 0 + ((2 * s)⁻¹ : L) • B 1

variable (B) in

def ev (s : L) (x : K) : L := B.repr x 0 + s * B.repr x 1

theorem mul_idm (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (h2 : (2 : L) ≠ 0) {s : L}
    (hs0 : s ≠ 0) (hs : s * s = Δ) (x : K) : x * idm B s = ev B s x • idm B s := by
  have hd : B 1 * idm B s = algebraMap L K s * idm B s := by
    unfold idm
    rw [Algebra.smul_def, Algebra.smul_def, h0, mul_one]
    have e1 : algebraMap L K s * algebraMap L K (2 * s)⁻¹ = algebraMap L K (2⁻¹ : L) := by
      rw [← map_mul]; congr 1; field_simp
    have e2 : algebraMap L K (2 * s)⁻¹ * algebraMap L K Δ =
        algebraMap L K s * algebraMap L K (2⁻¹ : L) := by
      rw [← map_mul, ← map_mul, ← hs]; congr 1; field_simp
    linear_combination (algebraMap L K (2 * s)⁻¹) * h1 + e2 - B 1 * e1
  have hx := coord_eq h0 x
  calc x * idm B s = (algebraMap L K (B.repr x 0) + algebraMap L K (B.repr x 1) * B 1) * idm B s :=
        congrArg (· * idm B s) hx
    _ = ev B s x • idm B s := by
      unfold ev
      rw [Algebra.smul_def, map_add, map_mul]
      linear_combination (algebraMap L K (B.repr x 1)) * hd

theorem ev_idm (h2 : (2 : L) ≠ 0) {s : L} (hs0 : s ≠ 0) :
    ev B s (idm B s) = 1 ∧ ev B s (idm B (-s)) = 0 := by
  have c1 := repr_coord B (2⁻¹ : L) ((2 * s)⁻¹ : L)
  have c2 := repr_coord B (2⁻¹ : L) ((2 * -s)⁻¹ : L)
  unfold ev idm
  rw [c1.1, c1.2, c2.1, c2.2]
  constructor <;> field_simp <;> ring

theorem idm_add (h0 : B 0 = 1) (h2 : (2 : L) ≠ 0) {s : L} (hs : s ≠ 0) :
    idm B s + idm B (-s) = 1 := by
  unfold idm
  have e : ((2 * -s)⁻¹ : L) = -(2 * s)⁻¹ := by field_simp
  rw [e, neg_smul, h0, Algebra.smul_def, mul_one]
  have e2 : algebraMap L K (2⁻¹ : L) + algebraMap L K (2⁻¹ : L) = 1 := by
    rw [← map_add, ← map_one (algebraMap L K)]; congr 1; field_simp; norm_num
  linear_combination e2

theorem split_case (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (h2 : w (2 : L) = 1) (hΔ : w Δ = 1) {s : L} (hs : s * s = Δ)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  have h20 : (2 : L) ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [h2]; exact one_ne_zero)
  have hws : w s = 1 := by
    have hq : w s ^ 2 = 1 := by rw [← map_pow, sq, hs, hΔ]
    refine le_antisymm (le_one_of_sq hq.le) ?_
    by_contra hc
    exact absurd hq (pow_lt_one₀ zero_le (not_le.1 hc) two_ne_zero).ne
  have hs0 : s ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hws]; exact one_ne_zero)
  have hns : -s ≠ 0 := neg_ne_zero.2 hs0
  have hs' : -s * -s = Δ := by rw [neg_mul_neg, hs]
  set e : K := idm B s with he_def
  set f : K := idm B (-s) with hf_def
  have hef1 : e + f = 1 := idm_add h0 h20 hs0
  have me (x : K) : x * e = ev B s x • e := mul_idm h0 h1 h20 hs0 hs x
  have mf (x : K) : x * f = ev B (-s) x • f := mul_idm h0 h1 h20 hns hs' x
  have hee : e * e = e := by rw [me, (ev_idm h20 hs0).1, one_smul]
  have hff : f * f = f := by
    rw [mf]
    have := (ev_idm (B := B) h20 hns).1
    rw [this, one_smul]
  have hfe : f * e = 0 := by rw [me, (ev_idm h20 hs0).2, zero_smul]
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have hdec (x : K) : x = ev B s x • e + ev B (-s) x • f := by
    rw [← me, ← mf, ← mul_add, hef1, mul_one]
  have wi : w (2⁻¹ : L) = 1 := by rw [map_inv₀, h2, inv_one]
  have wi2 (t : L) (ht : w t = 1) : w ((2 * t)⁻¹ : L) = 1 := by
    rw [map_inv₀, map_mul, h2, ht, one_mul, inv_one]
  have hei (t : L) (ht : w t = 1) (l : Fin 2) : w (B.repr (idm B t) l) ≤ 1 := by
    have c := repr_coord B (2⁻¹ : L) ((2 * t)⁻¹ : L)
    unfold idm
    fin_cases l
    · simp only [Fin.zero_eta]; rw [c.1, wi]
    · simp only [Fin.mk_one]; rw [c.2, wi2 t ht]
  have he_int := hei s hws
  have hf_int := hei (-s) (by rw [Valuation.map_neg, hws])
  have h10 : (1 : K) ≠ 0 := h0 ▸ B.ne_zero 0
  have he0 : e ≠ 0 := fun h => by
    have := (ev_idm (B := B) h20 hs0).1
    rw [← he_def, h] at this
    simp [ev] at this
  have hf0 : f ≠ 0 := fun h => by
    have := (ev_idm (B := B) h20 hns).1
    rw [← hf_def, h] at this
    simp [ev] at this

  have hsum (g : K) (t : L) (mg : ∀ x, x * g = ev B t x • g) (hg : g ≠ 0) :
      ∃ k, ev B t (y k) ≠ 0 := by
    by_contra! hall
    apply hg
    calc g = (z ⬝ᵥ y) * g := by rw [hz, one_mul]
      _ = ∑ k, z k * (y k * g) := by simp only [dotProduct, Finset.sum_mul, mul_assoc]
      _ = 0 := by simp [mg, hall]
  obtain ⟨k₁, hk₁⟩ := hsum e s me he0
  obtain ⟨k₂, hk₂⟩ := hsum f (-s) mf hf0
  haveI : Nonempty (Fin M) := ⟨k₁⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => w (ev B s (y k)))
  obtain ⟨j, hj⟩ := Finite.exists_max (fun k => w (ev B (-s) (y k)))
  have hpi : ev B s (y i) ≠ 0 := by
    intro h
    have := hi k₁
    simp only [h, map_zero] at this
    exact hk₁ ((Valuation.zero_iff w).1 (le_antisymm this zero_le))
  have hqj : ev B (-s) (y j) ≠ 0 := by
    intro h
    have := hj k₂
    simp only [h, map_zero] at this
    exact hk₂ ((Valuation.zero_iff w).1 (le_antisymm this zero_le))
  set p : Fin M → L := fun k => ev B s (y k) with hp
  set q : Fin M → L := fun k => ev B (-s) (y k) with hq
  have hpi' : p i ≠ 0 := hpi
  have hqj' : q j ≠ 0 := hqj
  have huv : ((p i)⁻¹ • e + (q j)⁻¹ • f) * (p i • e + q j • f) = 1 := by
    rw [mul_ef hee hff hef, inv_mul_cancel₀ hpi', inv_mul_cancel₀ hqj', one_smul, one_smul, hef1]
  have huy (k : Fin M) : ((p i)⁻¹ • e + (q j)⁻¹ • f) * y k =
      ((p i)⁻¹ * p k) • e + ((q j)⁻¹ * q k) • f := by
    rw [← mul_ef hee hff hef, ← hdec (y k)]
  have hle (t₀ t : L) (h : w t ≤ w t₀) (h0 : t₀ ≠ 0) : w (t₀⁻¹ * t) ≤ 1 := by
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 h0)), mul_one]
    exact h
  refine ⟨⟨(p i)⁻¹ • e + (q j)⁻¹ • f, p i • e + q j • f, huv, by rw [mul_comm]; exact huv⟩,
    Pi.single i e + Pi.single j f, ?_, ?_, ?_⟩
  · intro k l
    simp only [Units.val_mk]
    rw [huy]
    exact int_ef w he_int hf_int (hle _ _ (hi k) hpi') (hle _ _ (hj k) hqj') l
  · intro k l
    have hz0 : ∀ l, w (B.repr (0 : K) l) ≤ 1 := fun l => by simp
    have h1' : ∀ (g : K) (m : Fin M), (∀ l, w (B.repr g l) ≤ 1) →
        w (B.repr ((Pi.single m g : Fin M → K) k) l) ≤ 1 := by
      intro g m hg
      by_cases hk : k = m
      · subst hk; simpa using hg l
      · simp [Pi.single_apply, hk]
    simp only [Pi.add_apply, map_add, Finsupp.add_apply]
    exact (w.map_add _ _).trans (max_le (h1' e i he_int) (h1' f j hf_int))
  · simp only [Units.val_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, huy]
    have a1 : e * (((p i)⁻¹ * p i) • e + ((q j)⁻¹ * q i) • f) = e := by
      rw [inv_mul_cancel₀ hpi', one_smul, mul_add, hee, mul_smul_comm, hef, smul_zero, add_zero]
    have a2 : f * (((p i)⁻¹ * p j) • e + ((q j)⁻¹ * q j) • f) = f := by
      rw [inv_mul_cancel₀ hqj', one_smul, mul_add, hff, mul_smul_comm, hfe, smul_zero, zero_add]
    rw [a1, a2, hef1]

theorem core (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) (h2 : w (2 : L) = 1) (hΔ : w Δ = 1)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  by_cases hn : IsSquare Δ
  · obtain ⟨s, hs⟩ := hn
    exact split_case w h0 h1 h2 hΔ hs.symm y z hz
  · exact inert_case w h0 h1 hsq hΔ hn y z hz

end Quad

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (b₂ : Module.Basis (Fin 2) F E) (Δ : F), Δ ≠ 0 ∧ b₂ 0 = 1 ∧
      b₂ 1 * b₂ 1 = algebraMap F E Δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv (x : E) : σ (σ x) = x := by
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra! hc
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa using h'.symm
  set δ : E := x - σ x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσ : σ δ = -δ := by rw [hδ, map_sub, hinv, neg_sub]
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσ, map_zero] at h2
    have hs2 : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hst + h2
    have hs : s = 0 :=
      (mul_eq_zero.1 ((map_eq_zero_iff _ (algebraMap F E).injective).1 hs2)).resolve_left
        two_ne_zero
    refine ⟨hs, ?_⟩
    rw [hs, map_zero, zero_add] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 ((mul_eq_zero.1 hst).resolve_right hδ0)
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.2.2.1]
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hB1 : B 1 = δ := by simp [hB]
  obtain ⟨α, β, hs⟩ : ∃ α β : F, δ * δ = algebraMap F E α + algebraMap F E β * δ := by
    have hs := (B.sum_repr (δ * δ)).symm
    rw [Fin.sum_univ_two, hB0, hB1, Algebra.smul_def, Algebra.smul_def, mul_one] at hs
    exact ⟨_, _, hs⟩
  have h2 := congrArg σ hs
  rw [map_mul, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσ] at h2
  have hc : algebraMap F E β = 0 := by
    have : (2 * δ) * algebraMap F E β = 0 := by
      linear_combination h2 - hs
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hδ0)
  rw [hc, zero_mul, add_zero] at hs
  refine ⟨B, α, ?_, hB0, by rw [hB1]; exact hs⟩
  intro h0
  rw [h0, map_zero] at hs
  exact mul_self_ne_zero.2 hδ0 hs

theorem change_basis {d d' : ℕ} (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b').repr x k ∈ v.adicCompletionIntegers F := by
  have h : ∀ j k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F (b'.repr (b j) k) ≤ 1 := fun j k => GoodInt.eventually_le_one _
  filter_upwards [Filter.eventually_all.2 fun j => Filter.eventually_all.2 (h j)] with v hv x hx k
  have key : (Algebra.TensorProduct.basis (Fv F v) b').repr x k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) b).repr x j *
        (Algebra.TensorProduct.basis (Fv F v) b').repr
          ((Algebra.TensorProduct.basis (Fv F v) b) j) k := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr x]
    simp [map_sum, Finsupp.finset_sum_apply]
  rw [key]
  refine sum_mem fun j _ => mul_mem (hx j) ?_
  have e : (Algebra.TensorProduct.basis (Fv F v) b) j = inclR (Fv F v) (b j) := by
    simp [inclR, Algebra.TensorProduct.basis_apply]
  rw [e, GoodInt.repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers,
    GoodInt.valued_algebraMap]
  exact hv j k

end Global

theorem exists_primitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ latV b v ∧ z ∈ latV b v ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hcm d b M
  obtain ⟨b₂, Δ, hΔ0, h0, h1⟩ := exists_basis hcm
  filter_upwards [change_basis b₂ b, GoodInt.eventually_eq_one Δ hΔ0,
    GoodInt.eventually_eq_one (2 : F) two_ne_zero] with v hch hΔ h2 y hy
  obtain ⟨z, hz⟩ := hy
  have hB0 : (Algebra.TensorProduct.basis (Fv F v) b₂) 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, h0]; rfl
  have hB1 : (Algebra.TensorProduct.basis (Fv F v) b₂) 1 *
      (Algebra.TensorProduct.basis (Fv F v) b₂) 1 =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) Δ) := by
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1, mul_one]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E Δ = algebraMap F (Fv F v) Δ ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have h2' : Valued.v (2 : Fv F v) = 1 := by
    have := GoodInt.valued_algebraMap v (2 : F)
    rw [map_ofNat] at this
    rw [this, h2]
  have hΔ' : Valued.v (algebraMap F (Fv F v) Δ) = 1 := by
    rw [GoodInt.valued_algebraMap, hΔ]
  have hsq : ∀ x : Fv F v, Valued.v (x - 1) < 1 → IsSquare x := fun x hx =>
    GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x (by
      rw [show (4 : Fv F v) = 2 * 2 by norm_num, map_mul, h2', one_mul]
      exact hx)
  obtain ⟨u, z', c1, c2, c3⟩ := core Valued.v hB0 hB1 hsq h2' hΔ' (y 0) z hz
  refine ⟨u, fun _ => z', ?_, ?_, ?_⟩
  · intro a i k
    obtain rfl := Subsingleton.elim a 0
    refine hch _ (fun l => ?_) k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact c1 i l
  · intro a i k
    refine hch _ (fun l => ?_) k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact c2 i l
  · simpa [dotProduct] using c3

end GlobalTheory.CompanionTheory.SW.PrimGood
