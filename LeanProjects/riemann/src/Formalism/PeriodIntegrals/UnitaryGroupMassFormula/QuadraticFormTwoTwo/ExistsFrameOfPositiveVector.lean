import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.GANormSqStar

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gb_entry {i j : Fin (2 * r + k + 1)} (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r i j = if i = j then (if j.val = r + k then -1 else 1) else 0 := by
  simp only [Hpk]
  by_cases h : i = j
  · subst h
    have h1 : ¬ (i.val < r ∧ i.val + i.val = 2 * r + k) := by omega
    rw [if_neg h1, if_neg h1, if_pos ⟨hj, hj', rfl⟩, if_pos rfl]
  · have h1 : ¬ (i.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h2 : ¬ (j.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := fun hh => h hh.2.2
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h]

theorem gb_mulVec {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    Hpk k r *ᵥ v = fun i => (if i.val = r + k then -1 else 1) * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [gb_entry hi.1 hi.2, if_pos rfl]
    · rw [hv i (by omega)]; ring
  · intro b _ hb
    by_cases hb' : r ≤ b.val ∧ b.val ≤ r + k
    · rw [gb_entry hb'.1 hb'.2, if_neg (Ne.symm hb)]; ring
    · rw [hv b (by omega)]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

theorem gb_herm {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * ((if i.val = r + k then -1 else 1) * v i) := by
  unfold herm
  rw [gb_mulVec hv]
  simp only [dotProduct, Pi.star_apply]

theorem gb_symm {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  rw [gb_herm hv, gb_herm hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_mul', star_star, star_neg, star_one] <;> ring

theorem gb_add_left (v v' w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v + v') w = herm (Hpk k r) v w + herm (Hpk k r) v' w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

theorem gb_smul_left (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • v) w = c * herm (Hpk k r) v w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem gb_sub_left (v v' w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v - v') w = herm (Hpk k r) v w - herm (Hpk k r) v' w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem gb_smul_right (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (c • w) = star c * herm (Hpk k r) v w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem gb_sub_right (v w w' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (w - w') = herm (Hpk k r) v w - herm (Hpk k r) v w' := by
  simp only [herm, star_sub, sub_dotProduct]

theorem gb_wb_smul {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : ℂ) : inWb k r (c • v) := by
  intro i hi
  simp [hv i hi]

theorem gb_wb_sub {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) : inWb k r (v - w) := by
  intro i hi
  simp [hv i hi, hw i hi]

theorem gb_sq {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hl : v (wI k r (Fin.last k)) = 0) :
    (herm (Hpk k r) v v).re = ∑ i, Complex.normSq (v i) := by
  rw [gb_herm hv, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have e : i = wI k r (Fin.last k) := Fin.ext (by simp [wI, h])
    have h0 : v i = 0 := by rw [e]; exact hl
    simp [h0]
  · simp only [one_mul, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring

theorem gb_pos {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hv : inWb k r v)
    (hvz : herm (Hpk k r) v z = 0) (hv0 : v ≠ 0) : 0 < (herm (Hpk k r) v v).re := by
  classical
  obtain ⟨t, htv⟩ : ∃ t : Fin (2 * r + k + 1), t.val = r + k := ⟨⟨r + k, by omega⟩, rfl⟩
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      herm (Hpk k r) a b = -(star (b t) * a t) + ∑ i ∈ Finset.univ.erase t, star (b i) * a i := by
    intro a b ha
    rw [gb_herm ha, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    congr 1
    · rw [if_pos htv]; ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i.val ≠ r + k := fun h => Finset.ne_of_mem_erase hi (Fin.ext (by rw [htv]; exact h))
      rw [if_neg hne]; ring
  have nsq : ∀ x : ℂ, (star x * x).re = ‖x‖ ^ 2 := by
    intro x
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hre : ∀ a : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      (herm (Hpk k r) a a).re = (∑ i ∈ Finset.univ.erase t, ‖a i‖ ^ 2) - ‖a t‖ ^ 2 := by
    intro a ha
    rw [key a a ha, Complex.add_re, Complex.neg_re, nsq, Complex.re_sum]
    simp only [nsq]
    ring
  have hzz : (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) < ‖z t‖ ^ 2 := by
    have h1 := hre z hz
    unfold Tz at hT
    linarith
  have hvz' : ∑ i ∈ Finset.univ.erase t, star (z i) * v i = star (z t) * v t := by
    have h1 := key v z hv
    rw [hvz] at h1
    linear_combination -h1
  have cs1 : ‖z t‖ * ‖v t‖ ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖ := by
    have e : ‖z t‖ * ‖v t‖ = ‖∑ i ∈ Finset.univ.erase t, star (z i) * v i‖ := by
      rw [hvz', norm_mul, norm_star]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_star]
  have cs2 : (∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS0 : 0 ≤ ‖z t‖ * ‖v t‖ := by positivity
  have hab : (‖z t‖ * ‖v t‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := by
    nlinarith [mul_le_mul cs1 cs1 hS0 (hS0.trans cs1)]
  have hNz : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hNv : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rw [hre v hv]
  by_contra hneg
  push_neg at hneg
  have hle : (∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2) ≤ ‖v t‖ ^ 2 := by linarith
  have hb : ‖v t‖ ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg hNz (sub_nonneg.2 hle), sq_nonneg ‖v t‖]
  have hvt : v t = 0 := by
    have h2 : ‖v t‖ ^ 2 = 0 := le_antisymm hb (sq_nonneg _)
    simpa using h2
  have hNv0 : ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 = 0 := by linarith
  have hvE : ∀ i ∈ Finset.univ.erase t, v i = 0 := by
    intro i hi
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hNv0 i hi
    simpa using h3
  apply hv0
  funext i
  by_cases hi : i = t
  · subst hi; simpa using hvt
  · simpa using hvE i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)

theorem gb_normalize {b v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) (hv : inWb k r v)
    (hvb : herm (Hpk k r) v b = 0) (hv0 : v ≠ 0) : ∃ s : ℂ, herm (Hpk k r) (s • v) (s • v) = 1 := by
  have hp := gb_pos hb hT hv hvb hv0
  have him : (herm (Hpk k r) v v).im = 0 := by
    have h := congrArg Complex.im (gb_symm hv hv)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  set q := (herm (Hpk k r) v v).re with hq
  have hvv : herm (Hpk k r) v v = (q : ℂ) := Complex.ext (by simp [hq]) (by simp [him])
  refine ⟨(((Real.sqrt q)⁻¹ : ℝ) : ℂ), ?_⟩
  rw [gb_smul_left, gb_smul_right, hvv]
  have hst : star (((Real.sqrt q)⁻¹ : ℝ) : ℂ) = (((Real.sqrt q)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hst]
  have hne : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hr : ((Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) : ℝ) = 1 := by
    field_simp
    linarith [Real.mul_self_sqrt hp.le, Real.sq_sqrt hp.le]
  exact_mod_cast hr

def gbL (c : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := herm (Hpk k r) v c
  map_add' v w := gb_add_left v w c
  map_smul' a v := by simp only [gb_smul_left, smul_eq_mul, RingHom.id_apply]

theorem gb_perp {m : ℕ} (hm : m + 2 < k + 1) (cs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (a b : Fin (2 * r + k + 1) → ℂ) :
    ∃ v, v ≠ 0 ∧ inWb k r v ∧ herm (Hpk k r) v a = 0 ∧ herm (Hpk k r) v b = 0 ∧
      ∀ j, herm (Hpk k r) v (cs j) = 0 := by
  classical
  obtain ⟨c, hca, hcb, hcs⟩ : ∃ c : Fin (m + 2) → Fin (2 * r + k + 1) → ℂ,
      c 0 = a ∧ c (Fin.succ 0) = b ∧ ∀ j : Fin m, c j.succ.succ = cs j :=
    ⟨Fin.cons a (Fin.cons b cs), by simp, by simp, fun j => by simp⟩
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ),
      ∀ x, emb x = Function.extend (wI k r) x 0 :=
    ⟨Function.ExtendByZero.linearMap ℂ (wI k r), fun x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (m + 2) → ℂ),
      ∀ x j, L x j = herm (Hpk k r) (emb x) (c j) :=
    ⟨(LinearMap.pi fun j => gbL (c j)) ∘ₗ emb, fun x j => rfl⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℂ (LinearMap.range L) ≤ m + 2 := by
    have h1 := Submodule.finrank_le (LinearMap.range L)
    simpa using h1
  simp only [Module.finrank_fin_fun] at hrk
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker L) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx0' : x ≠ 0 := fun h => hx0 (by subst h; rfl)
  have hL0 : ∀ j, herm (Hpk k r) (emb x) (c j) = 0 := by
    intro j
    have h1 := congrFun (LinearMap.mem_ker.1 hx) j
    rw [hL] at h1
    exact h1
  have hinj : Function.Injective (wI k r) := by
    intro p q h
    simp only [wI, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  refine ⟨emb x, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hx0'
    funext j
    have h1 := congrFun h0 (wI k r j)
    rw [hemb, hinj.extend_apply] at h1
    simpa using h1
  · intro i hi
    have hni : ¬∃ p, wI k r p = i := by
      rintro ⟨p, rfl⟩
      have := p.isLt
      simp only [wI, Fin.val_mk] at hi
      omega
    rw [hemb, Function.extend_apply' _ _ _ hni, Pi.zero_apply]
  · have h1 := hL0 0
    rwa [hca] at h1
  · have h1 := hL0 (Fin.succ 0)
    rwa [hcb] at h1
  · intro j
    have h1 := hL0 j.succ.succ
    rwa [hcs] at h1

theorem exists_frame_of_positive_vector {a b : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∀ m, m ≤ k - 1 → ∃ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_⟩
    unfold IsFrameOf
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨Bs, hB⟩ := ih (by omega)
    unfold IsFrameOf at hB
    obtain ⟨hB1, hB2, hB3⟩ := hB
    obtain ⟨v, hv0, hvw, hva, hvb, hvc⟩ := gb_perp (by omega) Bs a b
    obtain ⟨s, hs⟩ := gb_normalize hb hT hvw hvb hv0
    have hsv : inWb k r (s • v) := gb_wb_smul hvw s
    have h1 : ∀ i, herm (Hpk k r) (Bs i) (s • v) = 0 := by
      intro i
      rw [gb_smul_right, gb_symm (hB1 i) hvw, hvc i, star_zero, mul_zero]
    have h2 : ∀ i, herm (Hpk k r) (s • v) (Bs i) = 0 := by
      intro i
      rw [gb_smul_left, hvc i, mul_zero]
    refine ⟨Fin.snoc Bs (s • v), ?_⟩
    unfold IsFrameOf
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hsv
      · rw [Fin.snoc_castSucc]; exact hB1 j
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [Fin.snoc_last, if_pos rfl]; exact hs
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h2, if_neg (Fin.castSucc_lt_last j').ne']
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h1, if_neg (Fin.castSucc_lt_last i').ne]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hB2]
        by_cases h : i' = j' <;> simp [h]
    · intro i w hw
      have hw' := hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        rcases hw' with rfl | rfl
        · rw [gb_smul_left, hva, mul_zero]
        · rw [gb_smul_left, hvb, mul_zero]
      · rw [Fin.snoc_castSucc]; exact hB3 j w hw

theorem exists_frame {a b : Fin (2 * r + k + 1) → ℂ} (ha : inWb k r a) (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∃ Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := exists_frame_of_positive_vector hb hT (k - 1) le_rfl

theorem exists_unit {z a : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ha : inWb k r a)
    (hind : ∀ c : ℂ, a ≠ c • z) :
    ∃ e : Fin (2 * r + k + 1) → ℂ, inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      ∀ v, herm (Hpk k r) v a = 0 → herm (Hpk k r) v z = 0 → herm (Hpk k r) v e = 0 := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro h
    unfold Tz at hT
    rw [h] at hT
    simp at hT
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = herm (Hpk k r) a z / herm (Hpk k r) z z := ⟨_, rfl⟩
  have hwb : inWb k r (a - c • z) := gb_wb_sub ha (gb_wb_smul hz c)
  have hwz : herm (Hpk k r) (a - c • z) z = 0 := by
    rw [gb_sub_left, gb_smul_left, hc]
    simp [hzz]
  have hw0 : a - c • z ≠ 0 := by
    intro h
    exact hind c (sub_eq_zero.1 h)
  obtain ⟨s, hs⟩ := gb_normalize hz hT hwb hwz hw0
  refine ⟨s • (a - c • z), gb_wb_smul hwb s, ?_, hs, ?_⟩
  · rw [gb_smul_left, hwz, mul_zero]
  · intro v hva hvz
    rw [gb_smul_right, gb_sub_right, gb_smul_right, hva, hvz]
    ring

theorem geom_package {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    ∃ (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (e' e : Fin (2 * r + k + 1) → ℂ),
      IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs ∧
      inWb k r e' ∧ herm (Hpk k r) e' z' = 0 ∧ herm (Hpk k r) e' e' = 1 ∧ IsFrameOf k r [z', e'] Bs ∧
      inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      IsFrameOf k r [z, e] (fun a => g *ᵥ Bs a) := by
  have hgi := glev_inWb hg hz
  have hgi' := glev_inWb hg hz'
  obtain ⟨hnp1, hnp2⟩ := not_prop_of_GG hz hz' hg hGG
  obtain ⟨_, hu2⟩ := glev_unit hg
  obtain ⟨Bs, hB⟩ := exists_frame hgi.2 hz' hT'
  obtain ⟨e', he'w, he'z, he'e, he'v⟩ := exists_unit hz' hT' hgi.2 hnp1
  obtain ⟨e, hew, hez, hee, hev⟩ := exists_unit hz hT hgi'.1 hnp2
  have hB' := hB
  unfold IsFrameOf at hB'
  obtain ⟨hB1, hB2, hB3⟩ := hB'
  have hBa : ∀ a, herm (Hpk k r) (Bs a) (g⁻¹ *ᵥ z) = 0 := fun a => hB3 a _ (by simp)
  have hBb : ∀ a, herm (Hpk k r) (Bs a) z' = 0 := fun a => hB3 a _ (by simp)
  have hgz : g *ᵥ (g⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hgB : ∀ a, herm (Hpk k r) (g *ᵥ Bs a) z = 0 := by
    intro a
    have h1 := glev_herm hg (Bs a) (g⁻¹ *ᵥ z)
    rw [hgz] at h1
    rw [h1]
    exact hBa a
  refine ⟨Bs, e', e, hB, he'w, he'z, he'e, ?_, hew, hez, hee, ?_⟩
  · unfold IsFrameOf
    refine ⟨hB1, hB2, ?_⟩
    intro a v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h
    · rw [h]; exact hBb a
    · rw [h]; exact he'v (Bs a) (hBa a) (hBb a)
  · unfold IsFrameOf
    refine ⟨fun a => (glev_inWb hg (hB1 a)).1, fun a b => ?_, ?_⟩
    · show herm (Hpk k r) (g *ᵥ Bs a) (g *ᵥ Bs b) = if a = b then 1 else 0
      rw [glev_herm hg]
      exact hB2 a b
    · intro a v hv
      show herm (Hpk k r) (g *ᵥ Bs a) v = 0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with h | h
      · rw [h]; exact hgB a
      · rw [h]
        apply hev
        · rw [glev_herm hg]; exact hBb a
        · exact hgB a

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
