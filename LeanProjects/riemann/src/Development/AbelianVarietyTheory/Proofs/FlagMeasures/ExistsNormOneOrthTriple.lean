import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OrthCompl

section Ring

variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]

theorem exists_gram_unit (S : Subring E) (σ : E →+* E) (φ : o →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hN : ∀ x ∈ S, ∃ c, x * σ x = φ c)
    (hτ : ∃ τ ∈ S, τ + σ τ = 1) {y0 y1 y2 c0 c1 c2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) (hc0 : c0 ∈ S) (hc1 : c1 ∈ S) (hc2 : c2 ∈ S)
    (h : y0 * σ c0 + y1 * σ c1 + y2 * σ c2 = 1) :
    ∃ d0 ∈ S, ∃ d1 ∈ S, ∃ d2 ∈ S, ∃ w : o, IsUnit w ∧
      (y0 * σ y0 + y1 * σ y1 + y2 * σ y2) * (d0 * σ d0 + d1 * σ d1 + d2 * σ d2)
        - (y0 * σ d0 + y1 * σ d1 + y2 * σ d2) * (d0 * σ y0 + d1 * σ y1 + d2 * σ y2) = φ w := by
  obtain ⟨n0, hn0⟩ := hN y0 hy0
  obtain ⟨n1, hn1⟩ := hN y1 hy1
  obtain ⟨n2, hn2⟩ := hN y2 hy2
  have hu : ∀ a b : o, ¬ IsUnit a → IsUnit b → IsUnit (a - b) := fun a b ha hb => by
    by_contra hab
    have h1 : a ∈ IsLocalRing.maximalIdeal o := ha
    have h2 : a - b ∈ IsLocalRing.maximalIdeal o := hab
    have h3 := Ideal.sub_mem _ h1 h2
    rw [sub_sub_cancel] at h3
    exact h3 hb
  by_cases ha : IsUnit (n0 + n1 + n2)
  · by_cases h0 : IsUnit (n1 + n2)
    · refine ⟨1, S.one_mem, 0, S.zero_mem, 0, S.zero_mem, n1 + n2, h0, ?_⟩
      simp only [map_one, map_zero, map_add, ← hn1, ← hn2]
      ring
    by_cases h1 : IsUnit (n0 + n2)
    · refine ⟨0, S.zero_mem, 1, S.one_mem, 0, S.zero_mem, n0 + n2, h1, ?_⟩
      simp only [map_one, map_zero, map_add, ← hn0, ← hn2]
      ring
    have u0 : IsUnit n0 := by
      have := (hu _ _ h0 ha).neg
      rwa [show -(n1 + n2 - (n0 + n1 + n2)) = n0 by ring] at this
    have u1 : IsUnit n1 := by
      have := (hu _ _ h1 ha).neg
      rwa [show -(n0 + n2 - (n0 + n1 + n2)) = n1 by ring] at this
    obtain ⟨τ, hτS, hτ⟩ := hτ
    obtain ⟨t, ht⟩ := hN τ hτS
    refine ⟨1, S.one_mem, τ * σ y0 * y1, S.mul_mem (S.mul_mem hτS (hσS _ hy0)) hy1, 0, S.zero_mem,
      ((n1 + n2) + (n0 + n2) * (t * n0 * n1)) - n0 * n1, hu _ _ ?_ (u0.mul u1), ?_⟩
    · have g0 : n1 + n2 ∈ IsLocalRing.maximalIdeal o := h0
      have g1 : n0 + n2 ∈ IsLocalRing.maximalIdeal o := h1
      exact Ideal.add_mem _ g0 (Ideal.mul_mem_right _ _ g1)
    · simp only [map_one, map_zero, map_add, map_sub, map_mul, hσ, ← hn0, ← hn1, ← hn2, ← ht]
      linear_combination (-(y0 * σ y0 * (y1 * σ y1))) * hτ
  · obtain ⟨m0, hm0⟩ := hN c0 hc0
    obtain ⟨m1, hm1⟩ := hN c1 hc1
    obtain ⟨m2, hm2⟩ := hN c2 hc2
    have h' := congrArg σ h
    simp only [map_add, map_mul, hσ, map_one] at h'
    refine ⟨c0, hc0, c1, hc1, c2, hc2, (n0 + n1 + n2) * (m0 + m1 + m2) - 1,
      hu _ _ (fun hh => ha (isUnit_of_mul_isUnit_left hh)) isUnit_one, ?_⟩
    simp only [map_one, map_add, map_sub, map_mul, ← hn0, ← hn1, ← hn2, ← hm0, ← hm1, ← hm2]
    rw [h]
    linear_combination -h'

theorem exists_norm_one_orth (S : Subring E) (σ : E →+* E) (φ : o →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hN : ∀ x ∈ S, ∃ c, x * σ x = φ c)
    (hτ : ∃ τ ∈ S, τ + σ τ = 1) (hU : ∀ u : oˣ, ∃ x ∈ S, x * σ x = φ u)
    {y0 y1 y2 c0 c1 c2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) (hc0 : c0 ∈ S) (hc1 : c1 ∈ S) (hc2 : c2 ∈ S)
    (h : y0 * σ c0 + y1 * σ c1 + y2 * σ c2 = 1) :
    ∃ u0 ∈ S, ∃ u1 ∈ S, ∃ u2 ∈ S, u0 * σ u0 + u1 * σ u1 + u2 * σ u2 = 1 ∧
      u0 * σ y0 + u1 * σ y1 + u2 * σ y2 = 0 := by
  obtain ⟨d0, hd0, d1, hd1, d2, hd2, w, hw, hd⟩ :=
    exists_gram_unit S σ φ hσ hσS hN hτ hy0 hy1 hy2 hc0 hc1 hc2 h
  obtain ⟨x, hx, hxx⟩ := hU hw.unit⁻¹
  have hw1 : φ w * φ (hw.unit⁻¹ : oˣ) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  refine ⟨x * σ (y1 * d2 - y2 * d1), ?_, x * σ (y2 * d0 - y0 * d2), ?_,
    x * σ (y0 * d1 - y1 * d0), ?_, ?_, ?_⟩
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy1 hd2) (S.mul_mem hy2 hd1)))
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy2 hd0) (S.mul_mem hy0 hd2)))
  · exact S.mul_mem hx (hσS _ (S.sub_mem (S.mul_mem hy0 hd1) (S.mul_mem hy1 hd0)))
  · simp only [map_mul, map_sub, hσ]
    rw [← hd, ← hxx] at hw1
    linear_combination hw1
  · simp only [map_mul, map_sub]
    ring

omit [IsLocalRing o] in

theorem exists_primitive [IsArtinianRing E] [IsReduced E] (S : Subring E) [IsPrincipalIdealRing S]
    (hid : ∀ e : E, e * e = e → e ∈ S) {y0 y1 y2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) :
    ∃ d : E, ∃ b0 ∈ S, ∃ b1 ∈ S, ∃ b2 ∈ S, ∃ r0 ∈ S, ∃ r1 ∈ S, ∃ r2 ∈ S,
      y0 = d * b0 ∧ y1 = d * b1 ∧ y2 = d * b2 ∧ b0 * r0 + b1 * r1 + b2 * r2 = 1 := by
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span {(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩})).principal
  have hm : ∀ z ∈ ({(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩} : Set S), ∃ b : S, b * d = z :=
    fun z hz => by
      have := Ideal.subset_span hz
      rw [hd] at this
      exact Ideal.mem_span_singleton'.1 this
  obtain ⟨b0, hb0⟩ := hm ⟨y0, hy0⟩ (by simp)
  obtain ⟨b1, hb1⟩ := hm ⟨y1, hy1⟩ (by simp)
  obtain ⟨b2, hb2⟩ := hm ⟨y2, hy2⟩ (by simp)
  have hdm : d ∈ Ideal.span {(⟨y0, hy0⟩ : S), ⟨y1, hy1⟩, ⟨y2, hy2⟩} := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨r0, z, hz, hz'⟩ := Ideal.mem_span_insert.1 hdm
  obtain ⟨r1, r2, rfl⟩ := Ideal.mem_span_pair.1 hz
  have e0 : (b0 : E) * d = y0 := congrArg Subtype.val hb0
  have e1 : (b1 : E) * d = y1 := congrArg Subtype.val hb1
  have e2 : (b2 : E) * d = y2 := congrArg Subtype.val hb2
  have e3 : (d : E) = r0 * y0 + (r1 * y1 + r2 * y2) := congrArg Subtype.val hz'
  have : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {(d : E)})
  have hee : e * e = e := he
  obtain ⟨p, hp⟩ : ∃ p, p * (d : E) = e :=
    Ideal.mem_span_singleton'.1 (hI ▸ Ideal.mem_span_singleton_self e)
  obtain ⟨q, hq⟩ : ∃ q, q * e = (d : E) :=
    Ideal.mem_span_singleton'.1 (hI ▸ Ideal.mem_span_singleton_self (d : E))
  have hde : (d : E) * e = d := by rw [← hq, mul_assoc, hee]
  have heS := hid e hee
  have h1e := S.sub_mem S.one_mem heS
  refine ⟨d, e * b0 + (1 - e), S.add_mem (S.mul_mem heS b0.2) h1e, e * b1, S.mul_mem heS b1.2,
    e * b2, S.mul_mem heS b2.2, e * r0 + (1 - e), S.add_mem (S.mul_mem heS r0.2) h1e,
    r1, r1.2, r2, r2.2, ?_, ?_, ?_, ?_⟩
  · linear_combination -e0 - (b0 - 1 : E) * hde
  · linear_combination -e1 - (b1 : E) * hde
  · linear_combination -e2 - (b2 : E) * hde
  · have k : e * (b0 * r0 + b1 * r1 + b2 * r2) = e := by
      rw [← hp]
      linear_combination p * r0 * e0 + p * r1 * e1 + p * r2 * e2 - p * e3
    linear_combination k + ((b0 : E) * r0 - b0 - r0 + 1) * hee

end Ring

section Space

open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def IsON (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {k : ℕ} (e : Fin k → Fin n → E) :
    Prop :=
  ∀ i j, hf L Hm (e i) (e j) = if i = j then 1 else 0

def orthTo (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    Submodule L.O (Fin n → E) where
  carrier := {x | hf L Hm x v = 0}
  zero_mem' := by simp [hf]
  add_mem' := by
    intro a b ha hb
    show hf L Hm (a + b) v = 0
    rw [hf_add_l, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    show hf L Hm ((c : E) • a) v = 0
    rw [hf_smul_l, ha, mul_zero]

variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem hf_eq_zero_symm (h : IsHerm L Hm) {x v : Fin n → E} (hx : hf L Hm x v = 0) :
    hf L Hm v x = 0 := by
  rw [← hf_cj L h, hx, map_zero]

theorem isON_cons (h : IsHerm L Hm) {k : ℕ} {v : Fin n → E} {e : Fin k → Fin n → E}
    (hv : hf L Hm v v = 1) (hev : ∀ i, hf L Hm (e i) v = 0) (he : IsON L Hm e) :
    IsON L Hm (Fin.cons v e : Fin (k + 1) → Fin n → E) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hv
  · simpa [(Fin.succ_ne_zero j).symm] using hf_eq_zero_symm L h (hev j)
  · simpa using hev i
  · simpa using he i j

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem exists_norm_one_orth_triple (y0 y1 y2 : E) :
    ∃ u0 ∈ L.O, ∃ u1 ∈ L.O, ∃ u2 ∈ L.O, u0 * L.cj u0 + u1 * L.cj u1 + u2 * L.cj u2 = 1 ∧
      u0 * y0 + u1 * y1 + u2 * y2 = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨h1, -, -, h4, -, -, -, h8⟩ := order_facts L ϖ hϖ
  have := L.reduced
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hden : ∀ x : E, ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E a * x ∈ L.O := fun x => by
    obtain ⟨a, ha, hi⟩ := ((IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    refine ⟨a, ha, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def] at hi
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  obtain ⟨a0, ha0, hy0⟩ := hden y0
  obtain ⟨a1, ha1, hy1⟩ := hden y1
  obtain ⟨a2, ha2, hy2⟩ := hden y2
  have hid : ∀ e : E, e * e = e → e ∈ L.O := fun e he => by
    rw [L.O_def]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, by monicity!, ?_⟩
    simp [sq, he]
  obtain ⟨d, b0, hb0, b1, hb1, b2, hb2, r0, hr0, r1, hr1, r2, hr2, e0, e1, e2, e3⟩ :=
    exists_primitive L.O hid (L.O.mul_mem (L.O.mul_mem (hint a1) (hint a2)) hy0)
      (L.O.mul_mem (L.O.mul_mem (hint a0) (hint a2)) hy1)
      (L.O.mul_mem (L.O.mul_mem (hint a0) (hint a1)) hy2)
  obtain ⟨u0, hu0, u1, hu1, u2, hu2, k1, k2⟩ := exists_norm_one_orth L.O (L.cj : E →+* E)
    (algebraMap 𝒪[F] E) L.cj_cj (fun x hx => cj_mem L hx) (fun x hx => exists_norm L hx)
    (by simpa using h1 1) h8 (cj_mem L hb0) (cj_mem L hb1) (cj_mem L hb2) hr0 hr1 hr2
    (by simpa using congrArg L.cj e3)
  refine ⟨u0, hu0, u1, hu1, u2, hu2, k1, ?_⟩
  simp only [RingHom.coe_coe, L.cj_cj] at k2
  have hne : (a0 : F) * a1 * a2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa using ha0) (by simpa using ha1)) (by simpa using ha2)
  refine ((IsUnit.mk0 _ hne).map (algebraMap F E)).mul_right_eq_zero.1 ?_
  simp only [map_mul]
  linear_combination u0 * e0 + u1 * e1 + u2 * e2 + d * k2

theorem exists_triple (h : IsHerm L Hm) (M : Submodule L.O (Fin n → E)) {e0 e1 e2 : Fin n → E}
    (m0 : e0 ∈ M) (m1 : e1 ∈ M) (m2 : e2 ∈ M)
    (h00 : hf L Hm e0 e0 = 1) (h11 : hf L Hm e1 e1 = 1) (h22 : hf L Hm e2 e2 = 1)
    (h01 : hf L Hm e0 e1 = 0) (h02 : hf L Hm e0 e2 = 0) (h12 : hf L Hm e1 e2 = 0)
    (y : Fin n → E) :
    ∃ u ∈ M, ∃ t ∈ M, ∃ s ∈ M, hf L Hm u u = 1 ∧ hf L Hm t t = 1 ∧ hf L Hm s s = 1 ∧
      hf L Hm t u = 0 ∧ hf L Hm s u = 0 ∧ hf L Hm s t = 0 ∧ hf L Hm u y = 0 := by
  have h10 := hf_eq_zero_symm L h h01
  have h20 := hf_eq_zero_symm L h h02
  have h21 := hf_eq_zero_symm L h h12
  have hM : ∀ a ∈ L.O, ∀ b ∈ L.O, ∀ c ∈ L.O, a • e0 + b • e1 + c • e2 ∈ M :=
    fun a ha b hb c hc => M.add_mem (M.add_mem (M.smul_mem ⟨a, ha⟩ m0) (M.smul_mem ⟨b, hb⟩ m1))
      (M.smul_mem ⟨c, hc⟩ m2)
  have hB : ∀ a b c a' b' c' : E, hf L Hm (a • e0 + b • e1 + c • e2) (a' • e0 + b' • e1 + c' • e2)
      = a * L.cj a' + b * L.cj b' + c * L.cj c' := fun a b c a' b' c' => by
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, h00, h11, h22, h01, h02, h12, h10, h20,
      h21]
    ring
  obtain ⟨u0, hu0, u1, hu1, u2, hu2, k1, k2⟩ :=
    exists_norm_one_orth_triple L (hf L Hm e0 y) (hf L Hm e1 y) (hf L Hm e2 y)
  obtain ⟨t0, ht0, t1, ht1, t2, ht2, l1, l2⟩ :=
    exists_norm_one_orth_triple L (L.cj u0) (L.cj u1) (L.cj u2)
  have l3 := congrArg L.cj l2
  simp only [map_add, map_mul, map_zero, L.cj_cj] at l3
  refine ⟨_, hM u0 hu0 u1 hu1 u2 hu2, _, hM t0 ht0 t1 ht1 t2 ht2, _,
    hM (L.cj (u1 * t2 - u2 * t1)) (cj_mem L ?_) (L.cj (u2 * t0 - u0 * t2)) (cj_mem L ?_)
      (L.cj (u0 * t1 - u1 * t0)) (cj_mem L ?_), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact L.O.sub_mem (L.O.mul_mem hu1 ht2) (L.O.mul_mem hu2 ht1)
  · exact L.O.sub_mem (L.O.mul_mem hu2 ht0) (L.O.mul_mem hu0 ht2)
  · exact L.O.sub_mem (L.O.mul_mem hu0 ht1) (L.O.mul_mem hu1 ht0)
  · rw [hB, k1]
  · rw [hB, l1]
  · rw [hB]
    simp only [map_sub, map_mul, L.cj_cj]
    linear_combination (t0 * L.cj t0 + t1 * L.cj t1 + t2 * L.cj t2) * k1 + l1
      - (L.cj t0 * u0 + L.cj t1 * u1 + L.cj t2 * u2) * l2
  · rw [hB, l2]
  · rw [hB]
    simp only [map_sub, map_mul]
    ring
  · rw [hB]
    simp only [map_sub, map_mul]
    ring
  · simp only [hf_add_l, hf_smul_l]
    exact k2

theorem exists_isON_orth (h : IsHerm L Hm) (y : Fin n → E) (k : ℕ) :
    ∀ (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2) → Fin n → E), (∀ i, e i ∈ M) →
      IsON L Hm e → ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ⊓ orthTo L Hm y) ∧ IsON L Hm u := by
  induction k with
  | zero => exact fun M e _ _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro M e hM he
    let f : Fin k → Fin n → E := fun i => e i.succ.succ.succ
    have hf' : IsON L Hm f := fun i j => by simpa [f] using he i.succ.succ.succ j.succ.succ.succ
    have hne : ∀ i j, i ≠ j → hf L Hm (e i) (e j) = 0 := fun i j hij => by
      rw [he, if_neg hij]
    have heq : ∀ i, hf L Hm (e i) (e i) = 1 := fun i => by rw [he, if_pos rfl]
    have hmem : ∀ i : Fin (k + 1 + 2), (∀ j : Fin k, i ≠ j.succ.succ.succ) →
        e i ∈ M ⊓ ⨅ j, orthTo L Hm (f j) := fun i hi =>
      ⟨hM i, (Submodule.mem_iInf _).2 fun j => hne _ _ (hi j)⟩
    obtain ⟨u, hu, t, ht, s, hs, uu, tt, ss, tu, su, st, uy⟩ := exists_triple L h
      (M ⊓ ⨅ j, orthTo L Hm (f j)) (e0 := e 0) (e1 := e (Fin.succ 0))
      (e2 := e (Fin.succ (Fin.succ 0)))
      (hmem _ fun j => (Fin.succ_ne_zero _).symm)
      (hmem _ fun j hj => (Fin.succ_ne_zero _).symm (Fin.succ_injective _ hj))
      (hmem _ fun j hj => (Fin.succ_ne_zero _).symm
        (Fin.succ_injective _ (Fin.succ_injective _ hj)))
      (heq _) (heq _) (heq _) (hne _ _ (Fin.succ_ne_zero _).symm)
      (hne _ _ (Fin.succ_ne_zero _).symm)
      (hne _ _ fun hj => (Fin.succ_ne_zero _).symm (Fin.succ_injective _ hj)) y
    have hfo : ∀ {v}, v ∈ M ⊓ ⨅ j, orthTo L Hm (f j) → ∀ j, hf L Hm (f j) v = 0 :=
      fun hv j => hf_eq_zero_symm L h ((Submodule.mem_iInf _).1 hv.2 j)
    obtain ⟨w, hw, hw'⟩ := ih (M ⊓ orthTo L Hm u)
      (Fin.cons t (Fin.cons s f : Fin (k + 1) → Fin n → E))
      (Fin.cases ⟨ht.1, tu⟩ (Fin.cases ⟨hs.1, su⟩ fun j => ⟨hM _, hfo hu j⟩))
      (isON_cons L h tt (Fin.cases st (hfo ht)) (isON_cons L h ss (hfo hs) hf'))
    exact ⟨Fin.cons u w, Fin.cases ⟨hu.1, uy⟩ fun j => ⟨(hw j).1.1, (hw j).2⟩,
      isON_cons L h uu (fun j => (hw j).1.2) hw'⟩

theorem exists_isON_orth_family (h : IsHerm L Hm) (k m : ℕ) :
    ∀ (y : Fin m → Fin n → E) (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2 * m) → Fin n → E),
      (∀ i, e i ∈ M) → IsON L Hm e →
      ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ∧ ∀ j, hf L Hm (u i) (y j) = 0) ∧ IsON L Hm u := by
  induction m with
  | zero => exact fun y M e hM he => ⟨e, fun i => ⟨hM i, fun j => j.elim0⟩, he⟩
  | succ m ih =>
    intro y M e hM he
    obtain ⟨v, hv, hv'⟩ := exists_isON_orth L h (y 0) (k + 2 * m) M e hM he
    obtain ⟨u, hu, hu'⟩ := ih (fun j => y j.succ) _ v hv hv'
    exact ⟨u, fun i => ⟨(hu i).1.1, Fin.cases (hu i).1.2 (hu i).2⟩, hu'⟩

end Space

theorem exists_orthonormal_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∃ u : Fin (n - 2 * m) → Fin n → E, (∀ i, u i ∈ Λ ∧ u i ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∀ i j, hf L Hm (u i) (u j) = if i = j then 1 else 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH Λ hΛ m y _
  by_cases hn : 2 * m ≤ n
  · obtain ⟨b, hb, hΛb⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
    have hk : n - 2 * m + 2 * m = n := Nat.sub_add_cancel hn
    obtain ⟨u, hu, hu'⟩ := exists_isON_orth_family L hH.1 (n - 2 * m) m y Λ
      (fun i => b (Fin.cast hk i)) (fun i => hΛb ▸ Submodule.subset_span ⟨_, rfl⟩)
      (fun i j => by simpa using hb (Fin.cast hk i) (Fin.cast hk j))
    refine ⟨u, fun i => ⟨(hu i).1, fun z hz => ?_⟩, hu'⟩
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact (hu i).2 j
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [Eichler.hf_add_r, ha, hb, add_zero]
    | smul c a _ ha => rw [Eichler.hf_smul_r, ha, mul_zero]
  · have h0 : ∀ i : Fin (n - 2 * m), False := fun i => by have := i.2; omega
    exact ⟨fun _ => 0, fun i => (h0 i).elim, fun i => (h0 i).elim⟩

end GlobalTheory.HL.OrthCompl
