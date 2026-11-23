import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.CompSymmComp

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Reps

open Classical

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem cq_rep_int (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) :
    ∀ (D : ℕ) (y : E), IntAt P y → ∃ i : ℕ, i < q ^ D ∧ IntAt P ((y - i) / (q : E) ^ D)
  | 0, y, hy => ⟨0, by simp, by simpa using hy⟩
  | D + 1, y, hy => by
    have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
    obtain ⟨i, hi, hz⟩ := cq_rep_int hq hu hp hcard D y hy
    obtain ⟨d, hd, hdr⟩ := ocbS_natCast_surj hq hp hcard (redP P ((y - i) / (q : E) ^ D))
    have hzd : IntAt P (((y - i) / (q : E) ^ D - d) / q) := by
      refine ciIntAt_div hq hu (ciIntAt_sub hz (ocbS_intAt_natCast d)) ?_
      rw [redP_sub hz (ocbS_intAt_natCast d), redP_natCast₂, hdr, sub_self]
    refine ⟨i + q ^ D * d, ?_, ?_⟩
    · have h1 : q ^ D * d ≤ q ^ D * (q - 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : q ^ D * (q - 1) + q ^ D = q ^ (D + 1) := by
        rw [pow_succ, Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hp.pos)]
      omega
    · have e : (y - ((i + q ^ D * d : ℕ) : E)) / (q : E) ^ (D + 1) = ((y - i) / (q : E) ^ D - d) / q := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd

theorem cq_rep (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) (A B : ℕ) (x : E) (hx : IntAt P ((q : E) ^ A * x)) :
    ∃ v ∈ LocE.valsQ E q A B, IntAt P ((x - v) / (q : E) ^ B) := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨i, hi, hz⟩ := cq_rep_int hq hu hp hcard (A + B) _ hx
  refine ⟨(i : E) / (q : E) ^ A, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩, ?_⟩
  have e : (x - (i : E) / (q : E) ^ A) / (q : E) ^ B = ((q : E) ^ A * x - i) / (q : E) ^ (A + B) := by
    rw [pow_add]
    field_simp
  rw [e]
  exact hz

theorem cq_rep_unique (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    {A B : ℕ} {v v' : E} (hv : v ∈ LocE.valsQ E q A B) (hv' : v' ∈ LocE.valsQ E q A B) (h : IntAt P ((v - v') / (q : E) ^ B)) :
    v = v' := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 hv'
  rw [Finset.mem_range] at hi hi'
  have key : ∀ j j' : ℕ, j < q ^ (A + B) → j' < q ^ (A + B) → j' ≤ j →
      IntAt P (((j : E) / (q : E) ^ A - (j' : E) / (q : E) ^ A) / (q : E) ^ B) → j = j' := by
    intro j j' hj hj' hle hI
    have e : ((j : E) / (q : E) ^ A - (j' : E) / (q : E) ^ A) / (q : E) ^ B = ((j - j' : ℕ) : E) / (q : E) ^ (A + B) := by
      rw [Nat.cast_sub hle, pow_add]
      field_simp
    rw [e, ocbS_intAt_div_pow hq hu hp] at hI
    have := Nat.eq_zero_of_dvd_of_lt hI (by omega)
    omega
  rcases le_total i' i with hle | hle
  · rw [key i i' hi hi' hle h]
  · have h' : IntAt P (((i' : E) / (q : E) ^ A - (i : E) / (q : E) ^ A) / (q : E) ^ B) := by
      have e : ((i' : E) / (q : E) ^ A - (i : E) / (q : E) ^ A) / (q : E) ^ B =
          -(((i : E) / (q : E) ^ A - (i' : E) / (q : E) ^ A) / (q : E) ^ B) := by ring
      rw [e]
      exact ciIntAt_neg h
    rw [key i' i hi' hi hle h']

theorem cq_vals_int {A B : ℕ} {v : E} (hv : v ∈ LocE.valsQ E q A B) (hq0 : (q : E) ≠ 0) : IntAt P ((q : E) ^ A * v) := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hq0)]
  exact ocbS_intAt_natCast i

end Reps

section Perm

theorem cq_sum_perm {α M : Type} [DecidableEq α] [AddCommMonoid M] (V W : Finset α) (hWV : W ⊆ V) (T σ : α → α) (F : α → M)
    (h1 : ∀ t ∈ V, F (T t) ≠ 0 → t ∈ W) (h2 : ∀ u ∈ V, F u ≠ 0 → u ∈ W) (h3 : ∀ t ∈ W, σ t ∈ W) (h4 : Set.InjOn σ W)
    (h5 : ∀ t ∈ W, F (σ t) = F (T t)) : ∑ t ∈ V, F (T t) = ∑ u ∈ V, F u := by
  classical
  rw [← Finset.sum_subset hWV (fun t ht htW => by by_contra h; exact htW (h1 t ht h)),
    ← Finset.sum_subset hWV (fun u hu huW => by by_contra h; exact huW (h2 u hu h))]
  rw [← Finset.sum_congr rfl h5]
  have himg : W.image σ = W := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact h3 t ht
    · rw [Finset.card_image_of_injOn h4]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun x hx y hy hxy => h4 hx hy hxy)]

end Perm

section R1

variable {k : Type} [CommRing k] {n c : ℕ}

theorem cq_inX_apply (x : Fin n → k) (l : Fin (n + c)) : Loc.inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  by_cases h : l.1 < n <;> simp [LinearMap.pi_apply, h]

theorem reduction_column_standard_basis {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : Loc.R1cond k n c r) {i : ℕ} (l : Fin (n + c))
    (hl : n + i ≤ l.1) : r (Loc.eN k (n + c) (n + i)) l = if l.1 = n + i then 1 else 0 := by
  have h := hr.2.2 i l (show ¬ (l.1 < n + i) by omega)
  rw [Pi.sub_apply, sub_eq_zero] at h
  rw [h]
  rfl

theorem cq_decomp (z : Fin (n + c) → k) :
    z = Loc.inX k n c (fun j => z (Fin.castAdd c j)) + ∑ i : Fin c, z (Fin.natAdd n i) • Loc.eN k (n + c) (n + i.1) := by
  funext l
  rw [Pi.add_apply, Finset.sum_apply, cq_inX_apply]
  by_cases hl : l.1 < n
  · rw [dif_pos hl, Finset.sum_eq_zero (fun i _ => by
      rw [Pi.smul_apply, smul_eq_mul]
      show z (Fin.natAdd n i) * (if l.1 = n + i.1 then 1 else 0) = 0
      rw [if_neg (by omega), mul_zero]), add_zero]
    rfl
  · rw [dif_neg hl, zero_add]
    obtain ⟨j, rfl⟩ : ∃ j : Fin c, l = Fin.natAdd n j := ⟨⟨l.1 - n, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [Finset.sum_eq_single j]
    · rw [Pi.smul_apply, smul_eq_mul]
      show z (Fin.natAdd n j) = z (Fin.natAdd n j) * (if (Fin.natAdd n j).1 = n + j.1 then 1 else 0)
      rw [if_pos (by simp), mul_one]
    · intro i _ hij
      rw [Pi.smul_apply, smul_eq_mul]
      show z (Fin.natAdd n i) * (if (Fin.natAdd n j).1 = n + i.1 then 1 else 0) = 0
      rw [if_neg (fun h => hij (Fin.ext (by simp at h; omega))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem cq_r_apply {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (z : Fin (n + c) → k) :
    r z = Loc.inX k n c (g (fun j => z (Fin.castAdd c j))) + ∑ i : Fin c, z (Fin.natAdd n i) • r (Loc.eN k (n + c) (n + i.1)) := by
  conv_lhs => rw [cq_decomp z]
  rw [map_add, hg, map_sum]
  simp only [map_smul]

theorem reduction_entry_lower_block {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hr : Loc.R1cond k n c r) (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (z : Fin (n + c) → k) (v : Fin c) :
    r z (Fin.natAdd n v) = z (Fin.natAdd n v) +
      ∑ i : Fin c, if v.1 < i.1 then z (Fin.natAdd n i) * r (Loc.eN k (n + c) (n + i.1)) (Fin.natAdd n v) else 0 := by
  rw [cq_r_apply hg z, Pi.add_apply, cq_inX_apply, dif_neg (by simp), zero_add, Finset.sum_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_neg (lt_irrefl _),
    zero_add]
  congr 1
  · rw [Pi.smul_apply, smul_eq_mul, reduction_column_standard_basis hr _ (by simp), if_pos (by simp), mul_one]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hvi : v.1 < i.1
    · rw [if_pos hvi]
    · rw [if_neg hvi, reduction_column_standard_basis hr _ (by simp; omega), if_neg (fun h => by
        have := Finset.ne_of_mem_erase hi
        apply this
        exact Fin.ext (by simp at h; omega)), mul_zero]

theorem cq_r_XRow {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (z : Fin (n + c) → k) (l : Fin n) :
    r z (Fin.castAdd c l) = g (fun j => z (Fin.castAdd c j)) l +
      ∑ i : Fin c, z (Fin.natAdd n i) * r (Loc.eN k (n + c) (n + i.1)) (Fin.castAdd c l) := by
  rw [cq_r_apply hg z, Pi.add_apply, cq_inX_apply, dif_pos (by simp), Finset.sum_apply]
  congr 1

end R1

section Tgt

open Classical

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem cq_bd_mono {m m' : ℕ} {x : E} (hx : IntAt P ((q : E) ^ m * x)) (h : m ≤ m') : IntAt P ((q : E) ^ m' * x) := by
  have e : (q : E) ^ m' * x = (q : E) ^ (m' - m) * ((q : E) ^ m * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  rw [e]
  have hp : IntAt P ((q : E) ^ (m' - m)) := by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ (m' - m))
    rwa [map_pow, map_natCast] at h
  exact hp.mul hx

theorem free_point_column_entry {n' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' (c + 1) n c → E) (l : Fin (n + c))
    (s : Fin (n' + (c + 1))) : Loc.xx1 y t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else PI.UnfoldEquiv.UnitaryGroupMassFormula.base y l s :=
  PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_single y t l s

end Tgt

section TgtMain

open Classical

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem cq_bd_mul {m1 m2 : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m1 * x)) (hy : IntAt P ((q : E) ^ m2 * y)) :
    IntAt P ((q : E) ^ (m1 + m2) * (x * y)) := by
  have e : (q : E) ^ (m1 + m2) * (x * y) = ((q : E) ^ m1 * x) * ((q : E) ^ m2 * y) := by rw [pow_add]; ring
  rw [e]
  exact hx.mul hy

theorem cq_bd_add {m : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m * x)) (hy : IntAt P ((q : E) ^ m * y)) :
    IntAt P ((q : E) ^ m * (x + y)) := by
  rw [mul_add]
  exact hx.add hy

theorem cq_bd_sub {m : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m * x)) (hy : IntAt P ((q : E) ^ m * y)) :
    IntAt P ((q : E) ^ m * (x - y)) := by
  rw [mul_sub]
  exact ciIntAt_sub hx hy

theorem cq_bd_int (m : ℕ) {x : E} (hx : IntAt P x) : IntAt P ((q : E) ^ m * x) := by
  have hp : IntAt P ((q : E) ^ m) := by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ m)
    rwa [map_pow, map_natCast] at h
  exact hp.mul hx

theorem cq_bd_sum {ι : Type} (s : Finset ι) {m : ℕ} (f : ι → E) (h : ∀ i ∈ s, IntAt P ((q : E) ^ m * f i)) :
    IntAt P ((q : E) ^ m * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact ciIntAt_sum _ _ h

theorem cq_ar {a c e i v : ℕ} (hv : v < i) (hi : i < c) : a + (c - (i + 1)) * e + e ≤ a + (c - (v + 1)) * e := by
  have h1 : (c - (i + 1)) * e + e = (c - i) * e := by
    rw [show c - i = (c - (i + 1)) + 1 by omega, Nat.succ_mul]
  have h2 : (c - i) * e ≤ (c - (v + 1)) * e := Nat.mul_le_mul_right e (by omega)
  omega

theorem arithmetic_index_inequality {a c e i : ℕ} (hi : i < c) : a + (c - (i + 1)) * e + e ≤ a + c * e := by
  have h1 : (c - (i + 1)) * e + e = (c - i) * e := by
    rw [show c - i = (c - (i + 1)) + 1 by omega, Nat.succ_mul]
  have h2 : (c - i) * e ≤ c * e := Nat.mul_le_mul_right e (by omega)
  omega

theorem arithmetic_exponent_inequality {a c e v : ℕ} (hv : v + 1 < c) : e ≤ a + (c - (v + 1)) * e := by
  have : 1 * e ≤ (c - (v + 1)) * e := Nat.mul_le_mul_right e (by omega)
  omega

end TgtMain

section TgtThm

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def cqLev (n l : ℕ) : ℕ := if l < n then 0 else l - n + 1

set_option maxHeartbeats 1600000 in

theorem finite_sum_target_equality (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {K : Type} [Field K] {n' n c : ℕ} (psi : E → K) {D a b e A B : ℕ}
    (hadd : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → psi (x + y) = psi x * psi y)
    (hint : ∀ x : E, IntAt P x → psi x = 1) (Ψ : Loc.SF E K (n' + (c + 1)) (n + c))
    (hsupp : ∀ x, Ψ x ≠ 0 → ∀ s l, IntAt P ((q : E) ^ a * x (Pi.single s 1) l)) (haD : a ≤ D)
    (hinv : ∀ x z, (∀ s l, IntAt P (((q : E) ^ b)⁻¹ * z (Pi.single s 1) l)) → Ψ (x + z) = Ψ x)
    (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hr : r ∈ Loc.R1 E n c) (g : Sp E n ≃ₗ[E] Sp E n) (hgI : g ∈ GLint E n P)
    (hg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) (hre : ∀ s l, IntAt P ((q : E) ^ e * r (Pi.single s 1) l))
    (heD : e ≤ D) (hA : a + (c + 1) * e ≤ A) (hbB : b ≤ B) (wt : K) (y : HomE E n' n) :
    Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi (LocE.valsQ E q A B) wt (fun x => Ψ (r.toLinearMap ∘ₗ x)) y =
      psi (Loc.n1Arg r) * Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi (LocE.valsQ E q A B) wt Ψ (g.toLinearMap ∘ₗ y) := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  let ι := Loc.FC n' (c + 1) n c
  let V : Finset (ι → E) := Fintype.piFinset fun _ : ι => LocE.valsQ E q A B
  let Z : (ι → E) → Fin (n' + (c + 1)) → Fin (n + c) → E := fun t s => Loc.xx1 y t (Pi.single s 1)
  let T : (ι → E) → (ι → E) := fun t p => r (Z t p.1.2) p.1.1
  let y' := g.toLinearMap ∘ₗ y
  let G : (ι → E) → K := fun u =>
    Ψ (Loc.xx1 y' u) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' u))
  let bnd : Fin (n + c) → ℕ := fun m => a + (c - cqLev n m.1) * e
  let box : (ι → E) → Prop := fun t => ∀ p : ι, IntAt P ((q : E) ^ bnd p.1.1 * t p)

  have hxx : ∀ t, r.toLinearMap ∘ₗ Loc.xx1 y t = Loc.xx1 y' (T t) := fun t =>
    (PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_extractFree (PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_map hr.1 hg (PI.UnfoldEquiv.UnitaryGroupMassFormula.isFillOf_fillMatrix y t))).symm
  have hch : ∀ t, Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ Loc.xx1 y t) =
      Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t) + Loc.n1Arg r :=
    fun t => PI.UnfoldEquiv.UnitaryGroupMassFormula.chArg_map hr.1 (PI.UnfoldEquiv.UnitaryGroupMassFormula.isFillOf_fillMatrix y t)

  have hlevA : ∀ i : Fin c, cqLev n (Fin.natAdd n i).1 = i.1 + 1 := fun i => by
    unfold cqLev; rw [if_neg (by simp)]; simp
  have hlevX : ∀ j : Fin n, cqLev n (Fin.castAdd c j).1 = 0 := fun j => by
    unfold cqLev; rw [if_pos (by simp)]
  have hre' : ∀ (i : ℕ) (hi : n + i < n + c) (l : Fin (n + c)), IntAt P ((q : E) ^ e * r (Loc.eN E (n + c) (n + i)) l) := by
    intro i hi l
    rw [ocbS_eN_single hi]
    exact hre _ _
  have hcol : ∀ t (p : ι), Z t p.1.2 p.1.1 = t p := fun t p => by
    show Loc.xx1 y t (Pi.single p.1.2 1) p.1.1 = t p
    rw [free_point_column_entry, dif_pos p.2]
  have hfreeS : ∀ p : ι, n' ≤ p.1.2.1 := fun p => p.2.1
  have hXfree : ∀ (p : ι) (j : Fin n), Loc.IsFree n' n c (Fin.castAdd c j).1 p.1.2.1 := fun p j => by
    have h := p.2
    unfold Loc.IsFree at h ⊢
    simp only [Fin.coe_castAdd]
    have := j.2
    omega
  have hbase : ∀ (s : Fin (n' + (c + 1))) (m : Fin (n + c)), n' ≤ s.1 → IntAt P (PI.UnfoldEquiv.UnitaryGroupMassFormula.base y m s) := by
    intro s m hs
    unfold PI.UnfoldEquiv.UnitaryGroupMassFormula.base
    rw [dif_neg (by omega)]
    split_ifs
    · exact ciIntAt_one
    · exact ciIntAt_zero
  have hZbd : ∀ t, box t → ∀ (p : ι) (m : Fin (n + c)), IntAt P ((q : E) ^ bnd m * Z t p.1.2 m) := by
    intro t ht p m
    show IntAt P ((q : E) ^ bnd m * Loc.xx1 y t (Pi.single p.1.2 1) m)
    rw [free_point_column_entry]
    split_ifs with hf
    · exact ht ⟨(m, p.1.2), hf⟩
    · exact cq_bd_int _ (hbase _ _ (hfreeS p))
  have hgE : ∀ (j l : Fin n), IntAt P (g (Pi.single j 1) l) := fun j l =>
    (ciMem_stdAt P _).1 ((hgI _).2 (ciSingle_mem j)) l
  have hgE' : ∀ (j l : Fin n), IntAt P (g.symm (Pi.single j 1) l) := fun j l =>
    (ciMem_stdAt P _).1 (((Subgroup.inv_mem _ hgI : g⁻¹ ∈ GLint E n P) _).2 (ciSingle_mem j)) l

  have hTaux : ∀ t (p : ι) (v : Fin c), p.1.1 = Fin.natAdd n v → T t p = t p +
      ∑ i : Fin c, if v.1 < i.1 then Z t p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.natAdd n v) else 0 := by
    intro t p v hv
    show r (Z t p.1.2) p.1.1 = _
    rw [hv, reduction_entry_lower_block hr.1 hg, ← hv, hcol]
  have hTX : ∀ t (p : ι) (l0 : Fin n), p.1.1 = Fin.castAdd c l0 → T t p =
      g (fun j => Z t p.1.2 (Fin.castAdd c j)) l0 +
        ∑ i : Fin c, Z t p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.castAdd c l0) := by
    intro t p l0 hl0
    show r (Z t p.1.2) p.1.1 = _
    rw [hl0, cq_r_XRow hg]
  have hrow : ∀ p : ι, (∃ v : Fin c, p.1.1 = Fin.natAdd n v) ∨ ∃ l0 : Fin n, p.1.1 = Fin.castAdd c l0 := by
    intro p
    by_cases hl : p.1.1.1 < n
    · exact Or.inr ⟨⟨p.1.1.1, hl⟩, Fin.ext rfl⟩
    · exact Or.inl ⟨⟨p.1.1.1 - n, by have := p.1.1.2; omega⟩, Fin.ext (by simp; omega)⟩
  have hTbd : ∀ t, box t → ∀ p, IntAt P ((q : E) ^ bnd p.1.1 * T t p) := by
    intro t ht p
    rcases hrow p with ⟨v, hv⟩ | ⟨l0, hl0⟩
    · have hb : bnd p.1.1 = a + (c - (v.1 + 1)) * e := by
        show a + (c - cqLev n p.1.1.1) * e = _
        rw [hv, hlevA]
      rw [hTaux t p v hv, hb]
      refine cq_bd_add ?_ (cq_bd_sum _ _ fun i _ => ?_)
      · have := ht p
        rwa [hb] at this
      · split_ifs with hvi
        · have h1 := hZbd t ht p (Fin.natAdd n i)
          have hbi : bnd (Fin.natAdd n i) = a + (c - (i.1 + 1)) * e := by
            show a + (c - cqLev n (Fin.natAdd n i).1) * e = _
            rw [hlevA]
          rw [hbi] at h1
          exact cq_bd_mono (cq_bd_mul h1 (hre' i.1 (by omega) _)) (cq_ar hvi i.2)
        · rw [mul_zero]
          exact ciIntAt_zero
    · have hb : bnd p.1.1 = a + c * e := by
        show a + (c - cqLev n p.1.1.1) * e = _
        rw [hl0, hlevX, Nat.sub_zero]
      rw [hTX t p l0 hl0, hb]
      refine cq_bd_add ?_ (cq_bd_sum _ _ fun i _ => ?_)
      · rw [residue_linearEquiv_apply_eq_sum g]
        refine cq_bd_sum _ _ fun j _ => ?_
        have h1 := hZbd t ht p (Fin.castAdd c j)
        have hbj : bnd (Fin.castAdd c j) = a + c * e := by
          show a + (c - cqLev n (Fin.castAdd c j).1) * e = _
          rw [hlevX, Nat.sub_zero]
        rw [hbj] at h1
        have h2 := cq_bd_mul (cq_bd_int 0 (hgE j l0)) h1
        rwa [zero_add] at h2
      · have h1 := hZbd t ht p (Fin.natAdd n i)
        have hbi : bnd (Fin.natAdd n i) = a + (c - (i.1 + 1)) * e := by
          show a + (c - cqLev n (Fin.natAdd n i).1) * e = _
          rw [hlevA]
        rw [hbi] at h1
        exact cq_bd_mono (cq_bd_mul h1 (hre' i.1 (by omega) _)) (arithmetic_index_inequality i.2)
  have hbA : ∀ m : Fin (n + c), bnd m ≤ A := by
    intro m
    have : (c - cqLev n m.1) * e ≤ (c + 1) * e := Nat.mul_le_mul_right e (by omega)
    show a + (c - cqLev n m.1) * e ≤ A
    omega
  let ρ : E → E := fun x => if h : IntAt P ((q : E) ^ A * x) then Classical.choose (cq_rep hq hu hp hcard A B x h) else x
  have hρ : ∀ x, IntAt P ((q : E) ^ A * x) → ρ x ∈ LocE.valsQ E q A B ∧ IntAt P ((x - ρ x) / (q : E) ^ B) := by
    intro x h
    simp only [ρ, dif_pos h]
    exact Classical.choose_spec (cq_rep hq hu hp hcard A B x h)
  let σ : (ι → E) → (ι → E) := fun t p => ρ (T t p)
  let W : Finset (ι → E) := V.filter box

  have hσW : ∀ t ∈ W, σ t ∈ W := by
    intro t ht
    obtain ⟨-, htb⟩ := Finset.mem_filter.1 ht
    have hT := hTbd t htb
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun p => (hρ _ (cq_bd_mono (hT p) (hbA _))).1, fun p => ?_⟩
    have h2 := (hρ _ (cq_bd_mono (hT p) (hbA _))).2
    show IntAt P ((q : E) ^ bnd p.1.1 * ρ (T t p))
    have e1 : (q : E) ^ bnd p.1.1 * ρ (T t p) =
        (q : E) ^ bnd p.1.1 * T t p - (q : E) ^ (bnd p.1.1 + B) * ((T t p - ρ (T t p)) / (q : E) ^ B) := by
      rw [pow_add]
      field_simp
      ring
    rw [e1]
    exact ciIntAt_sub (hT p) (cq_bd_int _ h2)

  have hinj : Set.InjOn σ W := by
    intro t ht t' ht' hσ
    obtain ⟨htV, htb⟩ := Finset.mem_filter.1 ht
    obtain ⟨htV', htb'⟩ := Finset.mem_filter.1 ht'
    have hd : ∀ p, IntAt P ((T t p - T t' p) / (q : E) ^ B) := fun p => by
      have h1 := (hρ _ (cq_bd_mono (hTbd t htb p) (hbA _))).2
      have h2 := (hρ _ (cq_bd_mono (hTbd t' htb' p) (hbA _))).2
      have he : ρ (T t p) = ρ (T t' p) := congrFun hσ p
      have e1 : (T t p - T t' p) / (q : E) ^ B = (T t p - ρ (T t p)) / (q : E) ^ B - (T t' p - ρ (T t' p)) / (q : E) ^ B := by
        rw [he]
        ring
      rw [e1]
      exact ciIntAt_sub h1 h2
    have hvals : ∀ p, t p ∈ LocE.valsQ E q A B ∧ t' p ∈ LocE.valsQ E q A B :=
      fun p => ⟨Fintype.mem_piFinset.1 htV p, Fintype.mem_piFinset.1 htV' p⟩
    have hA' : ∀ k, ∀ p : ι, ∀ v : Fin c, p.1.1 = Fin.natAdd n v → c - v.1 = k → t p = t' p := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro p v hv hk
        have e2 : T t p - T t' p = t p - t' p := by
          rw [hTaux t p v hv, hTaux t' p v hv]
          have hs : ∀ i : Fin c, (if v.1 < i.1 then Z t p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.natAdd n v) else 0) =
              (if v.1 < i.1 then Z t' p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.natAdd n v) else 0) := by
            intro i
            split_ifs with hvi
            · congr 1
              show Loc.xx1 y t (Pi.single p.1.2 1) (Fin.natAdd n i) = Loc.xx1 y t' (Pi.single p.1.2 1) (Fin.natAdd n i)
              rw [free_point_column_entry, free_point_column_entry]
              split_ifs with hf
              · exact ih (c - i.1) (by omega) ⟨(Fin.natAdd n i, p.1.2), hf⟩ i rfl rfl
              · rfl
            · rfl
          rw [Finset.sum_congr rfl (fun i _ => hs i)]
          ring
        have h3 := hd p
        rw [e2] at h3
        exact cq_rep_unique hq hu hp (hvals p).1 (hvals p).2 h3
    funext p
    rcases hrow p with ⟨v, hv⟩ | ⟨l0, hl0⟩
    · exact hA' _ p v hv rfl
    · have hZaux : ∀ i : Fin c, Z t p.1.2 (Fin.natAdd n i) = Z t' p.1.2 (Fin.natAdd n i) := fun i => by
        show Loc.xx1 y t (Pi.single p.1.2 1) (Fin.natAdd n i) = Loc.xx1 y t' (Pi.single p.1.2 1) (Fin.natAdd n i)
        rw [free_point_column_entry, free_point_column_entry]
        split_ifs with hf
        · exact hA' _ ⟨(Fin.natAdd n i, p.1.2), hf⟩ i rfl rfl
        · rfl
      have hgΔ : ∀ l1 : Fin n, IntAt P ((g (fun j => Z t p.1.2 (Fin.castAdd c j)) l1 -
          g (fun j => Z t' p.1.2 (Fin.castAdd c j)) l1) / (q : E) ^ B) := by
        intro l1
        let p1 : ι := ⟨(Fin.castAdd c l1, p.1.2), hXfree p l1⟩
        have e3 : T t p1 - T t' p1 = g (fun j => Z t p.1.2 (Fin.castAdd c j)) l1 - g (fun j => Z t' p.1.2 (Fin.castAdd c j)) l1 := by
          rw [hTX t p1 l1 rfl, hTX t' p1 l1 rfl]
          show g (fun j => Z t p.1.2 (Fin.castAdd c j)) l1 + ∑ i : Fin c, Z t p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.castAdd c l1) -
            (g (fun j => Z t' p.1.2 (Fin.castAdd c j)) l1 + ∑ i : Fin c, Z t' p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.castAdd c l1)) = _
          rw [Finset.sum_congr rfl (fun i _ => by rw [hZaux i])]
          ring
        have h3 := hd p1
        rwa [e3] at h3
      have hΔ : ∀ j : Fin n, IntAt P ((Z t p.1.2 (Fin.castAdd c j) - Z t' p.1.2 (Fin.castAdd c j)) / (q : E) ^ B) := by
        intro j
        have e4 : Z t p.1.2 (Fin.castAdd c j) - Z t' p.1.2 (Fin.castAdd c j) =
            g.symm (g (fun j => Z t p.1.2 (Fin.castAdd c j)) - g (fun j => Z t' p.1.2 (Fin.castAdd c j))) j := by
          rw [← map_sub, LinearEquiv.symm_apply_apply]
          rfl
        rw [e4, residue_linearEquiv_apply_eq_sum g.symm, Finset.sum_div]
        refine ciIntAt_sum _ _ fun l1 _ => ?_
        rw [mul_div_assoc, Pi.sub_apply]
        exact (hgE' l1 j).mul (hgΔ l1)
      have e5 : t p - t' p = Z t p.1.2 (Fin.castAdd c l0) - Z t' p.1.2 (Fin.castAdd c l0) := by
        rw [← hl0, hcol, hcol]
      have h3 := hΔ l0
      rw [← e5] at h3
      exact cq_rep_unique hq hu hp (hvals p).1 (hvals p).2 h3

  have hT_W : ∀ t ∈ V, G (T t) ≠ 0 → t ∈ W := by
    intro t htV hG
    have hΨ : Ψ (Loc.xx1 y' (T t)) ≠ 0 := fun h => hG (by show Ψ _ * _ = 0; rw [h, zero_mul])
    have hS := hsupp _ hΨ
    have hTa : ∀ p : ι, IntAt P ((q : E) ^ a * T t p) := fun p => by
      have h1 := hS p.1.2 p.1.1
      rwa [free_point_column_entry, dif_pos p.2] at h1
    have hA' : ∀ k, ∀ p : ι, ∀ v : Fin c, p.1.1 = Fin.natAdd n v → c - v.1 = k →
        IntAt P ((q : E) ^ (a + (c - (v.1 + 1)) * e) * t p) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro p v hv hk
        have e2 : t p = T t p - ∑ i : Fin c, (if v.1 < i.1 then Z t p.1.2 (Fin.natAdd n i) *
            r (Loc.eN E (n + c) (n + i.1)) (Fin.natAdd n v) else 0) := by
          rw [hTaux t p v hv]
          ring
        rw [e2]
        refine cq_bd_sub (cq_bd_mono (hTa p) (by omega)) (cq_bd_sum _ _ fun i _ => ?_)
        split_ifs with hvi
        · have hZi : IntAt P ((q : E) ^ (a + (c - (i.1 + 1)) * e) * Z t p.1.2 (Fin.natAdd n i)) := by
            show IntAt P (_ * Loc.xx1 y t (Pi.single p.1.2 1) (Fin.natAdd n i))
            rw [free_point_column_entry]
            split_ifs with hf
            · exact ih (c - i.1) (by omega) ⟨(Fin.natAdd n i, p.1.2), hf⟩ i rfl rfl
            · exact cq_bd_int _ (hbase _ _ (hfreeS p))
          exact cq_bd_mono (cq_bd_mul hZi (hre' i.1 (by omega) _)) (cq_ar hvi i.2)
        · rw [mul_zero]
          exact ciIntAt_zero
    have hZaux : ∀ (p : ι) (i : Fin c), IntAt P ((q : E) ^ (a + (c - (i.1 + 1)) * e) * Z t p.1.2 (Fin.natAdd n i)) := by
      intro p i
      show IntAt P (_ * Loc.xx1 y t (Pi.single p.1.2 1) (Fin.natAdd n i))
      rw [free_point_column_entry]
      split_ifs with hf
      · exact hA' _ ⟨(Fin.natAdd n i, p.1.2), hf⟩ i rfl rfl
      · exact cq_bd_int _ (hbase _ _ (hfreeS p))
    refine Finset.mem_filter.2 ⟨htV, fun p => ?_⟩
    rcases hrow p with ⟨v, hv⟩ | ⟨l0, hl0⟩
    · have hb : bnd p.1.1 = a + (c - (v.1 + 1)) * e := by
        show a + (c - cqLev n p.1.1.1) * e = _
        rw [hv, hlevA]
      rw [hb]
      exact hA' _ p v hv rfl
    · have hb : bnd p.1.1 = a + c * e := by
        show a + (c - cqLev n p.1.1.1) * e = _
        rw [hl0, hlevX, Nat.sub_zero]
      rw [hb]
      have hgX : ∀ l1 : Fin n, IntAt P ((q : E) ^ (a + c * e) * g (fun j => Z t p.1.2 (Fin.castAdd c j)) l1) := by
        intro l1
        let p1 : ι := ⟨(Fin.castAdd c l1, p.1.2), hXfree p l1⟩
        have e3 : g (fun j => Z t p.1.2 (Fin.castAdd c j)) l1 = T t p1 -
            ∑ i : Fin c, Z t p.1.2 (Fin.natAdd n i) * r (Loc.eN E (n + c) (n + i.1)) (Fin.castAdd c l1) := by
          rw [hTX t p1 l1 rfl]
          ring
        rw [e3]
        exact cq_bd_sub (cq_bd_mono (hTa p1) (by omega))
          (cq_bd_sum _ _ fun i _ => cq_bd_mono (cq_bd_mul (hZaux p i) (hre' i.1 (by omega) _)) (arithmetic_index_inequality i.2))
      have e4 : t p = g.symm (g (fun j => Z t p.1.2 (Fin.castAdd c j))) l0 := by
        rw [LinearEquiv.symm_apply_apply, ← hl0, hcol]
      rw [e4, residue_linearEquiv_apply_eq_sum g.symm]
      refine cq_bd_sum _ _ fun l1 _ => ?_
      have h2 := cq_bd_mul (cq_bd_int 0 (hgE' l1 l0)) (hgX l1)
      rwa [zero_add] at h2
  have hG_W : ∀ u ∈ V, G u ≠ 0 → u ∈ W := by
    intro u huV hG
    have hΨ : Ψ (Loc.xx1 y' u) ≠ 0 := fun h => hG (by show Ψ _ * _ = 0; rw [h, zero_mul])
    have hS := hsupp _ hΨ
    refine Finset.mem_filter.2 ⟨huV, fun p => ?_⟩
    have h1 := hS p.1.2 p.1.1
    rw [free_point_column_entry, dif_pos p.2] at h1
    exact cq_bd_mono h1 (by show a ≤ a + (c - cqLev n p.1.1.1) * e; omega)

  have hatN_add : ∀ (v w : Fin (n + c) → E) (i : ℕ), Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
    intro v w i
    unfold Loc.atN
    split_ifs
    · rfl
    · rw [add_zero]
  have hchA : ∀ X Y : (Fin (n' + (c + 1)) → E) →ₗ[E] (Fin (n + c) → E),
      Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (X + Y) =
        Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) X + Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) Y := by
    intro X Y
    unfold Loc.chArg
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.add_apply, hatN_add]
  have hchBd : ∀ (m : ℕ) (X : (Fin (n' + (c + 1)) → E) →ₗ[E] (Fin (n + c) → E)), (∀ s l, IntAt P ((q : E) ^ m * X (Pi.single s 1) l)) →
      IntAt P ((q : E) ^ m * Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) X) := by
    intro m X hX
    unfold Loc.chArg
    refine cq_bd_sum _ _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [ocbS_eN_single (show n' + i + 1 < n' + (c + 1) by omega), ocbS_atN_of_lt _ (show n + i < n + c by omega)]
    exact hX _ _
  have hGσ : ∀ t ∈ W, G (σ t) = G (T t) := by
    intro t ht
    obtain ⟨-, htb⟩ := Finset.mem_filter.1 ht
    have hT := hTbd t htb
    have hd : ∀ p, IntAt P ((σ t p - T t p) / (q : E) ^ B) := fun p => by
      have h2 := (hρ _ (cq_bd_mono (hT p) (hbA _))).2
      have e1 : (σ t p - T t p) / (q : E) ^ B = -((T t p - ρ (T t p)) / (q : E) ^ B) := by
        show (ρ (T t p) - T t p) / (q : E) ^ B = _
        ring
      rw [e1]
      exact ciIntAt_neg h2
    let z := Loc.xx1 y' (σ t) - Loc.xx1 y' (T t)
    have hz : ∀ s l, z (Pi.single s 1) l =
        if hf : Loc.IsFree n' n c l.1 s.1 then σ t ⟨(l, s), hf⟩ - T t ⟨(l, s), hf⟩ else 0 := by
      intro s l
      show (Loc.xx1 y' (σ t) - Loc.xx1 y' (T t)) (Pi.single s 1) l = _
      rw [LinearMap.sub_apply, Pi.sub_apply, free_point_column_entry, free_point_column_entry]
      split_ifs
      · rfl
      · rw [sub_self]
    have hzB : ∀ s l, IntAt P (z (Pi.single s 1) l / (q : E) ^ B) := by
      intro s l
      rw [hz]
      split_ifs with hf
      · exact hd ⟨(l, s), hf⟩
      · rw [zero_div]
        exact ciIntAt_zero
    have hzb : ∀ s l, IntAt P (((q : E) ^ b)⁻¹ * z (Pi.single s 1) l) := by
      intro s l
      have e1 : ((q : E) ^ b)⁻¹ * z (Pi.single s 1) l = (q : E) ^ (B - b) * (z (Pi.single s 1) l / (q : E) ^ B) := by
        rw [show (q : E) ^ B = (q : E) ^ (B - b) * (q : E) ^ b by rw [← pow_add, Nat.sub_add_cancel hbB]]
        field_simp
      rw [e1]
      exact cq_bd_int _ (hzB s l)
    have hzI : ∀ s l, IntAt P (z (Pi.single s 1) l) := by
      intro s l
      have e1 : z (Pi.single s 1) l = (q : E) ^ B * (z (Pi.single s 1) l / (q : E) ^ B) := by
        field_simp
      rw [e1]
      exact cq_bd_int _ (hzB s l)
    have hxz : Loc.xx1 y' (σ t) = Loc.xx1 y' (T t) + z := by
      show _ = Loc.xx1 y' (T t) + (Loc.xx1 y' (σ t) - Loc.xx1 y' (T t))
      abel
    show Ψ (Loc.xx1 y' (σ t)) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (σ t))) =
      Ψ (Loc.xx1 y' (T t)) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (T t)))
    rw [hxz, hinv _ z hzb]
    by_cases h0 : Ψ (Loc.xx1 y' (T t)) = 0
    · rw [h0, zero_mul, zero_mul]
    · congr 1
      have hcz : IntAt P (Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) z) := by
        have h1 := hchBd 0 z (fun s l => cq_bd_int 0 (hzI s l))
        rwa [pow_zero, one_mul] at h1
      have hcX := hchBd a _ (hsupp _ h0)
      rw [hchA, neg_add, hadd _ _ (by rw [mul_neg]; exact ciIntAt_neg (cq_bd_mono hcX haD)) (cq_bd_int D (ciIntAt_neg hcz)),
        hint _ (ciIntAt_neg hcz), mul_one]
  have hsum : ∑ t ∈ V, G (T t) = ∑ u ∈ V, G u :=
    cq_sum_perm V W (Finset.filter_subset _ _) T σ G hT_W hG_W hσW hinj hGσ

  have hn1Bd : IntAt P ((q : E) ^ e * Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine cq_bd_sum _ _ fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [ocbS_atN_of_lt _ (show n + i < n + c by omega)]
    exact hre' (i + 1) (by omega) _
  have hterm : ∀ t, Ψ (r.toLinearMap ∘ₗ Loc.xx1 y t) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t)) =
      psi (Loc.n1Arg r) * G (T t) := by
    intro t
    have e1 : Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t) =
        Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (T t)) - Loc.n1Arg r := by
      rw [← hxx t, hch t]
      ring
    rw [e1, hxx t]
    show _ = psi (Loc.n1Arg r) * (Ψ (Loc.xx1 y' (T t)) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (T t))))
    by_cases h0 : Ψ (Loc.xx1 y' (T t)) = 0
    · rw [h0, zero_mul, zero_mul, mul_zero]
    · have hcX := hchBd a _ (hsupp _ h0)
      rw [show -(Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (T t)) - Loc.n1Arg r) =
          -Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y' (T t)) + Loc.n1Arg r by ring,
        hadd _ _ (by rw [mul_neg]; exact ciIntAt_neg (cq_bd_mono hcX haD)) (cq_bd_mono hn1Bd heD)]
      ring
  unfold Loc.E1
  simp only []
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.mul_sum, hsum]
  ring

end TgtThm

end Formalism.L2.Col
