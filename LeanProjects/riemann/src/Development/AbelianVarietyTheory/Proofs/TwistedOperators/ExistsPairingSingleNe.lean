import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGl1UnitValuation

noncomputable section

namespace GlobalTheory.SphTheta

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

def antiG (L : Type) [Field L] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, P.fIwasawa_antiJ_mul_antiJ, P.fIwasawa_antiJ_mul_antiJ⟩

def hi (n : ℕ) (k : Fin (n / 2)) : Fin n := ⟨n - n / 2 + k, by omega⟩

def lo (n : ℕ) (k : Fin (n / 2)) : Fin n := ⟨k, by omega⟩

def liftPar (q : ℂˣ) (n n' : ℕ) (α : Fin (n / 2) → ℂˣ) (k : Fin (n' / 2)) : ℂˣ :=
  if h : k.1 < n' / 2 - n / 2 then (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * (k.1 : ℤ))
  else (-1) ^ (n + n') * (α ⟨n' / 2 - 1 - k.1, by omega⟩)⁻¹

section

variable {L : Type} [Field L]

def embLow (n' n : ℕ) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) : Matrix (Fin n') (Fin n) L := fun r c =>
  if h : n' - n' / 2 ≤ r.1 ∧ n - n / 2 ≤ c.1 then z ⟨r.1 - (n' - n' / 2), by omega⟩ ⟨c.1 - (n - n / 2), by omega⟩ else 0

def lowBlock {n : ℕ} (g : Matrix (Fin n) (Fin n) L) : Matrix (Fin (n / 2)) (Fin (n / 2)) L := g.submatrix (hi n) (hi n)

def pairing (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) {n n' : ℕ} (x y : Matrix (Fin n') (Fin n) L) : ℂ :=
  ψ (δ * (∑ i, ∑ j, x i j * σ (y i.rev j.rev)) + σ (δ * (∑ i, ∑ j, x i j * σ (y i.rev j.rev))))

def conjU {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (n : ℕ) : GU σ n →* GU σ n :=
  ((bc σ).comp (GU σ n).subtype).codRestrict _ fun g => by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) L => M.map σ) (show cT σ g.1.1 * antiJ L n * g.1.1 = antiJ L n from g.2)
    have hJ : (antiJ L n).map σ = antiJ L n := by
      ext i j
      simp only [Matrix.map_apply, antiJ]
      split_ifs <;> simp
    simp only [Matrix.map_mul, hJ] at h
    exact h

variable [Valued L (WithZero (Multiplicative ℤ))]

variable (L) in

def intMat (α β : Type) : Submodule (intL L) (Matrix α β L) where
  carrier := {x | ∀ i j, x i j ∈ intL L}
  add_mem' h h' i j := add_mem (h i j) (h' i j)
  zero_mem' _ _ := zero_mem _
  smul_mem' r _ h i j := mul_mem r.2 (h i j)

variable (L) in

def mixLat (n' n : ℕ) : Submodule (intL L) (Matrix (Fin n') (Fin n) L) where
  carrier := {x | ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
    (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L)}
  add_mem' h h' r c := ⟨fun e => by rw [Matrix.add_apply, (h r c).1 e, (h' r c).1 e, add_zero],
    fun e e' => add_mem ((h r c).2 e e') ((h' r c).2 e e')⟩
  zero_mem' _ _ := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' a x h r c := ⟨fun e => by rw [Matrix.smul_apply, (h r c).1 e, smul_zero],
    fun e e' => mul_mem a.2 ((h r c).2 e e')⟩

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def CayleyRule {σ : L →+* L} {n : ℕ} (q N : ℕ) {α β : Type} (ρ : Matrix α β L → Module.End ℂ M)
    (π : GU σ n →* Module.End ℂ M) (s : M) : Prop :=
  ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L α β, ∀ v, e (ρ u v) = e v) → ∀ g : GU σ n, (1 + g.1.1).det ≠ 0 →
    (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → e (π g⁻¹ s) = ((-1) ^ N * (q : ℂ) ^ N) ^ ordL (1 + g.1.1).det * e s

def IsStd (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) {n n' : ℕ}
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M) : Prop :=
  LocPair ϖ σ q δ (antiG L n) (antiG L n') ψ ρ ω ∧ s ≠ 0 ∧ LocVac ρ s ∧ Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_mul_apply {n : ℕ} {β : Type} (A : Matrix (Fin n) β L) (i : Fin n) (j : β) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, P.fIwasawa_antiJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mul_antiJ_apply {n : ℕ} {β : Type} (A : Matrix β (Fin n) L) (i : β) (j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  simp only [Matrix.mul_apply, P.fIwasawa_antiJ, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j.rev] <;> simp +contextual [eq_comm (a := j), Fin.rev_eq_iff]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem locH_antiG (σ : L →+* L) (δ : L) {n n' : ℕ} (x y : Matrix (Fin n') (Fin n) L) :
    locH σ δ (antiG L n) (antiG L n') x y = δ * ∑ i, ∑ j, x i j * σ (y i.rev j.rev) := by
  show δ * Matrix.trace (antiJ L n * (y.map σ)ᵀ * antiJ L n' * x) = _
  congr 1
  rw [Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_antiJ_apply, antiJ_mul_apply, mul_comm]
  rfl

theorem mem_intL {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

def intConj {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict _ fun x => mem_intL.2 ((hv x).trans_le x.2)

def half (h2 : Valued.v (2 : L) = 1) : intL L := ⟨2⁻¹, mem_intL.2 (by rw [map_inv₀, h2, inv_one])⟩

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem two_ne_zero_of (h2 : Valued.v (2 : L) = 1) : (2 : L) ≠ 0 := fun h => by simp [h] at h2

theorem isHeis_of (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (h2 : Valued.v (2 : L) = 1)
    (hδ : σ δ = -δ) {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} (h0 : ρ 0 = 1)
    (hm : ∀ x y, ρ x * ρ y = ψ ((locH σ δ (antiG L n) (antiG L n') x y +
      σ (locH σ δ (antiG L n) (antiG L n') x y)) / 2) • ρ (x + y)) :
    IsHeis (intConj hv) (half h2) (pairing σ δ ψ) ρ where
  sg_sg r := Subtype.ext (hσ r)
  w_add := Subtype.ext (by
    have := two_ne_zero_of h2
    show (2⁻¹ : L) + σ 2⁻¹ = 1
    rw [map_inv₀, map_ofNat]; field_simp; norm_num)
  add_left x y z := by
    simp only [pairing, ← AddChar.map_add_eq_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]
    congr 1; ring
  add_right x y z := by
    simp only [pairing, ← AddChar.map_add_eq_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]
    congr 1; ring
  alt x := by
    have : σ (∑ i, ∑ j, x i j * σ (x i.rev j.rev)) = ∑ i, ∑ j, x i j * σ (x i.rev j.rev) := by
      simp only [map_sum, map_mul, hσ]
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm]
      simp [mul_comm]
    rw [pairing, map_mul, this, hδ, neg_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  adj r x y := by
    have : ∀ i j, (r • x) i j * σ (y i.rev j.rev) = x i j * σ ((intConj hv r • y) i.rev j.rev) := fun i j => by
      show (r : L) * x i j * _ = x i j * σ (σ r * y i.rev j.rev)
      rw [map_mul, hσ]; ring
    simp only [pairing, this]
  zero v := by rw [h0]; rfl
  comp x y v := by
    have e : ∀ i j, (half h2 • x) i j * σ (y i.rev j.rev) = 2⁻¹ * (x i j * σ (y i.rev j.rev)) := fun i j =>
      mul_assoc _ _ _
    rw [← Module.End.mul_apply, hm, locH_antiG, pairing]
    simp only [e, ← Finset.mul_sum, map_mul, map_inv₀, map_ofNat, LinearMap.smul_apply]
    congr 2; ring

theorem pairing_single (x : Matrix (Fin n') (Fin n) L) (i : Fin n') (j : Fin n) (u : L) :
    pairing σ δ ψ x (Matrix.single i.rev j.rev u) = ψ (δ * (x i j * σ u) + σ (δ * (x i j * σ u))) := by
  have : ∑ i', ∑ j', x i' j' * σ (Matrix.single i.rev j.rev u i'.rev j'.rev) = x i j * σ u := by
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply_of_col_ne _ _ (fun h => hb (Fin.rev_injective h).symm), map_zero, mul_zero]
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply_of_row_ne (fun h => hb (Fin.rev_injective h).symm), map_zero, mul_zero]
    · simp
  rw [pairing, this]

theorem exists_pairing_single_ne (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) (hδ : Valued.v δ = 1)
    (hψ : ∃ a ∈ intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L) {i : Fin n'} {j : Fin n}
    (hx : x i j ∉ intL L) : ∃ u ∈ intL L, pairing σ δ ψ x (Matrix.single i.rev j.rev u) ≠ 1 := by
  obtain ⟨a, ha, ha', hne⟩ := hψ
  have h0 : x i j ≠ 0 := fun h => hx (h ▸ zero_mem _)
  have hd : δ ≠ 0 := fun h => by simp [h] at hδ
  have h20 := two_ne_zero_of h2
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨σ (ϖ⁻¹ * a / (2 * δ * x i j)), mem_intL.2 ?_, ?_⟩
  · have hv0 : Valued.v (x i j) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h1 : WithZero.exp (1 : ℤ) ≤ Valued.v (x i j) := by
      rw [mem_intL, not_le, ← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
      rw [← WithZero.exp_log hv0, WithZero.exp_le_exp]; omega
    rw [hU.2.1, map_div₀, map_mul, map_mul, map_mul, h2, hδ, one_mul, one_mul, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      div_le_one₀ (zero_lt_iff.2 hv0)]
    exact (mul_le_of_le_one_right' ha).trans h1
  · have : δ * (x i j * (ϖ⁻¹ * a / (2 * δ * x i j))) = ϖ⁻¹ * a / 2 := by field_simp
    rw [pairing_single, hU.1, this, map_div₀, map_mul, map_inv₀, hU.2.2.1, ha', map_ofNat, show ϖ⁻¹ * a / 2 + ϖ⁻¹ * a / 2 = ϖ⁻¹ * a by field_simp; norm_num]
    exact hne

theorem selfDual_intMat (hU : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) (hψ : ∃ a ∈ intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) :
    SelfDual (pairing σ δ ψ) (intMat L (Fin n') (Fin n)) := by
  have hs : ∀ a ∈ intL L, σ a ∈ intL L := fun a ha => mem_intL.2 ((hU.2.1 a).trans_le ha)
  refine fun x => ⟨fun hx y hy => ?_, fun h i j => ?_⟩
  · have : δ * ∑ i, ∑ j, x i j * σ (y i.rev j.rev) ∈ intL L :=
      mul_mem (mem_intL.2 hδ.le) (sum_mem fun i _ => sum_mem fun j _ => mul_mem (hx i j) (hs _ (hy _ _)))
    exact hψ0 _ (add_mem this (hs _ this)) (by rw [map_add, hU.1, add_comm])
  · by_contra hx
    obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne hU h2 hδ hψ x hx
    refine hne (h _ fun i' j' => ?_)
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]

variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.v_two (h : IsStd ϖ σ q δ ψ ρ ω s) : Valued.v (2 : L) = 1 := LatModel.v_two h.1.unr h.1.odd

theorem IsStd.isHeis (h : IsStd ϖ σ q δ ψ ρ ω s) : IsHeis (intConj h.1.unr.2.1) (half h.v_two) (pairing σ δ ψ) ρ :=
  isHeis_of h.1.unr.1 h.1.unr.2.1 h.v_two h.1.delta.2 h.1.rho_zero h.1.rho_mul

theorem IsStd.selfDual (h : IsStd ϖ σ q δ ψ ρ ω s) : SelfDual (pairing σ δ ψ) (intMat L (Fin n') (Fin n)) :=
  selfDual_intMat h.1.unr h.v_two h.1.delta.1 h.1.psi_int h.1.psi_ne

theorem IsStd.fixes (h : IsStd ϖ σ q δ ψ ρ ω s) : Fixes ρ (intMat L (Fin n') (Fin n)) s := h.2.2.1

theorem mem_KU_iff {g : GU σ n} : g ∈ KU σ n ↔ (g : GL (Fin n) L) ∈ GLint (Fin n) (intL L) :=
  ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

end

end GlobalTheory.SphTheta

end
