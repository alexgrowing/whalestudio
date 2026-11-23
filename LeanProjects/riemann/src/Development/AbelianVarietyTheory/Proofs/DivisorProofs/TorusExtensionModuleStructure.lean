import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TorCls.OpenP

theorem mem_range_map_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (X : GL (Fin n) R)
    (h1 : ∀ i j, (X : Matrix (Fin n) (Fin n) R) i j ∈ S)
    (h2 : ∀ i j, ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ S) :
    X ∈ (GeneralLinearGroup.map S.subtype).range := by
  let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hA : A.map S.subtype = (X : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have hB : B.map S.subtype = ((X⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by ext i j; rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.mul_inv)
  have hBA : B * A = 1 := inj (by
    simp only [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero S.subtype) (map_one S.subtype)]
    exact X.inv_mul)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : L) :
    ∃ N : ℕ, (((p : L) ^ N * x : L) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (‖(x : PadicAlgCl p)‖ + 1) by positivity) hp
  refine ⟨N, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.2 ?_⟩
  have e : (((p : L) ^ N * x : L) : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (x : PadicAlgCl p) := by
    simp
  rw [e, norm_mul, norm_pow]
  have h0 : 0 ≤ ‖(x : PadicAlgCl p)‖ := norm_nonneg _
  calc ‖(p : PadicAlgCl p)‖ ^ N * ‖(x : PadicAlgCl p)‖ ≤ 1 / (‖(x : PadicAlgCl p)‖ + 1) * (‖(x : PadicAlgCl p)‖ + 1) :=
        mul_le_mul hN.le (by linarith) h0 (by positivity)
    _ = 1 := by field_simp

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r N : ℕ) :
    (p : KQ p K r) ^ N ∈ intKQ p K r :=
  pow_mem (natCast_mem _ p) N

theorem inclK_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : K)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclK p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨x, h⟩, rfl⟩)

theorem inclQ_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : Qr p r)
    (h : (x : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p) : inclQ p K r x ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨x, h⟩, rfl⟩)

theorem tmul_eq_inclK_mul_inclQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) (b : Qr p r) :
    (show KQ p K r from a ⊗ₜ[ℚ_[p]] b) = inclK p K r a * inclQ p K r b := by
  change a ⊗ₜ[ℚ_[p]] b = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_pow_mul_mem_intKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r) :
    ∃ N : ℕ, (p : KQ p K r) ^ N * x ∈ intKQ p K r := by
  refine TensorProduct.induction_on (R := ℚ_[p]) (M := K) (N := Qr p r)
    (motive := fun y : K ⊗[ℚ_[p]] Qr p r => ∃ N : ℕ, (p : KQ p K r) ^ N * (show KQ p K r from y) ∈ intKQ p K r) x
    ⟨0, ?_⟩ ?_ ?_
  · change (p : KQ p K r) ^ 0 * (0 : KQ p K r) ∈ intKQ p K r
    rw [mul_zero]; exact zero_mem _
  · intro a b
    obtain ⟨N₁, h₁⟩ := exists_pow_mul_mem p K a
    obtain ⟨N₂, h₂⟩ := exists_pow_mul_mem p (Qr p r) b
    refine ⟨N₁ + N₂, ?_⟩
    rw [tmul_eq_inclK_mul_inclQ]
    have e : (p : KQ p K r) ^ (N₁ + N₂) * (inclK p K r a * inclQ p K r b) =
        inclK p K r ((p : K) ^ N₁ * a) * inclQ p K r ((p : Qr p r) ^ N₂ * b) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, pow_add]; ring
    rw [e]
    exact mul_mem (inclK_mem_intKQ p K r _ h₁) (inclQ_mem_intKQ p K r _ h₂)
  · rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, ?_⟩
    change (p : KQ p K r) ^ (N + M) * ((show KQ p K r from x) + (show KQ p K r from y)) ∈ intKQ p K r
    generalize (show KQ p K r from x) = x' at hN ⊢
    generalize (show KQ p K r from y) = y' at hM ⊢
    have e : (p : KQ p K r) ^ (N + M) * (x' + y') =
        (p : KQ p K r) ^ M * ((p : KQ p K r) ^ N * x') + (p : KQ p K r) ^ N * ((p : KQ p K r) ^ M * y') := by
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_pow_mem_intKQ p K r M) hN) (mul_mem (natCast_pow_mem_intKQ p K r N) hM)

theorem exists_pow_mul_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (KQ p K r)) :
    ∃ N : ℕ, ∀ i j, (p : KQ p K r) ^ N * A i j ∈ intKQ p K r := by
  choose f hf using exists_pow_mul_mem_intKQ p K r
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2), fun i j => ?_⟩
  have hle : f (A i j) ≤ Finset.univ.sup fun ij : Fin n × Fin n => f (A ij.1 ij.2) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => f (A ij.1 ij.2)) (Finset.mem_univ (i, j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, pow_add, mul_assoc]
  exact mul_mem (natCast_pow_mem_intKQ p K r _) (hf _)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP
variable (p : ℕ) [Fact p.Prime]

theorem norm_p_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

theorem exists_conj_entries_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) {n : ℕ}
    (R : GL (Fin n) (KQ p K r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) K,
      (∀ i j, ‖(((M - 1) i j : K) : PadicAlgCl p)‖ < ε) →
      ∀ i l, (((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) * M.map (inclK p K r) *
        (R : Matrix (Fin n) (Fin n) (KQ p K r))) i l ∈ intKQ p K r := by
  obtain ⟨N₁, h₁⟩ := exists_pow_mul_entries_mem p K r (R : Matrix (Fin n) (Fin n) (KQ p K r))
  obtain ⟨N₂, h₂⟩ := exists_pow_mul_entries_mem p K r ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r))
  refine ⟨‖(p : PadicAlgCl p)‖ ^ (N₁ + N₂), pow_pos (norm_p_pos p) _, fun M hM i l => ?_⟩
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hsplit : M.map (inclK p K r) = 1 + (M - 1).map (inclK p K r) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul]
  refine add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [Matrix.mul_apply]
  refine sum_mem fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun j _ => ?_
  set B := (M - 1) j k with hB
  set b : K := ((p : K) ^ (N₁ + N₂))⁻¹ * B with hb
  have hBb : B = (p : K) ^ (N₁ + N₂) * b := by rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hbint : (b : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff]
    have h := hM j k
    rw [← hB, hBb] at h
    have e : (((p : K) ^ (N₁ + N₂) * b : K) : PadicAlgCl p) = (p : PadicAlgCl p) ^ (N₁ + N₂) * (b : PadicAlgCl p) := by
      simp
    rw [e, norm_mul, norm_pow] at h
    have hpos := pow_pos (norm_p_pos p) (N₁ + N₂)
    by_contra hc
    push_neg at hc
    nlinarith
  have e2 : ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j * ((M - 1).map (inclK p K r)) j k *
      (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l =
      ((p : KQ p K r) ^ N₂ * ((R⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) *
        inclK p K r b * ((p : KQ p K r) ^ N₁ * (R : Matrix (Fin n) (Fin n) (KQ p K r)) k l) := by
    rw [Matrix.map_apply, ← hB, hBb, map_mul, map_pow, map_natCast, pow_add]; ring
  rw [e2]
  exact mul_mem (mul_mem (h₂ i j) (inclK_mem_intKQ p K r b hbint)) (h₁ k l)

end GlobalTheory.TorCls.OpenP

namespace GlobalTheory.TorCls.OpenP

theorem scalar_one_entry {R : Type} [CommRing R] (u : Rˣ) (i j : Fin 1) :
    ((GeneralLinearGroup.scalar (Fin 1) u : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) i j = (u : R) := by
  fin_cases i; fin_cases j; simp [GeneralLinearGroup.scalar]

theorem psiP_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)
    (h1 : ‖(z.2 : ℚ_[p])‖ ≤ 1) (h2 : ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) :
    (psiP G z).1 ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1 := by
  have hfst : (psiP G z).1 = GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom z.2) := rfl
  have hmem : ∀ a : ℚ_[p], ‖a‖ ≤ 1 → algebraMap ℚ_[p] (Qr p 1) a ∈ GlobalTheory.LKLoc.intR p (Q0 p) 1 := by
    intro a ha
    show ((algebraMap ℚ_[p] (Qr p 1) a : Qr p 1) : PadicAlgCl p) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff, IntermediateField.coe_algebraMap_apply, PadicAlgCl.norm_extends]
    exact ha
  refine mem_range_map_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [hfst, scalar_one_entry]; exact hmem _ h1
  · rw [hfst, ← map_inv, scalar_one_entry, ← map_inv]; exact hmem _ h2

theorem openp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1),
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C);
    ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  intro p _ G r₂
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  haveI : IsModuleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) := ⟨rfl⟩
  choose ε hε hM using fun w : Fin G.m => exists_conj_entries_mem p (G.Fw w) 1 (r₂.2 w)
  let e : ∀ (w : Fin G.m) (i j : Fin G.n), ℚ_[p] ⊗[ℚ] G.C → PadicAlgCl p :=
    fun w i j g => (((G.locW w g - 1) i j : G.Fw w) : PadicAlgCl p)
  have hcont : ∀ w i j, Continuous (e w i j) := by
    intro w i j
    let L : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] PadicAlgCl p :=
      (G.Fw w).val.toLinearMap ∘ₗ (Matrix.entryLinearMap ℚ_[p] (G.Fw w) i j) ∘ₗ (G.locW w).toLinearMap
    have he : e w i j = fun g => L g - (((1 : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : G.Fw w) : PadicAlgCl p) := by
      funext g; simp [e, L, Matrix.sub_apply]
    rw [he]
    exact (IsModuleTopology.continuous_of_linearMap L).sub continuous_const
  have hent : ∀ (w : Fin G.m) (z' : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), (∀ i j, ‖e w i j (z'.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w) →
      ∀ i l, (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) i l ∈ intKQ p (G.Fw w) 1 := by
    intro w z' h i l
    have hv : (((r₂⁻¹ * psiP G z' * r₂).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) =
        (((r₂.2 w)⁻¹ : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) *
          (G.locW w (z'.1 : ℚ_[p] ⊗[ℚ] G.C)).map (inclK p (G.Fw w) 1) * ((r₂.2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)) := rfl
    rw [hv]
    exact hM w _ h i l
  refine ⟨{z | ‖(z.2 : ℚ_[p])‖ ≤ 1 ∧ ‖((z.2⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 ∧
      ∀ w i j, ‖e w i j (z.1 : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w ∧ ‖e w i j (((z.1)⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)‖ < ε w},
    ?_, ?_, ?_⟩
  · have hball : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
      have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa [Metric.closedBall, dist_zero_right] using this
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (hball.preimage ((Units.continuous_val (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter
      ((hball.preimage ((Units.continuous_coe_inv (M := ℚ_[p])).comp (continuous_snd (X := (ℚ_[p] ⊗[ℚ] G.C)ˣ) (Y := ℚ_[p]ˣ)))).inter ?_)
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_val (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp ((hcont w i j).comp ((Units.continuous_coe_inv (M := ℚ_[p] ⊗[ℚ] G.C)).comp continuous_fst)))
      continuous_const)
  · refine ⟨by simp, by simp, fun w i j => ⟨?_, ?_⟩⟩ <;> simp [e, hε w]
  · rintro z ⟨h1, h2, h3⟩
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · have hk := psiP_fst_mem p G z h1 h2
      have := (normal_of_gl_one (GlobalTheory.LKLoc.Kint p (Q0 p) 1 1)).conj_mem _ hk r₂.1⁻¹
      simpa using this
    · refine (Subgroup.mem_pi _).2 fun w _ => ?_
      refine mem_range_map_of_entries _ _ (hent w z fun i j => (h3 w i j).1) ?_
      have hinv : ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = (r₂⁻¹ * psiP G z⁻¹ * r₂).2 w := by
        have hg : (r₂⁻¹ * psiP G z * r₂)⁻¹ = r₂⁻¹ * psiP G z⁻¹ * r₂ := by rw [map_inv]; group
        rw [show ((r₂⁻¹ * psiP G z * r₂).2 w)⁻¹ = ((r₂⁻¹ * psiP G z * r₂)⁻¹).2 w from rfl, hg]
      rw [hinv]
      exact hent w z⁻¹ fun i j => (h3 w i j).2

end GlobalTheory.TorCls.OpenP
