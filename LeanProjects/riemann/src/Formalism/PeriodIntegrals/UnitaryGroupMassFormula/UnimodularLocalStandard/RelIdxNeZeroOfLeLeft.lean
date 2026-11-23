import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Development

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Idx
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def smulHom (w : ℂ) : V →+ V := DistribMulAction.toAddMonoidHom V w

@[simp] lemma smulHom_apply (w : ℂ) (v : V) : smulHom w v = w • v := rfl

lemma smulHom_inj {w : ℂ} (hw : w ≠ 0) : Function.Injective (smulHom (V := V) w) := by
  intro x y hxy
  simp only [smulHom_apply] at hxy
  have h := congrArg (fun v => w⁻¹ • v) hxy
  simpa [smul_smul, inv_mul_cancel₀ hw] using h

private theorem relIndex_ne_zero_of_finite_cover {A B : AddSubgroup V} {ι : Type*} [Finite ι] (φ : ι → V)
    (hφ : ∀ i, φ i ∈ B) (hcov : ∀ b ∈ B, ∃ i, b - φ i ∈ A) : A.relIndex B ≠ 0 := by
  have hsurj : Function.Surjective (fun i => ((⟨φ i, hφ i⟩ : B) : B ⧸ A.addSubgroupOf B)) := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨i, hi⟩ := hcov b b.2
    refine ⟨i, ?_⟩
    show ((⟨φ i, hφ i⟩ : B) : B ⧸ A.addSubgroupOf B) = (b : B ⧸ A.addSubgroupOf B)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hi
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Finite.of_surjective _ hsurj
  exact AddSubgroup.index_ne_zero_of_finite

lemma relIdx_ne_zero_of_le_left {A A' B : AddSubgroup V} (h : A ≤ A') (hA : A.relIndex B ≠ 0) :
    A'.relIndex B ≠ 0 := by
  haveI : Finite (B ⧸ A.addSubgroupOf B) :=
    Nat.finite_of_card_ne_zero (α := B ⧸ A.addSubgroupOf B) hA
  refine relIndex_ne_zero_of_finite_cover (ι := B ⧸ A.addSubgroupOf B) (fun q => ((q.out : B) : V))
    (fun q => q.out.2) ?_
  intro b hb
  refine ⟨((⟨b, hb⟩ : B) : B ⧸ A.addSubgroupOf B), h ?_⟩
  have e : -((((⟨b, hb⟩ : B) : B ⧸ A.addSubgroupOf B)).out) + (⟨b, hb⟩ : B) ∈ A.addSubgroupOf B := by
    rw [← QuotientAddGroup.eq]
    exact QuotientAddGroup.out_eq' _
  rw [AddSubgroup.mem_addSubgroupOf] at e
  simpa [neg_add_eq_sub] using e

lemma relIdx_map_smul {w : ℂ} (hw : w ≠ 0) (A B : AddSubgroup V) :
    (A.map (smulHom w)).relIndex (B.map (smulHom w)) = A.relIndex B := by
  exact AddSubgroup.relIndex_map_map_of_injective A B (smulHom_inj hw)

lemma not_dvd_relIndex {A B : AddSubgroup V} {l n : ℕ} (hl : l.Prime) (hAB : A.relIndex B ≠ 0)
    (hn : ∀ y ∈ B, n • y ∈ A) (hln : ¬ l ∣ n) : ¬ l ∣ A.relIndex B := by
  intro hdvd
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : Finite (B ⧸ A.addSubgroupOf B) :=
    Nat.finite_of_card_ne_zero (α := B ⧸ A.addSubgroupOf B) hAB
  have hcard : l ∣ Nat.card (B ⧸ A.addSubgroupOf B) := hdvd
  obtain ⟨q, hq⟩ : ∃ q : B ⧸ A.addSubgroupOf B, addOrderOf q = l := by
    exact exists_prime_addOrderOf_dvd_card' l hcard
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply hln
  rw [← hq]
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hn _ y.2

lemma relIdx_ne_zero_of_cover {A B : AddSubgroup V} {ι : Type*} [Finite ι] (φ : ι → V)
    (hφ : ∀ i, φ i ∈ B) (hcov : ∀ b ∈ B, ∃ i, b - φ i ∈ A) : A.relIndex B ≠ 0 :=
  relIndex_ne_zero_of_finite_cover φ hφ hcov

private theorem relIndex_ne_zero_of_le {A B : AddSubgroup V} (h : B ≤ A) : A.relIndex B ≠ 0 :=
  relIndex_ne_zero_of_finite_cover (ι := Unit) (fun _ => 0) (fun _ => B.zero_mem)
    (fun b hb => ⟨(), by simpa using h hb⟩)

private theorem relIndex_ne_zero_trans' {A B C : AddSubgroup V} (h : A.relIndex B ≠ 0)
    (h' : B.relIndex C ≠ 0) : A.relIndex C ≠ 0 := by
  exact AddSubgroup.relIndex_ne_zero_trans h h'

lemma comm_smul {S X : AddSubgroup V} {w : ℂ} (hw : w ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hS : (S.map (smulHom (N : ℂ))).relIndex S ≠ 0) (h1 : S.relIndex X ≠ 0) (h2 : X.relIndex S ≠ 0)
    (ha : ∀ x ∈ X, (N : ℂ) • w • x ∈ X) (hb : ∀ x ∈ X, (N : ℂ) • w⁻¹ • x ∈ X) :
    S.relIndex (X.map (smulHom w)) ≠ 0 ∧ (X.map (smulHom w)).relIndex S ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNXS : (X.map (smulHom (N : ℂ))).relIndex (S.map (smulHom (N : ℂ))) ≠ 0 := by
    rw [relIdx_map_smul hN']; exact h2
  have t1 : (X.map (smulHom (N : ℂ))).relIndex X ≠ 0 :=
    relIndex_ne_zero_trans' (relIndex_ne_zero_trans' hNXS hS) h1
  have hcomm : (X.map (smulHom w)).map (smulHom (N : ℂ)) =
      (X.map (smulHom (N : ℂ))).map (smulHom w) := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext v
    simp only [AddMonoidHom.comp_apply, smulHom_apply, smul_smul, mul_comm]
  have t2 : ((X.map (smulHom w)).map (smulHom (N : ℂ))).relIndex
      (X.map (smulHom w)) ≠ 0 := by
    rw [hcomm, relIdx_map_smul hw]; exact t1
  have t3 : X.relIndex ((X.map (smulHom w)).map (smulHom (N : ℂ))) ≠ 0 := by
    refine relIndex_ne_zero_of_le ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using ha x hx
  have t4 : (X.map (smulHom w)).relIndex (X.map (smulHom (N : ℂ))) ≠ 0 := by
    refine relIndex_ne_zero_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(N : ℂ) • w⁻¹ • x, hb x hx, ?_⟩
    rw [smulHom_apply, smulHom_apply, smul_smul, smul_smul]
    congr 1
    rw [mul_comm w, mul_assoc, mul_inv_cancel₀ hw, mul_one]
  exact ⟨relIndex_ne_zero_trans' (relIndex_ne_zero_trans' h1 t3) t2,
    relIndex_ne_zero_trans' t4 (relIndex_ne_zero_trans' hNXS hS)⟩

end Idx

private theorem mem_lattice_iff_exists_int_comb (L : PeriodPair) (z : ℂ) :
    z ∈ L.lattice ↔ ∃ p q : ℤ, (p : ℂ) * L.ω₁ + (q : ℂ) * L.ω₂ = z := by
  exact PeriodPair.mem_lattice

lemma stdLat_smul_idx (L : PeriodPair) (m : Type*) [Fintype m] {N : ℕ} (hN : N ≠ 0) :
    ((stdLat L m).map (smulHom (N : ℂ))).relIndex (stdLat L m) ≠ 0 := by
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hN1 : (N : ℤ) ≠ 0 := hN0.ne'
  refine relIdx_ne_zero_of_cover (ι := m → (Set.Ico (0 : ℤ) N × Set.Ico (0 : ℤ) N))
    (fun f j => (((f j).1 : ℤ) : ℂ) * L.ω₁ + (((f j).2 : ℤ) : ℂ) * L.ω₂) ?_ ?_
  · intro f
    simp only [PI.ULS.stdLat, AddSubgroup.mem_pi]
    intro j _
    exact (mem_lattice_iff_exists_int_comb L _).mpr ⟨_, _, rfl⟩
  · intro b hb
    simp only [PI.ULS.stdLat, AddSubgroup.mem_pi] at hb
    have hb' : ∀ j, ∃ p q : ℤ, (p : ℂ) * L.ω₁ + (q : ℂ) * L.ω₂ = b j :=
      fun j => (mem_lattice_iff_exists_int_comb L (b j)).mp (hb j (Set.mem_univ _))
    choose p q hpq using hb'
    refine ⟨fun j => (⟨p j % N, Set.mem_Ico.mpr ⟨Int.emod_nonneg _ hN1, Int.emod_lt_of_pos _ hN0⟩⟩,
      ⟨q j % N, Set.mem_Ico.mpr ⟨Int.emod_nonneg _ hN1, Int.emod_lt_of_pos _ hN0⟩⟩), ?_⟩
    refine ⟨fun j => ((p j / N : ℤ) : ℂ) * L.ω₁ + ((q j / N : ℤ) : ℂ) * L.ω₂, ?_, ?_⟩
    · simp only [PI.ULS.stdLat, AddSubgroup.mem_pi]
      intro j _
      exact (mem_lattice_iff_exists_int_comb L _).mpr ⟨_, _, rfl⟩
    · funext j
      simp only [smulHom_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← hpq j]
      have d1 : (N : ℤ) * (p j / N) + p j % N = p j := by
        first
        | exact Int.ediv_add_emod _ _
        | exact EuclideanDomain.div_add_mod _ _
        | exact Int.mul_ediv_add_emod _ _
        | (rw [add_comm]; exact Int.emod_add_ediv _ _)
        | (rw [Int.emod_def]; ring)
        | (have e := Int.emod_def (p j) (N : ℤ); linarith)
      have d2 : (N : ℤ) * (q j / N) + q j % N = q j := by
        first
        | exact Int.ediv_add_emod _ _
        | exact EuclideanDomain.div_add_mod _ _
        | exact Int.mul_ediv_add_emod _ _
        | (rw [add_comm]; exact Int.emod_add_ediv _ _)
        | (rw [Int.emod_def]; ring)
        | (have e := Int.emod_def (q j) (N : ℤ); linarith)
      have c1 : (N : ℂ) * ((p j / N : ℤ) : ℂ) + ((p j % N : ℤ) : ℂ) = (p j : ℂ) := by
        exact_mod_cast d1
      have c2 : (N : ℂ) * ((q j / N : ℤ) : ℂ) + ((q j % N : ℤ) : ℂ) = (q j : ℂ) := by
        exact_mod_cast d2
      try dsimp only
      linear_combination L.ω₁ * c1 + L.ω₂ * c2

section Theta
variable {a : ℕ} {b c : ℤ} {d : ℕ}

lemma theta_conj (b : ℤ) (d : ℕ) : conj (cmTheta b d) = b - cmTheta b d := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  first
  | (simp only [PI.ULS.cmTheta, map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, h2]; ring)
  | (simp [PI.ULS.cmTheta, map_div₀]; ring)
  | (simp [PI.ULS.cmTheta, map_div₀]; done)
  | (apply Complex.ext <;> simp [PI.ULS.cmTheta] <;> ring)

lemma theta_norm (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hc : (4 : ℂ) * a * c = (b : ℂ) ^ 2 + d := by exact_mod_cast h
  simp only [PI.ULS.cmTheta]
  linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs
    + (-1 / 4 : ℂ) * hc

lemma two_theta_sub (b : ℤ) {d : ℕ} (hd : 0 < d) : 2 * cmTheta b d - b ≠ 0 := by
  have e : 2 * PI.ULS.cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    simp only [PI.ULS.cmTheta]; ring
  rw [e]
  exact mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne')

end Theta

end PI.UnitaryGroupMassFormula.UnimodLocStd
