import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

namespace UpperTheory.V.Z.Sym.Glob

private theorem index_range_mulLeft_eq_natAbs_det_and_det_ne_zero {B : Type} [Ring B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (hx : Function.Injective (fun z : B => x * z)) :
    (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup.index =
      (LinearMap.det (LinearMap.mulLeft ℤ x)).natAbs ∧ LinearMap.det (LinearMap.mulLeft ℤ x) ≠ 0 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ x) := hx
  refine ⟨?_, ?_⟩
  · let e := LinearEquiv.ofInjective (LinearMap.mulLeft ℤ x) hinj
    have h := Submodule.natAbs_det_equiv (LinearMap.range (LinearMap.mulLeft ℤ x)) e
    calc (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup.index
        = Nat.card (B ⧸ LinearMap.range (LinearMap.mulLeft ℤ x)) := rfl
      _ = _ := h.symm
      _ = _ := by
        congr 2
  · rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hinj

private theorem exists_natAbs_det_mulLeft_sum_le_mul_pow_card {B : Type} [Ring B] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ B) :
    ∃ C : ℕ, ∀ (c : ι → ℤ) (m : ℕ), (∀ i, |c i| ≤ m) →
      (LinearMap.det (LinearMap.mulLeft ℤ (∑ i, c i • b i))).natAbs ≤ C * m ^ Fintype.card ι := by
  set K0 : ℤ := ∑ t, ∑ l, ∑ i, |b.repr (b t * b l) i| with hK0
  have hK0n : 0 ≤ K0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι, fun c m hc => ?_⟩
  rw [← LinearMap.det_toMatrix b]
  have hent : ∀ i l, |LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t)) i l| ≤ (m : ℤ) * K0 := by
    intro i l
    rw [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    calc |∑ t, c t * b.repr (b t * b l) i| ≤ ∑ t, |c t * b.repr (b t * b l) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, (m : ℤ) * |b.repr (b t * b l) i| := by
          apply Finset.sum_le_sum
          intro t _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hc t) (abs_nonneg _)
      _ = (m : ℤ) * ∑ t, |b.repr (b t * b l) i| := by rw [Finset.mul_sum]
      _ ≤ (m : ℤ) * K0 := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
          apply Finset.sum_le_sum
          intro t _
          calc |b.repr (b t * b l) i| ≤ ∑ i', |b.repr (b t * b l) i'| :=
                Finset.single_le_sum (f := fun i' => |b.repr (b t * b l) i'|)
                  (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            _ ≤ ∑ l', ∑ i', |b.repr (b t * b l') i'| :=
                Finset.single_le_sum (f := fun l' => ∑ i', |b.repr (b t * b l') i'|)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (x := (m : ℤ) * K0) (fun i l => hent i l)
  have key : (((LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t))).det.natAbs : ℕ) : ℤ) ≤
      (((Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι * m ^ Fintype.card ι : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    rw [abs_of_nonneg hK0n]
    calc |(LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t))).det|
        ≤ (Fintype.card ι).factorial • ((m : ℤ) * K0) ^ Fintype.card ι := hdet
      _ = _ := by rw [nsmul_eq_mul, mul_pow]; ring
  exact_mod_cast key

private theorem exists_nat_mul_mem_principal_of_rightIdeal_index_ne_zero {B : Type} [Ring B] [Nontrivial B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (hinj : ∀ x : B, x ≠ 0 → Function.Injective (fun z : B => x * z)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ I : AddSubgroup B, (∀ y ∈ I, ∀ z : B, y * z ∈ I) → I.index ≠ 0 →
      ∃ x ∈ I, x ≠ 0 ∧ ∀ y ∈ I, ∃ z : B, (N : B) * y = x * z := by
  classical
  let b := Module.Free.chooseBasis ℤ B
  obtain ⟨C, hC⟩ := exists_natAbs_det_mulLeft_sum_le_mul_pow_card b
  refine ⟨C.factorial, Nat.factorial_ne_zero C, fun I hI hD => ?_⟩
  have hk : 0 < Fintype.card (Module.Free.ChooseBasisIndex ℤ B) := by
    have := Module.finrank_pos (R := ℤ) (M := B)
    rwa [Module.finrank_eq_card_chooseBasisIndex] at this
  set k := Fintype.card (Module.Free.ChooseBasisIndex ℤ B) with hkdef
  set D := I.index with hDdef
  set m := Nat.findGreatest (fun m => m ^ k ≤ D) D with hmdef
  have hm1 : m ^ k ≤ D := Nat.findGreatest_spec (P := fun m => m ^ k ≤ D) (Nat.zero_le D)
    (by rw [zero_pow hk.ne']; exact Nat.zero_le _)
  have hm2 : D < (m + 1) ^ k := by
    by_contra hcon
    push_neg at hcon
    have hle : m + 1 ≤ D := le_trans (Nat.le_self_pow hk.ne' _) hcon
    exact Nat.findGreatest_is_greatest (P := fun m => m ^ k ≤ D) (Nat.lt_succ_self m) hle hcon
  haveI : I.FiniteIndex := ⟨hD⟩
  haveI : Finite (B ⧸ I) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (B ⧸ I)
  let f : (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1)) → B ⧸ I :=
    fun c => QuotientAddGroup.mk (∑ i, ((c i : ℕ) : ℤ) • b i)
  have hcard : Fintype.card (B ⧸ I) < Fintype.card (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hm2
  obtain ⟨c, c', hne, hcc⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  let d : Module.Free.ChooseBasisIndex ℤ B → ℤ := fun i => ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)
  have hxeq : ∑ i, d i • b i = (∑ i, ((c i : ℕ) : ℤ) • b i) - ∑ i, ((c' i : ℕ) : ℤ) • b i := by
    simp only [d, sub_smul, Finset.sum_sub_distrib]
  have hxI : ∑ i, d i • b i ∈ I := by
    have h0 := (QuotientAddGroup.eq (s := I)).1 hcc
    rw [hxeq]
    have h1 := I.neg_mem h0
    simpa [sub_eq_add_neg, add_comm] using h1
  have hx0 : ∑ i, d i • b i ≠ 0 := by
    intro h0
    apply hne
    funext i
    have h1 := congrArg (fun v => b.repr v i) h0
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, d] at h1
    exact Fin.ext (by omega)
  have hdb : ∀ i, |d i| ≤ (m : ℤ) := by
    intro i
    have h1 : (c i : ℕ) ≤ m := Nat.lt_succ_iff.1 (c i).isLt
    have h2 : (c' i : ℕ) ≤ m := Nat.lt_succ_iff.1 (c' i).isLt
    rw [abs_le]
    constructor <;> simp only [d] <;> omega
  obtain ⟨hidx, hdet0⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero _ (hinj _ hx0)
  set x := ∑ i, d i • b i with hx
  set X := (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup with hXdef
  have hXI : X ≤ I := by
    rintro _ ⟨z, rfl⟩
    exact hI x hxI z
  have hrel := AddSubgroup.relIndex_mul_index hXI
  have hbound : X.index ≤ C * D := by
    rw [hidx]
    exact le_trans (hC d m hdb) (Nat.mul_le_mul_left C hm1)
  have hX0 : X.index ≠ 0 := by
    rw [hidx]
    exact Int.natAbs_ne_zero.2 hdet0
  have hr0 : X.relIndex I ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact hX0 hrel.symm
  have hrC : X.relIndex I ≤ C := by
    have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    rw [← hrel] at hbound
    exact Nat.le_of_mul_le_mul_right hbound hDpos
  refine ⟨x, hxI, hx0, fun y hy => ?_⟩
  have hmem := AddSubgroup.nsmul_index_mem (X.addSubgroupOf I) ⟨y, hy⟩
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have hmem' : X.relIndex I • y ∈ X := hmem
  obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hr0) hrC
  have hCy : (C.factorial : B) * y ∈ X := by
    rw [← nsmul_eq_mul, hq, mul_comm, ← smul_smul]
    exact X.nsmul_mem hmem' q
  obtain ⟨z, hz⟩ := hCy
  exact ⟨z, hz.symm⟩

theorem cls_abs {A M Γ G : Type} [Ring A] [CharZero A] [Ring M] [Group Γ] [Group G] (j : A →+* M) (R : Subring M)
    [Module.Finite ℤ (R.comap j)] (ι : Γ →* G) (σ : Γ →* A) (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (σ γ)) (U : Subgroup G)
    (hU : ∀ g, ρ g ∈ R → ρ g⁻¹ ∈ R → g ∈ U) (hσ : ∀ y ∈ R.comap j, y ≠ 0 → ∃ γ, σ γ = y)
    (hap : ∀ m ∈ R, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ R.comap j, ∃ r ∈ R, m = j x + (n : M) * r)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) :
    ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U, g = ι γ * s * u := by
  classical
  have hunit : ∀ γ, σ γ * σ γ⁻¹ = 1 ∧ σ γ⁻¹ * σ γ = 1 := fun γ =>
    ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hjunit : ∀ γ, j (σ γ) * j (σ γ⁻¹) = 1 ∧ j (σ γ⁻¹) * j (σ γ) = 1 := fun γ =>
    ⟨by rw [← map_mul, (hunit γ).1, map_one], by rw [← map_mul, (hunit γ).2, map_one]⟩
  have hρinv : ∀ g, ρ g * ρ g⁻¹ = 1 ∧ ρ g⁻¹ * ρ g = 1 := fun g =>
    ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hinjA : ∀ y : A, y ∈ R.comap j → y ≠ 0 → ∀ z z' : A, y * z = y * z' → z = z' := by
    intro y hy hy0 z z' h
    obtain ⟨γ, rfl⟩ := hσ y hy hy0
    calc z = σ γ⁻¹ * (σ γ * z) := by rw [← mul_assoc, (hunit γ).2, one_mul]
      _ = z' := by rw [h, ← mul_assoc, (hunit γ).2, one_mul]
  haveI : NoZeroSMulDivisors ℤ (R.comap j) := ⟨fun {c x} h => by
    by_contra hc
    push_neg at hc
    obtain ⟨hc0, hx0⟩ := hc
    have hx0' : (x : A) ≠ 0 := fun h' => hx0 (Subtype.ext h')
    have h1 : (c : A) * (x : A) = 0 := by
      have h2 := congrArg Subtype.val h
      simpa [zsmul_eq_mul] using h2
    obtain ⟨γ, hγ⟩ := hσ x x.2 hx0'
    have h3 : (c : A) = 0 := by
      calc (c : A) = (c : A) * (σ γ * σ γ⁻¹) := by rw [(hunit γ).1, mul_one]
        _ = 0 := by rw [← mul_assoc, hγ, h1, zero_mul]
    exact hc0 (Int.cast_eq_zero.1 h3)⟩
  haveI : Module.Free ℤ (R.comap j) := Module.free_of_finite_type_torsion_free'
  haveI : Nontrivial (R.comap j) := inferInstance
  obtain ⟨N, hN0, hNA⟩ := exists_nat_mul_mem_principal_of_rightIdeal_index_ne_zero (B := R.comap j) (fun x hx z z' h =>
    Subtype.ext (hinjA _ x.2 (fun h' => hx (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
  let good : G → Prop := fun k => ρ k⁻¹ ∈ R ∧ (N : M) * ρ k ∈ R
  have hstep : ∀ g, ∃ γ k, good k ∧ g = ι γ * k := by
    intro g
    obtain ⟨n, hn0, hnR⟩ := hden g
    have hnB : (n : A) ∈ R.comap j := by
      show j (n : A) ∈ R
      rw [map_natCast]
      exact natCast_mem R n
    obtain ⟨γ1, hγ1⟩ := hσ (n : A) hnB (Nat.cast_ne_zero.2 hn0)
    have ha : ρ (ι γ1 * g) ∈ R := by
      rw [map_mul, hι, hγ1, map_natCast]
      exact hnR
    obtain ⟨n', hn'0, hn'R⟩ := hden (ι γ1 * g)⁻¹
    set a := ρ (ι γ1 * g)
    set a' := ρ (ι γ1 * g)⁻¹
    have haa' : a * a' = 1 := (hρinv _).1
    have ha'a : a' * a = 1 := (hρinv _).2
    have hn'R2 : a' * (n' : M) ∈ R := by
      rw [← Nat.cast_comm]
      exact hn'R
    let I : AddSubgroup (R.comap j) :=
      { carrier := {y | ∃ r ∈ R, j (y : A) = a * r}
        add_mem' := by
          rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
          exact ⟨r + s, R.add_mem hr hs, by simp only [Subring.coe_add, map_add, hx, hy, mul_add]⟩
        zero_mem' := ⟨0, R.zero_mem, by simp⟩
        neg_mem' := by
          rintro x ⟨r, hr, hx⟩
          exact ⟨-r, R.neg_mem hr, by simp only [Subring.coe_neg, map_neg, hx, mul_neg]⟩ }
    have hIr : ∀ y ∈ I, ∀ z : R.comap j, y * z ∈ I := by
      rintro y ⟨r, hr, hy⟩ z
      exact ⟨r * j (z : A), R.mul_mem hr z.2, by simp only [Subring.coe_mul, map_mul, hy, mul_assoc]⟩
    have hn'I : ((n' : R.comap j)) ∈ I :=
      ⟨a' * n', hn'R2, by simp only [Subring.coe_natCast, map_natCast]; rw [← mul_assoc, haa', one_mul]⟩
    have hn'0B : ((n' : R.comap j)) ≠ 0 := by
      intro h
      apply hn'0
      have h2 := congrArg Subtype.val h
      simpa using h2
    obtain ⟨hidx, hdet⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (n' : R.comap j) (fun z z' h =>
      Subtype.ext (hinjA _ (n' : R.comap j).2 (fun h' => hn'0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
    have hle : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup ≤ I := by
      rintro _ ⟨z, rfl⟩
      exact hIr _ hn'I z
    haveI : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup.FiniteIndex :=
      ⟨by rw [hidx]; exact Int.natAbs_ne_zero.2 hdet⟩
    have hIidx : I.index ≠ 0 := (AddSubgroup.finiteIndex_of_le hle).index_ne_zero
    obtain ⟨x, ⟨r0, hr0R, hr0⟩, hx0, hxdiv⟩ := hNA I hIr hIidx
    have hx0' : (x : A) ≠ 0 := fun h' => hx0 (Subtype.ext h')
    obtain ⟨γx, hγx⟩ := hσ x x.2 hx0'
    obtain ⟨y, hyB, r, hr, hay⟩ := hap a ha n' hn'0
    have hyI : (⟨y, hyB⟩ : R.comap j) ∈ I := by
      refine ⟨1 - a' * n' * r, R.sub_mem R.one_mem (R.mul_mem hn'R2 hr), ?_⟩
      show j y = a * (1 - a' * n' * r)
      rw [mul_sub, mul_one, ← mul_assoc, ← mul_assoc, haa', one_mul, hay]
      abel
    obtain ⟨z, hz⟩ := hxdiv _ hyI
    obtain ⟨z', hz'⟩ := hxdiv _ hn'I
    have hz1 : (N : M) * j y = j (σ γx) * j (z : A) := by
      have h2 := congrArg (fun w : R.comap j => j (w : A)) hz
      simp only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2
      rw [hγx]
      exact h2
    have hz2 : (N : M) * (n' : M) = j (σ γx) * j (z' : A) := by
      have h2 := congrArg (fun w : R.comap j => j (w : A)) hz'
      simp only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2
      rw [hγx]
      exact h2
    refine ⟨γ1⁻¹ * γx, ι γx⁻¹ * (ι γ1 * g), ⟨?_, ?_⟩, ?_⟩
    · rw [mul_inv_rev, map_inv ι, inv_inv, map_mul, hι, hγx, hr0, ← mul_assoc, ha'a, one_mul]
      exact hr0R
    · rw [map_mul, hι]
      have h3 : (N : M) * (j (σ γx⁻¹) * a) = j (z : A) + j (z' : A) * r := by
        calc (N : M) * (j (σ γx⁻¹) * a) = j (σ γx⁻¹) * ((N : M) * a) := by
              rw [← mul_assoc, Nat.cast_comm, mul_assoc]
          _ = j (σ γx⁻¹) * (j (σ γx) * (j (z : A) + j (z' : A) * r)) := by
              congr 1
              rw [hay, mul_add, hz1, ← mul_assoc (N : M) (n' : M) r, hz2, mul_add, mul_assoc]
          _ = _ := by rw [← mul_assoc, (hjunit γx).2, one_mul]
      rw [h3]
      exact R.add_mem z.2 (R.mul_mem z'.2 hr)
    · rw [map_mul, map_inv, map_inv]
      group
  have hN0B : ((N : R.comap j)) ≠ 0 := by
    intro h
    apply hN0
    have h2 := congrArg Subtype.val h
    simpa using h2
  obtain ⟨hKidx, hKdet⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (N : R.comap j) (fun z z' h =>
    Subtype.ext (hinjA _ (N : R.comap j).2 (fun h' => hN0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
  set K := (LinearMap.range (LinearMap.mulLeft ℤ (N : R.comap j))).toAddSubgroup with hKd
  haveI : K.FiniteIndex := ⟨by rw [hKidx]; exact Int.natAbs_ne_zero.2 hKdet⟩
  haveI : Finite (R.comap j ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let φ : G → Set (R.comap j ⧸ K) := fun k =>
    (QuotientAddGroup.mk : R.comap j → R.comap j ⧸ K) '' {y | ∃ r ∈ R, j (y : A) = r * ρ k⁻¹}
  have hsub : ∀ s k, good s → good k → φ s ⊆ φ k → ρ (s⁻¹ * k) ∈ R := by
    rintro s k ⟨hs1, hs2⟩ ⟨hk1, hk2⟩ hφ
    obtain ⟨y, hyB, r, hr, hcy⟩ := hap (ρ s⁻¹) hs1 N hN0
    have hyJ : (⟨y, hyB⟩ : R.comap j) ∈ {y : R.comap j | ∃ r ∈ R, j (y : A) = r * ρ s⁻¹} := by
      refine ⟨1 - r * ((N : M) * ρ s), R.sub_mem R.one_mem (R.mul_mem hr hs2), ?_⟩
      show j y = (1 - r * ((N : M) * ρ s)) * ρ s⁻¹
      rw [sub_mul, one_mul, mul_assoc, mul_assoc, (hρinv s).1, mul_one, hcy, Nat.cast_comm]
      abel
    obtain ⟨y', ⟨r', hr', hy'⟩, hyy'⟩ := hφ ⟨_, hyJ, rfl⟩
    obtain ⟨w, hw⟩ := (QuotientAddGroup.eq (s := K)).1 hyy'
    have hw' : j y = j (y' : A) + (N : M) * j (w : A) := by
      have h2 := congrArg (fun v : R.comap j => j (v : A)) hw
      simp only [LinearMap.mulLeft_apply, Subring.coe_mul, Subring.coe_natCast, Subring.coe_add,
        Subring.coe_neg, map_mul, map_natCast, map_add, map_neg] at h2
      rw [h2]
      abel
    have e1 : j (w : A) * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * j (w : A) := by
      rw [mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]
    have e2 : r * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * r := by
      rw [mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]
    have key : ρ s⁻¹ = (r' + j (w : A) * ((N : M) * ρ k) + r * ((N : M) * ρ k)) * ρ k⁻¹ := by
      rw [add_mul, add_mul, e1, e2, ← hy', ← hw', hcy]
    rw [map_mul, key, mul_assoc, (hρinv k).2, mul_one]
    exact R.add_mem (R.add_mem hr' (R.mul_mem w.2 hk2)) (R.mul_mem hr hk2)
  have hfin : (φ '' {k | good k}).Finite := Set.toFinite _
  refine ⟨hfin.toFinset.image (fun v => if h : ∃ k, good k ∧ φ k = v then Classical.choose h else 1),
    fun g => ?_⟩
  obtain ⟨γ, k, hk, rfl⟩ := hstep g
  have hex : ∃ k', good k' ∧ φ k' = φ k := ⟨k, hk, rfl⟩
  have hs := Classical.choose_spec hex
  refine ⟨γ, Classical.choose hex, ?_, (Classical.choose hex)⁻¹ * k, ?_, by group⟩
  · rw [Finset.mem_image]
    refine ⟨φ k, hfin.mem_toFinset.2 ⟨k, hk, rfl⟩, ?_⟩
    rw [dif_pos hex]
  · apply hU
    · exact hsub _ k hs.1 hk hs.2.le
    · rw [mul_inv_rev, inv_inv]
      exact hsub k _ hk hs.1 hs.2.ge

theorem cls_of_relIndex {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (U U' : Subgroup G) (h : U'.relIndex U ≠ 0)
    (hS : ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U, g = ι γ * s * u) :
    ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * u := by
  classical
  obtain ⟨S, hS⟩ := hS
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨h⟩
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (U ⧸ U'.subgroupOf U)
  refine ⟨(S ×ˢ (Finset.univ.image (fun q : U ⧸ U'.subgroupOf U => ((Quotient.out q : U) : G)))).image
    (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨u, hu⟩ : U)
  refine ⟨γ, s * ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ U'.subgroupOf U) : U) : G), ?_,
    ((k : U) : G)⁻¹, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨(s, _), Finset.mem_product.2 ⟨hs, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  · exact U'.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
  · rw [hk]
    simp [mul_assoc]

theorem box_relIndex {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U U' : ∀ v, Subgroup (Gv v)) (S : Finset I) (h1 : ∀ v ∈ S, (U' v).relIndex (U v) ≠ 0) (h2 : ∀ v ∉ S, U v ≤ U' v) :
    (P.box U').relIndex (P.box U) ≠ 0 := by
  classical
  have hC : (⨅ v : S, Subgroup.comap (P.p v) (U' v)).relIndex (P.box U) ≠ 0 := by
    refine Subgroup.relIndex_iInf_ne_zero (fun v => ?_)
    rw [Subgroup.relIndex_comap]
    have hle : Subgroup.map (P.p v) (P.box U) ≤ U v := by
      rw [Subgroup.map_le_iff_le_comap]
      exact iInf_le (fun w => Subgroup.comap (P.p w) (U w)) (v : I)
    refine Subgroup.relIndex_ne_zero_trans (h1 v v.2) ?_
    rw [Subgroup.relIndex_eq_one.mpr hle]
    exact one_ne_zero
  have hX : (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U ≤ P.box U' := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hx1 hx2 ⊢
    intro v
    by_cases hv : v ∈ S
    · exact hx1 ⟨v, hv⟩
    · exact h2 v hv (hx2 v)
  refine Subgroup.relIndex_ne_zero_trans (K := (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U) ?_ ?_
  · rw [Subgroup.relIndex_eq_one.mpr hX]
    exact one_ne_zero
  · refine Subgroup.relIndex_inf_ne_zero hC ?_
    rw [Subgroup.relIndex_eq_one.mpr le_rfl]
    exact one_ne_zero

end UpperTheory.V.Z.Sym.Glob
