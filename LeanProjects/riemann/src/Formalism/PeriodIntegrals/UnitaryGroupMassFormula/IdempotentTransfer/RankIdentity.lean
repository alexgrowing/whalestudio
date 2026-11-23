import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.ESMulESOfNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegGeOfInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.FgOfLeL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFiniteOrder

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Alg2

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma eS_mul_eG (T : GoodSet K G) (s : T.S) : eS T s * eG T = eS T s := by
  classical
  rw [eG, Finset.mul_sum, Finset.sum_eq_single s]
  · exact eS_idem T s
  · intro t _ ht; exact eS_orth T s t (Ne.symm ht)
  · simp

lemma eG_mul_eS (T : GoodSet K G) (s : T.S) : eG T * eS T s = eS T s := by
  rw [← eG_comm, eS_mul_eG]

lemma card_S_le (T : GoodSet K G) : Fintype.card T.S ≤ Fintype.card G := by
  classical
  set U := Submodule.span K (Set.range (MonoidAlgebra.of K G)) with hU
  have hmem : ∀ s, eS T s ∈ U := fun s =>
    U.sum_mem fun y _ => U.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)
  let v : T.S → U := fun s => ⟨eS T s, hmem s⟩
  have hli : LinearIndependent K (fun s => eS T s) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 := congrArg (fun x => x * eS T t) hc
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h1
    rw [Finset.sum_eq_single t] at h1
    · rw [eS_idem] at h1
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (eS_ne_zero T t)
    · intro s _ hs; rw [eS_orth T s t hs, smul_zero]
    · simp
  have hv : LinearIndependent K v := LinearIndependent.of_comp U.subtype hli
  have h1 := hv.fintype_card_le_finrank
  have h2 : finrank K U ≤ Fintype.card G := finrank_range_le_card _
  omega

lemma dim_sq_le (T : GoodSet K G) (s : T.S) :
    finrank K (T.W s) * finrank K (T.W s) ≤ Fintype.card G := by
  have hall : ∀ a : MonoidAlgebra K G,
      (T.tau s).asAlgebraHom a ∈ Submodule.span K (Set.range (T.tau s)) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span K (Set.range (T.tau s)) = ⊤ := by
    rw [eq_top_iff]
    intro X _
    obtain ⟨a, rfl⟩ := T.irr s X
    exact hall a
  have h1 := finrank_range_le_card (R := K) (T.tau s : G → Module.End K (T.W s))
  rw [Set.finrank, htop, finrank_top, Module.finrank_linearMap] at h1
  exact h1

theorem finrank_range_eps_mul_eS_eq_nS_mul (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) (s : T.S) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))) =
      nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by
  obtain ⟨c, hc⟩ := trace_mul_eS T s ρ
  have hn : ∀ (Q : Pair K G), ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q)) := by
    intro Q
    rw [nS]
    exact finrank_range_idem _ (by rw [← map_mul, eps_idem])
  have hidS : ∀ (Q : Pair K G), (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s :=
    fun Q => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm
  apply Nat.cast_injective (R := K)
  rw [finrank_range_idem _ (by rw [← map_mul, hidS]), Nat.cast_mul,
    finrank_range_idem _ (by rw [← map_mul, hidS]), hc, hc, ← hn, ← hn, hM s, Nat.cast_one, mul_one, mul_comm]

lemma card_smul_eS (T : GoodSet K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) •
        MonoidAlgebra.of K G y := by
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]
  congr 1
  field_simp

end Alg2

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {G : Type} [Group G] [Fintype G]

lemma sigma0 (K : Type) [Field K] [NumberField K] : Nonempty (K →+* ℂ) :=
  ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom⟩

lemma chi_integral (T : GoodSet K G) (s : T.S) (y : G) :
    IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y)) := by
  obtain ⟨σ⟩ := sigma0 K
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  have hd : IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K)) := by
    have := isIntegral_algebraMap (R := ℤ) (A := K) (x := (finrank K (T.W s) : ℤ))
    simpa using this
  exact hd.mul h

lemma chi_norm (T : GoodSet K G) (s : T.S) (y : G) (σ : K →+* ℂ) :
    ‖σ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y))‖ ≤
      (finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ) := by
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

lemma ge_apply {V : Type} [AddCommGroup V] [Module K V] (T : GoodSet K G) (ρ : Representation K G V)
    (s : T.S) (x : V) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x := by
  rw [card_smul_eS, map_sum, LinearMap.sum_apply]
  simp only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]

lemma ge_mem (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (x : A.V) (hx : x ∈ A.L) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x ∈ A.L := by
  rw [ge_apply]
  refine A.L.sum_mem fun y _ => ?_
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r =
      ((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹) :=
    ⟨⟨_, chi_integral T s y⁻¹⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r (hA.2.1 y x hx)

lemma ge_norm (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (v : InfinitePlace K) (x : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x) ≤
      ((Fintype.card G : ℝ) * ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) *
        Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
  rw [ge_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans ?_
  have hterm : ∀ y : G, Formalism.HermitianLatticesTheory.normAt A.b A.X v
      ((((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x) ≤
      ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
    intro y
    rw [normAt_smul', hA.2.2]
    exact mul_le_mul_of_nonneg_right (chi_norm T s y⁻¹ v.embedding) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Lat

section AlgEps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma eG_eps_eS (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    eps P * eG T * (eps P * eS T s) = eps P * eS T s := by
  calc eps P * eG T * (eps P * eS T s) = eps P * (eG T * eps P) * eS T s := by simp only [mul_assoc]
    _ = eps P * (eps P * eG T) * eS T s := by rw [eG_comm]
    _ = (eps P * eps P) * (eG T * eS T s) := by simp only [mul_assoc]
    _ = eps P * eS T s := by rw [eps_idem, eG_mul_eS]

lemma eS_eps_eS (T : GoodSet K G) (P : Pair K G) (s t : T.S) :
    eS T t * (eps P * eS T s) = if s = t then eps P * eS T s else 0 := by
  rw [← mul_assoc, ← eS_comm, mul_assoc]
  split_ifs with h
  · subst h; rw [eS_idem]
  · rw [eS_orth T t s (Ne.symm h), mul_zero]

lemma eS_eps_eG (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s * (eps P * eG T) = eps P * eS T s * (((Fintype.card G : ℕ) : K) • eG T) := by
  rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← eS_comm, mul_assoc, eS_mul_eG]

lemma eG_eps_eG (T : GoodSet K G) (P : Pair K G) : eG T * (eps P * eG T) = eps P * eG T := by
  rw [← mul_assoc, ← eG_comm, mul_assoc, eG_idem]

end AlgEps

theorem splitBound : SplitBound := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  classical
  have hfd : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set L1 := cut A ρ (eps P * eG T) A.L with hL1def
  set L1s : T.S → Submodule (𝓞 K) A.V := fun s => cut A ρ (eps P * eS T s) A.L with hL1sdef
  set Pi : Submodule (𝓞 K) (T.S → A.V) := Submodule.pi Set.univ L1s with hPidef
  set ρP := Formalism.HN.piReal (fun _ : T.S => ρR) with hρP
  set dK : ℝ := (finrank ℚ K : ℝ) with hdK
  set R : ℕ := rkT T P0 P A ρ with hRdef
  have hdK0 : 0 < dK := by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL1 : L1 ≤ A.L := inf_le_left
  have hL1s : ∀ s, L1s s ≤ A.L := fun s => inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1
  have hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ) := by
    intro N hN
    rw [(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]
    push_cast
    rfl
  obtain ⟨hPiLat, hPirk, hPideg, -⟩ := Formalism.HN.piSum (𝓞 K) T.S (fun _ => A.V) (fun _ => _)
    (fun _ => ρR) L1s (fun s => lat _ (hL1s s))
  have hrkK1 : Formalism.HN.rkK L1 = R := rankPart K G T P0 P hM A ρ hA
  have hrkKs : ∀ s, Formalism.HN.rkK (L1s s) = nS T P s * rS T P0 A ρ s := by
    intro s
    show rkL A (cut A ρ (eps P * eS T s) A.L) = _
    rw [rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, rS, rkL_cut A hA.1]
  have hRsum : ((R : ℕ) : ℝ) = ∑ s, ((Formalism.HN.rkK (L1s s) : ℕ) : ℝ) := by
    rw [hRdef, rkT]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrkKs s]
    push_cast
    rfl
  have hrkPi : (Formalism.HN.rk ρP Pi : ℝ) = dK * R := by
    rw [hρP, hPidef, hPirk]
    push_cast
    rw [hRsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => hrkZ _ (hL1s s)
  have hrk1 : (Formalism.HN.rk ρR L1 : ℝ) = dK * R := by rw [hrkZ L1 hL1, hrkK1]

  have hnormP : ∀ x : T.S → A.V, ‖ρP x‖ ^ 2 = ∑ s, ‖ρR (x s)‖ ^ 2 := by
    intro x
    rw [hρP, PiLp.norm_sq_eq_of_L2]
    rfl
  have hcardS : (Fintype.card T.S : ℝ) ≤ Fintype.card G := by exact_mod_cast card_S_le T
  have hG1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hGpos : (0 : ℝ) < Fintype.card G := by linarith
  have hmemPi : ∀ x : T.S → A.V, x ∈ Pi ↔ ∀ s, x s ∈ L1s s := by
    intro x
    simp [hPidef, Submodule.mem_pi]

  let fA : (T.S → A.V) →+ A.V :=
    { toFun := fun x => ∑ s, x s
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib] }
  have hfA : ∀ x, fA x = ∑ s, x s := fun x => rfl
  have hA1 : ∀ x ∈ Pi, fA x ∈ L1 := by
    intro x hx
    rw [hmemPi] at hx
    rw [hfA]
    refine Submodule.mem_inf.mpr ⟨A.L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s)).1, ?_⟩
    show ∑ s, x s ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T))
    refine Submodule.sum_mem _ fun s _ => ?_
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
    refine ⟨ρ.asAlgebraHom (eps P * eS T s) z, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, eG_eps_eS, hz]
  have hA2 : ∀ x ∈ Pi, fA x = 0 → x = 0 := by
    intro x hx h0
    rw [hmemPi] at hx
    funext t
    have hproj : ∀ s, ρ.asAlgebraHom (eS T t) (x s) = if s = t then x s else 0 := by
      intro s
      obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eS_eps_eS]
      split_ifs <;> simp
    have := congrArg (ρ.asAlgebraHom (eS T t)) h0
    rw [hfA, map_sum, map_zero] at this
    simp only [hproj, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hA3 : ∀ x ∈ Pi, ‖ρR (fA x)‖ ≤ Real.sqrt (Fintype.card G) * ‖ρP x‖ := by
    intro x _
    rw [hfA, map_sum]
    have h1 : ‖∑ s, ρR (x s)‖ ≤ ∑ s, ‖ρR (x s)‖ := norm_sum_le _ _
    have h2 : (∑ s, ‖ρR (x s)‖) ^ 2 ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ s, ρR (x s)‖ ^ 2 ≤ (Real.sqrt (Fintype.card G) * ‖ρP x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hGpos.le, hnormP]
      calc ‖∑ s, ρR (x s)‖ ^ 2 ≤ (∑ s, ‖ρR (x s)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 := h2
        _ ≤ (Fintype.card G : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcardS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degA := deg_ge_of_inj ρP ρR Pi L1 hPiLat (lat L1 hL1) fA hA1 hA2
    (by exact_mod_cast hrkPi.trans hrk1.symm) (Real.sqrt (Fintype.card G)) (Real.sqrt_pos.mpr hGpos) hA3

  let fB : A.V →+ (T.S → A.V) :=
    { toFun := fun x s => ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x
      map_zero' := by funext s; simp
      map_add' := by intro x y; funext s; simp }
  have hfB : ∀ x s, fB x s = ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x := fun x s => rfl
  have hB1 : ∀ x ∈ L1, fB x ∈ Pi := by
    intro x hx
    rw [hmemPi]
    intro s
    rw [hfB]
    refine Submodule.mem_inf.mpr ⟨ge_mem T A ρ hA s x (Submodule.mem_inf.mp hx).1, ?_⟩
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))
    refine ⟨ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eG T) z, ?_⟩
    rw [← hz, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, eS_eps_eG]
  have hB2 : ∀ x ∈ L1, fB x = 0 → x = 0 := by
    intro x hx h0
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0 := by
      intro s
      have := congrFun h0 s
      rw [hfB, map_smul, LinearMap.smul_apply] at this
      exact (smul_eq_zero.mp this).resolve_left hG0
    have hx' : ρ.asAlgebraHom (eG T) x = x := by
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eG_eps_eG]
    rw [← hx', eG, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun s _ => hes s
  have hB3 : ∀ x ∈ L1, ‖ρP (fB x)‖ ≤ Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖ := by
    intro x _
    have hs : ∀ s, ‖ρR (fB x s)‖ ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖ := by
      intro s
      have hds : ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) ≤ Fintype.card G := by
        exact_mod_cast dim_sq_le T s
      have h1 := realize_le A.b A.X (fun y => fB y s) ((Fintype.card G : ℝ) *
        ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) (by positivity)
        (fun v y => ge_norm T A ρ hA s v y) x
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hds hGpos.le
    have h3 : ‖ρP (fB x)‖ ^ 2 ≤ (Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hnormP]
      calc ∑ s, ‖ρR (fB x s)‖ ^ 2 ≤ ∑ s : T.S, ((Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖) ^ 2 :=
            Finset.sum_le_sum fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hs s) 2
        _ = (Fintype.card T.S : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hcardS (by positivity)
        _ = (Fintype.card G : ℝ) ^ 5 * ‖ρR x‖ ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degB := deg_ge_of_inj ρR ρP L1 Pi (lat L1 hL1) hPiLat fB hB1 hB2
    (by exact_mod_cast hrk1.trans hrkPi.symm) (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) (by positivity) hB3

  have hconv1 := degL_eq A hA.1 L1 hL1
  have hconvs : ∑ s, degL A (L1s s) = (2 / dK) * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K := by
    rw [hρP, hPidef, hPideg, hRsum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => degL_eq A hA.1 (L1s s) (hL1s s)
  have hlogA : Real.log (Real.sqrt (Fintype.card G)) = laG G / 2 := by
    rw [Real.log_sqrt hGpos.le]; rfl
  have hlogB : Real.log (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) = 5 * laG G / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_pow]; unfold laG; push_cast; ring
  have hla : 0 ≤ laG G := Real.log_nonneg hG1
  rw [hlogA, hrkPi] at degA
  rw [hlogB, hrk1] at degB
  show |degL A L1 - ∑ s, degL A (L1s s)| ≤ 5 * laG G * (R : ℝ)
  rw [hconvs, hconv1, hrkK1]
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hexpr : (2 / dK * Formalism.HN.deg ρR L1 + (R : ℝ) * kap K) - (2 / dK * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K) =
      (2 / dK) * (Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi) := by ring
  have hD1 : -(dK * R * (laG G / 2)) ≤ Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi := by linarith
  have hD2 : Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi ≤ dK * R * (5 * laG G / 2) := by linarith
  have hc : 0 < 2 / dK := by positivity
  have e1 : (2 / dK) * (dK * R * (laG G / 2)) = R * laG G := by field_simp
  have e2 : (2 / dK) * (dK * R * (5 * laG G / 2)) = 5 * R * laG G := by field_simp
  have m1 := mul_le_mul_of_nonneg_left hD1 hc.le
  have m2 := mul_le_mul_of_nonneg_left hD2 hc.le
  rw [mul_neg, e1] at m1
  rw [e2] at m2
  have hRla : 0 ≤ R * laG G := mul_nonneg hR0 hla
  rw [hexpr, abs_le]
  constructor <;> linarith

end PI.Dv.Tr
