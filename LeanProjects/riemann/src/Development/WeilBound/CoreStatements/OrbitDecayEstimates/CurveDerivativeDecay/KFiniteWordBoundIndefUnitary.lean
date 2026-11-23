import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace

namespace CompanionTheory.Lime.T3

section Alg

variable {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_term (hU : IsInfUnitary ε E) (a b : Fin n) (x : M) :
    RCLike.re (inner ℂ ((E a b * E b a) x) x) = (if ε b = ε a then 1 else -1) * ‖E b a x‖ ^ 2 := by
  rw [Module.End.mul_apply, hU a b, inner_self_eq_norm_sq_to_K]
  unfold adjSign
  by_cases h : ε b = ε a
  · have h' : ε a = ε b := h.symm
    rw [if_pos h', if_pos h, one_mul, one_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  · have h' : ¬ ε a = ε b := fun e => h e.symm
    rw [if_neg h', if_neg h, neg_mul, one_mul, neg_mul, one_mul, map_neg, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]

theorem sum_sq_eq (hU : IsInfUnitary ε E) (x : M) :
    ∑ a, ∑ b, ‖E b a x‖ ^ 2 =
      2 * RCLike.re (inner ℂ (casimirK ε E x) x) - RCLike.re (inner ℂ (casimir E x) x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, sum_inner, map_sum]
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [re_term hU a b x]
  split_ifs <;> simp <;> ring

theorem norm_actM_le (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.hs X ≤ 1) (x : M) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑ a, ∑ b, ‖E b a x‖ ^ 2 ≤ C ^ 2) : ‖actM E X x‖ ≤ C := by
  have hS : ‖actM E X x‖ ≤ ∑ a, ∑ b, ‖X a b‖ * ‖E a b x‖ := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun b _ => norm_smul _ _)))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => ‖X p.1 p.2‖) (fun p => ‖E p.1 p.2 x‖)
  simp only [Fintype.sum_prod_type] at hCS
  have h2 : ∑ a, ∑ b, ‖E a b x‖ ^ 2 ≤ C ^ 2 := by
    rw [Finset.sum_comm]
    exact h
  have hX' : ∑ a, ∑ b, ‖X a b‖ ^ 2 ≤ 1 := hX
  have hS0 : 0 ≤ ∑ a, ∑ b, ‖X a b‖ * ‖E a b x‖ := by positivity
  have hsq : (∑ a, ∑ b, ‖X a b‖ * ‖E a b x‖) ^ 2 ≤ C ^ 2 := by
    refine hCS.trans ?_
    calc (∑ a, ∑ b, ‖X a b‖ ^ 2) * (∑ a, ∑ b, ‖E a b x‖ ^ 2) ≤ 1 * C ^ 2 :=
          mul_le_mul hX' h2 (by positivity) zero_le_one
      _ = C ^ 2 := one_mul _
  nlinarith

theorem nsq_le {u : Fin n → ℝ} {c : ℝ} (h : ∀ a, |u a| ≤ c) : nsq u ≤ n * c ^ 2 := by
  unfold nsq dot
  calc ∑ a, u a * u a ≤ ∑ _a : Fin n, c ^ 2 := Finset.sum_le_sum fun a _ => by
        have h1 := h a
        have h2 := abs_nonneg (u a)
        nlinarith [abs_mul_abs_self (u a)]
    _ = n * c ^ 2 := by simp

theorem nsq_nonneg' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg _

theorem abs_rhoN_le' (a : Fin n) : |rhoN ε a| ≤ n / 2 := by
  have key : ∀ s t : Finset (Fin n), |(((s.card : ℕ) : ℝ) - ((t.card : ℕ) : ℝ)) / 2| ≤ n / 2 := by
    intro s t
    have h1 : ((s.card : ℕ) : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ s).trans (by simp)
    have h2 : ((t.card : ℕ) : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ t).trans (by simp)
    have h3 : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
    have h4 : (0:ℝ) ≤ t.card := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  exact key _ _

theorem abs_rho_le (a : Fin n) : |rho n a| ≤ n / 2 := by
  unfold rho
  have h1 : ((a : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt a.isLt
  have h2 : (0:ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem layer_bound {lam : Fin n → ℝ} {B : ℝ} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hn : 1 ≤ n)
    (hB : ∀ a, |lam a| ≤ B) (hnB : (n : ℝ) ≤ 4 * B) {k S : ℕ} (hk : k ≤ S) {x : M} (hx : x ∈ layer ε E V k) :
    ∑ a, ∑ b, ‖E b a x‖ ^ 2 ≤ (8 * Real.sqrt n * (B + S) * ‖x‖) ^ 2 := by
  have hxg : x ∈ genSub E V := layer_le_genSub k hx
  have hcas : casimir E x = (casVal lam : ℂ) • x := casimir_genSub hE hc x hxg
  have hK := re_inner_casimirK_layer_le hE hU hV k hx
  rw [sum_sq_eq hU x, hcas]
  have hre : RCLike.re (inner ℂ ((casVal lam : ℂ) • x) x) = casVal lam * ‖x‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp
    left
    have h := RCLike.ofReal_re (K := ℂ) (‖x‖ ^ 2)
    rw [RCLike.ofReal_pow] at h
    exact h
  rw [hre]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by linarith
  have hS : (k:ℝ) ≤ S := by exact_mod_cast hk
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  set s := Real.sqrt n with hs
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ s := Real.sqrt_le_sqrt hn1
  have hlk : ∀ a, |(lowK ε lam + rhoC ε) a| ≤ B + n / 2 := by
    intro a
    have e : (lowK ε lam + rhoC ε) a = lam a + rhoN ε a := by
      simp only [lowK, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (hB a) (abs_rhoN_le' a))
  have hN := nsq_le hlk
  have hsN : Real.sqrt (nsq (lowK ε lam + rhoC ε)) ≤ s * (B + n / 2) := by
    calc Real.sqrt (nsq (lowK ε lam + rhoC ε)) ≤ Real.sqrt ((s * (B + n / 2)) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow, hs2]; exact hN)
      _ = s * (B + n / 2) := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
  have hrho := nsq_le (fun a => abs_rho_le (n := n) a)
  have hl0 := nsq_nonneg' lam
  have hrc0 := nsq_nonneg' (rhoC ε)
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := Real.sqrt_sq (by norm_num)
  set R := Real.sqrt (nsq (lowK ε lam + rhoC ε)) + Real.sqrt 2 * k with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hR : R ≤ 3 * s * (B + S) := by
    have h1 : s * (B + n / 2) ≤ s * (3 * B) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : Real.sqrt 2 * k ≤ 2 * S := mul_le_mul hsq2 hS hk0 (by norm_num)
    have h3 : 2 * (S:ℝ) ≤ 2 * s * S := by nlinarith
    nlinarith
  have hmain : 2 * (R ^ 2 - nsq (rhoC ε)) - casVal lam ≤ 64 * n * (B + S) ^ 2 := by
    have hcasv : casVal lam = nsq lam - nsq (rho n) := rfl
    rw [hcasv]
    have hR2 : R ^ 2 ≤ 9 * n * (B + S) ^ 2 := by
      have h6 := pow_le_pow_left₀ hR0 hR 2
      rw [mul_pow, mul_pow, hs2] at h6
      linarith
    have hrho' : nsq (rho n) ≤ 4 * n * (B + S) ^ 2 := by
      have h4 : (n:ℝ) / 2 ≤ 2 * (B + S) := by linarith
      have h5 : ((n:ℝ) / 2) ^ 2 ≤ (2 * (B + S)) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      nlinarith
    nlinarith
  calc _ ≤ 2 * ((R ^ 2 - nsq (rhoC ε)) * ‖x‖ ^ 2) - casVal lam * ‖x‖ ^ 2 := by linarith
    _ = (2 * (R ^ 2 - nsq (rhoC ε)) - casVal lam) * ‖x‖ ^ 2 := by ring
    _ ≤ (64 * n * (B + S) ^ 2) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hmain hx2
    _ = (8 * s * (B + S) * ‖x‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hs2]
      ring

theorem actM_mem_layer (hE : IsGlRep E) {V : Submodule ℂ M} (hV : IsKStableSub ε E V) (X : Matrix (Fin n) (Fin n) ℂ)
    {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) : actM E X x ∈ layer ε E V (k + 1) := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

end Alg

theorem le_four_mul {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : (m : ℝ) ≤ 4 * B := by
  obtain ⟨hanti, hint⟩ := hl
  have step : ∀ a b : Fin m, a < b → 1 ≤ lam a - lam b := by
    intro a b hab
    obtain ⟨p, hp⟩ := hint a
    obtain ⟨q, hq⟩ := hint b
    have hlt : lam b < lam a := hanti hab
    have hpq : (q : ℝ) < p := by linarith
    have hpq' : q < p := by exact_mod_cast hpq
    have h3 : q + 1 ≤ p := hpq'
    have h4 : (q : ℝ) + 1 ≤ p := by exact_mod_cast h3
    linarith
  have chain : ∀ k : ℕ, ∀ hk : k < m, (k : ℝ) ≤ lam ⟨0, by omega⟩ - lam ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := step ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp [Fin.lt_def])
      push_cast
      linarith
  have hc := chain (m - 1) (by omega)
  have hB0 := hB ⟨0, by omega⟩
  have hB1 := hB ⟨m - 1, by omega⟩
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hm1] at hc
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [abs_le] at hB0 hB1
  linarith [hB0.1, hB0.2, hB1.1, hB1.2]

theorem stdGap_of {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} (hm : 1 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 2 * (m : ℝ) ^ 3 + 1 ≤ h) : StdGap ε lam := by
  refine ⟨hl.1, h, hg, ?_⟩
  have hp : (pOf ε : ℝ) ≤ m := by
    unfold pOf
    exact_mod_cast (Finset.card_le_univ _).trans (by simp)
  have hq : (qOf ε : ℝ) ≤ m := by
    unfold qOf
    exact_mod_cast (Finset.card_le_univ _).trans (by simp)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp0 : (0:ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ qOf ε := Nat.cast_nonneg _
  have hpq := mul_le_mul hp hq hq0 (by linarith)
  have h1 : (m:ℝ) * pOf ε * qOf ε ≤ (m:ℝ) ^ 3 := by nlinarith
  have h3 : (0:ℝ) < (m:ℝ) ^ 3 := by positivity
  linarith

theorem dsigC_eq_actM {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (x : smD ε σ) : PI.DSInfCharCap.dsigC ε σ Y x = ((actM (smE ε σ) Y x : smD ε σ) : H) := by
  have hD := isDerivedOn_smE hσ
  have e1 : (1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y) = S7.cpart1 ε Y := by
    unfold PI.DSInfCharCap.thetaJ S7.cpart1
    rw [sub_eq_add_neg]
    rfl
  have e2 : (1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y) = S7.cpart2 ε Y := by
    unfold PI.DSInfCharCap.thetaJ S7.cpart2
    rw [sub_neg_eq_add]
    rfl
  show PI.PhMeasCore.dsig σ ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) x +
      Complex.I • PI.PhMeasCore.dsig σ ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) x = _
  rw [e1, e2]
  have d1 : PI.PhMeasCore.dsig σ (S7.cpart1 ε Y) x = ((actM (smE ε σ) (S7.cpart1 ε Y) x : smD ε σ) : H) :=
    dS_eq_actM hD (SmDerA.inG_cpart1 ε Y) x
  have d2 : PI.PhMeasCore.dsig σ (S7.cpart2 ε Y) x = ((actM (smE ε σ) (S7.cpart2 ε Y) x : smD ε σ) : H) :=
    dS_eq_actM hD (SmDerA.inG_cpart2 ε Y) x
  rw [d1, d2]
  conv_rhs => rw [SmDerA.cpart_decomp ε Y]
  rw [actM_add', actM_smul']
  simp

theorem kFiniteWordBound_indefUnitary : PositivityTheory.UnitaryDecomposition.WordBd := by
  unfold PositivityTheory.UnitaryDecomposition.WordBd
  intro m ε lam B H _ _ π hm hl hDS hB hg v hv
  have hm1 : 1 ≤ m := by omega
  haveI : CompleteSpace H := hDS.1
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hD := isDerivedOn_smE hπ
  have hGl : IsGlRep (smE ε π) := hD.glRep
  have hIU : IsInfUnitary ε (smE ε π) := isInfUnitary_of_isDerivedOn hπ hD
  have hm3 : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hgap : 2 * (m:ℝ) ^ 3 + 1 ≤ 100 * (m:ℝ) ^ 3 := by
    have h1 : (1:ℝ) ≤ (m:ℝ) ^ 3 := one_le_pow₀ hm3
    linarith
  have hstd : StdGap ε lam := stdGap_of hm1 hl hg hgap
  obtain ⟨_, h', hg', hlt⟩ := hstd
  obtain ⟨hcasS, huniq, _, hsmooth, _⟩ := isDS_props_of_gap m ε lam hl h' hg' hlt H π hDS
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  have hsub : Formalism.MainNotions.S.lowKSub ε lam π = S0 := by
    have hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S} = {S0} := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => huniq S S0 h hS0, fun h => h ▸ hS0⟩
    unfold Formalism.MainNotions.S.lowKSub
    rw [hset, sSup_singleton]
  rw [hsub] at hv
  have hsm0 : ∀ u ∈ S0, IsSmoothVecU ε π u := hsmooth S0 hS0.1 hS0.2.1
  have hS0le : S0 ≤ smD ε π := fun u hu => (mem_smD_iff ε π u).2 (hsm0 u hu)
  obtain ⟨w, hwS, hw0, hwk⟩ := exists_isKHWVec_of_isKTypeOf hπ hD hS0 hS0le
  let T : Submodule ℂ (smD ε π) := S0.comap (smD ε π).subtype
  have hTfd : FiniteDimensional ℂ T := by
    haveI := hS0.1
    let f : T →ₗ[ℂ] S0 := ((smD ε π).subtype.comp T.subtype).codRestrict S0 (fun x => x.2)
    refine Module.Finite.of_injective f (fun a b hab => ?_)
    have h : ((f a : S0) : H) = ((f b : S0) : H) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hTk : ∀ k ∈ Kset ε, ∀ y ∈ T, ∃ z ∈ T, (z : H) = π k (y : H) := by
    intro k hk y hy
    have hsy : IsSmoothVecU ε π (y : H) := (mem_smD_iff ε π _).1 y.2
    refine ⟨⟨π k y, (mem_smD_iff ε π _).2 (IsSmoothVecU.kStable hπ hk hsy)⟩, ?_, rfl⟩
    exact hS0.2.1 k hk _ hy
  have hTst : IsKStableSub ε (smE ε π) T := isKStableSub_of_kStable hπ hD T hTfd hTk
  have hwk' : IsKHWVec ε (smE ε π) (lowK ε lam) w := hwk
  let V := kLowSpan ε (smE ε π) w
  have hVT : V ≤ T := kLowSpan_le hTst hwS
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVT
  have hVirr : IsKIrrHW ε (smE ε π) (lowK ε lam) V := kLowSpan_kIrrHW hGl hIU hwk' hw0 hVfd
  have hVst : IsKStableSub ε (smE ε π) V := kLowSpan_kStable hGl hwk'
  have hVk := kStable_of_isKStableSub hπ hD V hVfd hVst
  have hmapS : Submodule.map (smD ε π).subtype V = S0 := by
    have hle : Submodule.map (smD ε π).subtype V ≤ S0 := by
      rintro u ⟨y, hy, rfl⟩
      exact hVT hy
    rcases hS0.2.2.1 _ hle (by
        rintro g hg u ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hze⟩ := hVk g hg y hy
        exact ⟨z, hz, hze⟩) with h | h
    · exfalso
      have hwm : (w : H) ∈ Submodule.map (smD ε π).subtype V := ⟨w, self_mem_kLowSpan w, rfl⟩
      rw [h] at hwm
      exact hw0 (Subtype.ext ((Submodule.mem_bot ℂ).1 hwm))
    · exact h
  rw [← hmapS] at hv
  obtain ⟨x0, hx0V, rfl⟩ := hv
  have hcV : ∀ y ∈ V, casimir (smE ε π) y = (casVal lam : ℂ) • y := by
    intro y _
    apply Subtype.ext
    rw [← casU_eq_casimir hD y]
    exact hcasS y ((mem_smD_iff ε π _).1 y.2)
  have hnB : (m:ℝ) ≤ 4 * B := le_four_mul hm hl hB
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hF, hfe⟩ := ((mem_smD_iff ε π _).1 x0.2) g₀ hg₀
    exact ⟨U, F, hUo, hgU, hF, fun g hg hgi => hfe g hg hgi⟩
  intro S W hlen hX
  have hS0' : (0:ℝ) ≤ S := Nat.cast_nonneg _
  have hC0 : 0 ≤ 8 * Real.sqrt m * (B + S) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
  have step : ∀ X, Formalism.REAL.hs X ≤ 1 → ∀ k ≤ S, ∀ z : smD ε π, z ∈ layer ε (smE ε π) V k →
      ‖actM (smE ε π) X z‖ ≤ 8 * Real.sqrt m * (B + S) * ‖z‖ := by
    intro X hXX k hk z hz
    have hlb := layer_bound hGl hIU hVirr hcV hm1 hB hnB hk hz
    exact norm_actM_le X hXX z (mul_nonneg hC0 (norm_nonneg _)) hlb
  have key : ∀ W' : List (Matrix (Fin m) (Fin m) ℂ), (∀ X ∈ W', Formalism.REAL.hs X ≤ 1) → ∀ (j : ℕ) (y : smD ε π),
      y ∈ layer ε (smE ε π) V j → j + W'.length ≤ S →
      ∃ z : smD ε π, z ∈ layer ε (smE ε π) V (j + W'.length) ∧
        (z : H) = PI.DSInfCharCap.dsigCW ε π W' y ∧ ‖z‖ ≤ (8 * Real.sqrt m * (B + S)) ^ W'.length * ‖y‖ := by
    intro W'
    induction W' with
    | nil =>
      intro _ j y hy _
      exact ⟨y, by simpa using hy, rfl, by simp⟩
    | cons X W' ih =>
      intro hXW j y hy hjl
      have hl' : j + W'.length ≤ S := by
        simp only [List.length_cons] at hjl
        omega
      obtain ⟨z, hz, hze, hzn⟩ := ih (fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)) j y hy hl'
      have hXX : Formalism.REAL.hs X ≤ 1 := hXW X (List.mem_cons_self ..)
      refine ⟨actM (smE ε π) X z, ?_, ?_, ?_⟩
      · have hm' := actM_mem_layer hGl hVst X hz
        simpa [Nat.add_assoc] using hm'
      · show _ = PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigCW ε π W' y)
        rw [← hze, dsigC_eq_actM hπ X z]
      · have h1 := step X hXX (j + W'.length) hl' z hz
        calc ‖actM (smE ε π) X z‖ ≤ 8 * Real.sqrt m * (B + S) * ‖z‖ := h1
          _ ≤ 8 * Real.sqrt m * (B + S) * ((8 * Real.sqrt m * (B + S)) ^ W'.length * ‖y‖) :=
            mul_le_mul_of_nonneg_left hzn hC0
          _ = (8 * Real.sqrt m * (B + S)) ^ (X :: W').length * ‖y‖ := by
            rw [List.length_cons, pow_succ]
            ring
  obtain ⟨z, _, hze, hzn⟩ := key W hX 0 x0 hx0V (by simpa using hlen)
  show ‖PI.DSInfCharCap.dsigCW ε π W (x0 : H)‖ ≤ (8 * Real.sqrt m * (B + S)) ^ W.length * ‖(x0 : H)‖
  rw [← hze]
  exact hzn

end CompanionTheory.Lime.T3
