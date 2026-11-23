import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UnitFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LevelOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.MapLk

noncomputable section

open Formalism.ConjugateSelfDual Polynomial CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Z.Sym.Unl

section
variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N]

private structure Pre (k : ℤ) (f : (ZMod N)ˣ → ℍ → ℂ) : Prop where
  mf : ∀ a, ∃ F : ModularForm (Gamma1 N) k, (F : ℍ → ℂ) = f a
  fam : ∀ (a b : (ZMod N)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → (b : ZMod N) = a * ((γ 1 1 : ℤ) : ZMod N) →
    f a ∣[k] γ = f b

private structure Good (k : ℤ) (f : (ZMod N)ˣ → ℍ → ℂ) : Prop where
  pre : Pre k f
  int : ∀ a, IntQ ι (f a)
  cg : ∀ σ : ℂ ≃+* ℂ, ∃ f' : (ZMod N)ˣ → ℍ → ℂ, Pre k f' ∧ ∀ a n, coef (f' a) n = σ (coef (f a) n)

private def VC (k : ℕ) (f : (ZMod N)ˣ → ℍ → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ∃ f' : (ZMod N)ˣ → ℍ → ℂ, Pre (k : ℤ) f' ∧ (∀ a, VanOff N k (f' a)) ∧
    ∀ a n, coef (f' a) n = σ (coef (f a) n)

omit [NeZero N] in
private lemma one_mem_per :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

variable {ι}

private lemma Pre.q_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Pre k f) (hg : Pre k' g) (a) :
    qExpansion 1 (f a * g a) = qExpansion 1 (f a) * qExpansion 1 (g a) := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  rw [← hF, ← hG]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_per F G

private lemma Pre.coef_sum {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Pre k f) (hg : Pre k' g) (a) (n : ℕ) :
    coef (f a * g a) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef (f a) p.1 * coef (g a) p.2 := by
  unfold coef
  rw [hf.q_mul hg, PowerSeries.coeff_mul]

private lemma Good.coef_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) (a) :
    coef (f a * g a) 0 = coef (f a) 0 * coef (g a) 0 := by
  rw [hf.pre.coef_sum hg.pre]
  simp

private lemma Pre.mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Pre k f) (hg : Pre k' g) :
    Pre (k + k') (fun a => f a * g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F.mul G, by rw [ModularForm.coe_mul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [ModularForm.mul_slash_SL2, hf.fam a b γ hγ h, hg.fam a b γ hγ h]

private lemma Good.mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) :
    Good ι (k + k') (fun a => f a * g a) where
  pre := hf.pre.mul hg.pre
  int a n := by
    show ‖ι.symm (coef (f a * g a) n)‖ ≤ 1
    rw [hf.pre.coef_sum hg.pre, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hf.int a p.1) (norm_nonneg _) (hg.int a p.2)
  cg σ := by
    obtain ⟨f', pf, cf⟩ := hf.cg σ
    obtain ⟨g', pg, cg⟩ := hg.cg σ
    refine ⟨fun a => f' a * g' a, pf.mul pg, fun a n => ?_⟩
    show coef (f' a * g' a) n = σ (coef (f a * g a) n)
    rw [pf.coef_sum pg, hf.pre.coef_sum hg.pre, map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_mul, cf, cg]

private lemma Pre.coef_comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Pre k f) (hg : Pre k g) (c : ℂ) (a) (n : ℕ) :
    coef (f a + c • g a) n = coef (f a) n + c * coef (g a) n := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  unfold coef
  rw [← hF, ← hG]
  have h1 := ModularForm.qExpansion_add one_pos one_mem_per F (c • G)
  have h2 := ModularForm.qExpansion_smul one_pos one_mem_per c G
  rw [FunLike.coe_smul] at h1
  rw [h1, h2]
  simp

private lemma Good.coef_comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ) (a) (n : ℕ) :
    coef (f a + c • g a) n = coef (f a) n + c * coef (g a) n :=
  hf.pre.coef_comb hg.pre c a n

private lemma Pre.comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Pre k f) (hg : Pre k g) (c : ℂ) :
    Pre k (fun a => f a + c • g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F + c • G, by rw [FunLike.coe_add, FunLike.coe_smul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [SlashAction.add_slash, ModularForm.SL_smul_slash, hf.fam a b γ hγ h, hg.fam a b γ hγ h]

private lemma Good.comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ)
    (hc : ‖ι.symm c‖ ≤ 1) : Good ι k (fun a => f a + c • g a) where
  pre := hf.pre.comb hg.pre c
  int a n := by
    show ‖ι.symm (coef (f a + c • g a) n)‖ ≤ 1
    rw [hf.coef_comb hg, map_add, map_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf.int a n) ?_)
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) (hg.int a n)
  cg σ := by
    obtain ⟨f', pf, cf⟩ := hf.cg σ
    obtain ⟨g', pg, cg⟩ := hg.cg σ
    refine ⟨fun a => f' a + σ c • g' a, pf.comb pg (σ c), fun a n => ?_⟩
    show coef (f' a + σ c • g' a) n = σ (coef (f a + c • g a) n)
    rw [pf.coef_comb pg, hf.coef_comb hg, map_add, map_mul, cf, cg]

private lemma good_one (k : ℕ) (hk : Even k) (h2 : k ≠ 2) :
    ∃ E : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) E ∧ ∀ a, coef (E a) 0 = 1 := by
  obtain ⟨f, h1, h0, hi⟩ := levelOne N k hk h2
  have hp : Pre (k : ℤ) (fun _ : (ZMod N)ˣ => (f : ℍ → ℂ)) := ⟨fun _ => ⟨f, rfl⟩, fun _ _ γ _ _ => h1 γ⟩
  refine ⟨fun _ => f, ⟨hp, fun _ n => ?_, fun σ => ⟨_, hp, fun _ n => ?_⟩⟩, fun _ => h0⟩
  · obtain ⟨c, hc⟩ := hi n
    rw [hc, map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ c
  · obtain ⟨c, hc⟩ := hi n
    rw [hc, map_intCast]

omit [NeZero N] in
private lemma symm_Lk (k : ℕ) (x : ℂ) : ι.symm (Lk k x) = Lk k (ι.symm x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm

private def rt (ι : Qbar l ≃+* ℂ) (a : ZMod N) : Qbar l := ι.symm (ZMod.stdAddChar a : ℂ)

private lemma rt_pow (a : ZMod N) (n : ℕ) : rt ι a ^ n = rt ι (n • a) := by
  unfold rt
  rw [AddChar.map_nsmul_eq_pow, map_pow]

private lemma rt_zero : rt ι (0 : ZMod N) = 1 := by simp [rt]

private lemma rt_inj : Function.Injective (rt ι : ZMod N → Qbar l) :=
  ι.symm.injective.comp ZMod.injective_stdAddChar

private lemma rt_powN (a : ZMod N) : rt ι a ^ N = 1 := by
  rw [rt_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, rt_zero]

private lemma rt_norm (a : ZMod N) : ‖rt ι a‖ = 1 := by
  have h := congrArg norm (rt_powN (ι := ι) a)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).1 h

private lemma rt_neg (a : ZMod N) : rt ι (-a) = (rt ι a)⁻¹ := by
  unfold rt
  rw [AddChar.map_neg_eq_inv, map_inv₀]

private lemma rt_sq (hN : 3 ≤ N) (a : (ZMod N)ˣ) : rt ι (a : ZMod N) ^ 2 ≠ 1 := by
  intro h
  rw [rt_pow, ← rt_zero (ι := ι) (N := N)] at h
  have h1 := rt_inj h
  rw [nsmul_eq_mul, Units.mul_left_eq_zero, ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

private lemma unit_ne_zero (hN : 3 ≤ N) (a : (ZMod N)ˣ) : (a : ZMod N) ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact a.ne_zero

private lemma eis_coef0 (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : (ZMod N)ˣ) :
    ι.symm (coef (eisFun N k a) 0) = Lk k (rt ι (a : ZMod N)) := by
  rw [(eisCoef N k hk a (unit_ne_zero hN a)).1, symm_Lk]
  rfl

private lemma pre_eis (k : ℕ) (hk : 3 ≤ k) (s : (ZMod N)ˣ) :
    Pre (k : ℤ) (fun a : (ZMod N)ˣ => eisFun N k ((s * a : (ZMod N)ˣ) : ZMod N)) where
  mf a := eisMF N k hk _
  fam a b γ hγ h := by
    show eisFun N k ((s * a : (ZMod N)ˣ) : ZMod N) ∣[(k : ℤ)] γ = eisFun N k ((s * b : (ZMod N)ˣ) : ZMod N)
    rw [Units.val_mul, Units.val_mul, h, ← mul_assoc]
    exact eisSlash N k hk _ γ hγ

private lemma good_eis (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 3 ≤ k) :
    Good ι (k : ℤ) (fun a : (ZMod N)ˣ => eisFun N k a) where
  pre :=
    { mf := fun a => eisMF N k hk a
      fam := fun a b γ hγ h => by
        show eisFun N k a ∣[(k : ℤ)] γ = eisFun N k b
        rw [h]; exact eisSlash N k hk a γ hγ }
  int a n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [eis_coef0 hN k hk]
      refine (lkSep l hl N (by omega) hlN).1 k _ (rt_powN _) fun h => rt_sq (ι := ι) hN a ?_
      rw [h, one_pow]
    · rw [(eisCoef N k hk a (unit_ne_zero hN a)).2 n hn, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
      have hr : ∀ b : ZMod N, ‖ι.symm (ZMod.stdAddChar b : ℂ)‖ = 1 := fun b => rt_norm (ι := ι) b
      rw [map_mul ι.symm, norm_mul, map_pow ι.symm, map_natCast ι.symm, norm_pow, map_add ι.symm, map_mul ι.symm]
      refine mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ e))
        (norm_nonneg _) ?_
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_mul, hr, hr, map_pow ι.symm, map_neg ι.symm, map_one ι.symm, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        max_self]
  cg σ := by
    obtain ⟨s, -, hs⟩ := eisCj N (by omega) σ
    exact ⟨_, pre_eis k hk s, hs k hk⟩

private lemma factor_of {m : ℕ} (hm : Even m) (h2 : m ≠ 2) {H : (ZMod N)ˣ → ℍ → ℂ} (hH : Good ι (m : ℤ) H)
    (d : (ZMod N)ˣ) (hd : ‖ι.symm (coef (H 1) 0) - ι.symm (coef (H d) 0)‖ = 1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) m hm h2
  refine ⟨m, _, hm, hH.comb hE (-coef (H d) 0) (by rw [map_neg, norm_neg]; exact hH.int d 0), ?_, ?_⟩
  · rw [hH.coef_comb hE, hE0]; ring
  · rw [hH.coef_comb hE, hE0, mul_one, ← sub_eq_add_neg, map_sub, hd]

private lemma factor (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (d : (ZMod N)ˣ) (h1 : d ≠ 1) (h2 : d ≠ -1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have g4 := good_eis (ι := ι) hl hN hlN 4 (by norm_num)
  have g5 := good_eis (ι := ι) hl hN hlN 5 (by norm_num)
  have hx : rt ι (d : ZMod N) ≠ rt ι ((1 : (ZMod N)ˣ) : ZMod N) := fun h => h1 (Units.ext (rt_inj h))
  have hy : rt ι (d : ZMod N) ≠ (rt ι ((1 : (ZMod N)ˣ) : ZMod N))⁻¹ := fun h => by
    rw [← rt_neg] at h
    exact h2 (Units.ext (rt_inj h))
  rcases (lkSep l hl N (by omega) hlN).2.2 _ _ (rt_powN _) (rt_powN _) (rt_sq hN 1) (rt_sq hN d) hx hy with h | h | h
  · refine factor_of (m := 4) (by decide) (by decide) g4 d ?_
    rw [eis_coef0 hN 4 (by norm_num), eis_coef0 hN 4 (by norm_num), h]
  · refine factor_of (m := 6) (by decide) (by decide) (g3.mul g3) d ?_
    rw [g3.coef_mul g3, g3.coef_mul g3, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl, ← sq, ← sq, h]
  · refine factor_of (m := 8) (by decide) (by decide) (g3.mul g5) d ?_
    rw [g3.coef_mul g5, g3.coef_mul g5, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl,
      eis_coef0 hN 5 (by norm_num), eis_coef0 hN 5 (by norm_num), h]

private lemma killer (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (S : Finset (ZMod N)ˣ) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ (∀ d ∈ S, d ≠ 1 → d ≠ -1 → coef (h d) 0 = 0) ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) 0 (by decide) (by decide)
    exact ⟨0, E, by decide, hE, by simp, by rw [hE0, map_one, norm_one]⟩
  | insert d S _ ih =>
    obtain ⟨m, h, hm, hg, h0, hu⟩ := ih
    by_cases hd : d ≠ 1 ∧ d ≠ -1
    · obtain ⟨m', h', hm', hg', h0', hu'⟩ := factor (ι := ι) hl hN hlN d hd.1 hd.2
      refine ⟨m + m', fun a => h a * h' a, hm.add hm', by exact_mod_cast hg.mul hg', fun e he e1 e2 => ?_, ?_⟩
      · rw [hg.coef_mul hg']
        rcases Finset.mem_insert.1 he with rfl | he
        · rw [h0', mul_zero]
        · rw [h0 e he e1 e2, zero_mul]
      · rw [hg.coef_mul hg', map_mul, norm_mul, hu, hu', mul_one]
    · refine ⟨m, h, hm, hg, fun e he e1 e2 => ?_, hu⟩
      rcases Finset.mem_insert.1 he with rfl | he
      · exact absurd ⟨e1, e2⟩ hd
      · exact h0 e he e1 e2

private lemma van_mul {k k' : ℕ} {f : ℍ → ℂ} (hf : VanOff N k f) {g : (ZMod N)ˣ → ℍ → ℂ} (hg : Pre (k' : ℤ) g) (a) :
    VanOff N (k + k') (f * g a) := by
  intro γ hγ
  obtain ⟨G, hG⟩ := hg.mf a
  rw [Nat.cast_add, ModularForm.mul_slash_SL2, ← hG]
  exact Filter.ZeroAtFilter.mul_boundedAtFilter (hf γ hγ) (ModularFormClass.bdd_at_infty_slash G γ)

private lemma VC.mul {k k' : ℕ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hv : VC k f) (pf : Pre (k : ℤ) f) (hg : Good ι (k' : ℤ) g) :
    VC (k + k') (fun a => f a * g a) := by
  intro σ
  obtain ⟨f', p', v', c'⟩ := hv σ
  obtain ⟨g', pg, cg⟩ := hg.cg σ
  refine ⟨fun a => f' a * g' a, by rw [Nat.cast_add]; exact p'.mul pg, fun a => van_mul (v' a) pg a, fun a n => ?_⟩
  show coef (f' a * g' a) n = σ (coef (f a * g a) n)
  rw [p'.coef_sum pg, pf.coef_sum hg.pre, map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [map_mul, c', cg]

private lemma vc_eis (hN : 3 ≤ N) : VC 3 (fun a : (ZMod N)ˣ => eisFun N 3 a) := by
  intro σ
  obtain ⟨s, -, hs⟩ := eisCj N (by omega) σ
  exact ⟨_, pre_eis 3 le_rfl s, fun a => eisVan N 3 le_rfl _ (s * a).isUnit (by omega), hs 3 le_rfl⟩

private lemma base (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 10 ≤ k) :
    ∃ f : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) f ∧ (∀ a, VanOff N k (f a)) ∧ VC k f ∧ ‖ι.symm (coef (f 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have v3 : ∀ a : (ZMod N)ˣ, VanOff N 3 (eisFun N 3 a) := fun a => eisVan N 3 le_rfl a a.isUnit (by omega)
  have u3 : ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N)) 0)‖ = 1 := by
    rw [eis_coef0 hN 3 le_rfl]
    exact (lkSep l hl N (by omega) hlN).2.1 _ (rt_powN _) (rt_sq hN 1)
  have step : ∀ (j : ℕ) (g : (ZMod N)ˣ → ℍ → ℂ), Good ι (j : ℤ) g → ‖ι.symm (coef (g 1) 0)‖ = 1 →
      Good ι ((3 + j : ℕ) : ℤ) (fun a : (ZMod N)ˣ => eisFun N 3 a * g a) ∧
      (∀ a : (ZMod N)ˣ, VanOff N (3 + j) (eisFun N 3 a * g a)) ∧
      VC (3 + j) (fun a : (ZMod N)ˣ => eisFun N 3 a * g a) ∧
      ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N) * g 1) 0)‖ = 1 := fun j g hg hu =>
    ⟨by rw [Nat.cast_add]; exact g3.mul hg, fun a => van_mul (v3 a) hg.pre a, (vc_eis hN).mul g3.pre hg, by
      rw [g3.coef_mul hg, map_mul, norm_mul, u3, hu, mul_one]⟩
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 6) ⟨t - 3, by omega⟩ (by omega)
    obtain ⟨a1, -, -, a3⟩ := step _ E hE (by rw [hE0, map_one, norm_one])
    have := step _ _ a1 a3
    rw [show 3 + (3 + (2 * t - 6)) = 2 * t by omega] at this
    exact ⟨_, this⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 2) ⟨t - 1, by omega⟩ (by omega)
    have := step _ E hE (by rw [hE0, map_one, norm_one])
    rw [show 3 + (2 * t - 2) = 2 * t + 1 by omega] at this
    exact ⟨_, this⟩

end

end UpperTheory.V.Z.Sym.Unl

open UpperTheory.V.Sd UpperTheory.V.Z.Sym.Unl in
theorem UpperTheory.V.Z.Sym.Unl.unitFamC :
    UpperTheory.V.Z.Sym.Unl.UnitFamC := by
  intro l _ hl ι N _ hN hlN
  obtain ⟨m, h, -, hg, h0, hu⟩ := killer (ι := ι) hl hN hlN Finset.univ
  refine ⟨10 + m, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + m := ⟨k - m, by omega⟩
  obtain ⟨f, hf, hv, hc, hfu⟩ := base (ι := ι) hl hN hlN j (by omega)
  have hG : Good ι ((j + m : ℕ) : ℤ) (fun a => f a * h a) := by
    rw [Nat.cast_add]; exact hf.mul hg
  have hC := hc.mul hf.pre hg
  choose F hF using hG.pre.mf
  refine ⟨F, fun a b γ hγ hab => ?_, fun a => ?_, fun a => ?_, ?_, fun a a1 a2 => ?_, fun σ => ?_⟩
  · rw [hF, hF]; exact hG.pre.fam a b γ hγ hab
  · rw [hF]; exact hG.int a
  · rw [hF]; exact van_mul (hv a) hg.pre a
  · rw [hF, hf.coef_mul hg, map_mul, norm_mul, hfu, hu, mul_one]
  · rw [hF, hf.coef_mul hg, h0 a (Finset.mem_univ a) a1 a2, mul_zero]
  · obtain ⟨f', p', v', c'⟩ := hC σ
    choose F' hF' using p'.mf
    refine ⟨F', fun a b γ hγ hab => ?_, fun a => ?_, fun a n => ?_⟩
    · rw [hF', hF']; exact p'.fam a b γ hγ hab
    · rw [hF']; exact v' a
    · rw [hF', hF]; exact c' a n
