import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.TrLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharacterEigenspaceAddMem

noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT UpperTheory.V.Hi UpperTheory.V.AlgebraTools

open NumberField IsDedekindDomain Formalism.UG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem psum_ne (Z : Multiset ℂ) (hZ : Z ≠ 0) (h0 : (0 : ℂ) ∉ Z) :
    ∃ j : ℕ, 1 ≤ j ∧ (Z.map (· ^ j)).sum ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀⟩ := Multiset.exists_mem_of_ne_zero hZ
  set S := Z.toFinset with hS
  let Q : Polynomial ℂ := Polynomial.X * ∏ z ∈ S.erase z₀, (Polynomial.X - Polynomial.C z)
  have hp : ∀ j, 1 ≤ j → ∑ a ∈ S, (Z.count a : ℂ) * a ^ j = 0 := fun j hj => by
    have := hcon j hj
    rw [Finset.sum_multiset_map_count] at this
    simpa [nsmul_eq_mul] using this
  have hq0 : Q.coeff 0 = 0 := by simp [Q, Polynomial.mul_coeff_zero]
  have h1 : ∑ a ∈ S, (Z.count a : ℂ) * Q.eval a = 0 := by
    have : ∀ a, Q.eval a = ∑ j ∈ Q.support, Q.coeff j * a ^ j := fun a => by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hq0]
    · calc _ = Q.coeff j * ∑ a ∈ S, (Z.count a : ℂ) * a ^ j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by rw [hp j hj, mul_zero]
  have h2 : ∑ a ∈ S, (Z.count a : ℂ) * Q.eval a = (Z.count z₀ : ℂ) * Q.eval z₀ := by
    refine Finset.sum_eq_single_of_mem z₀ (Multiset.mem_toFinset.2 hz₀) fun a ha hne => ?_
    have : Q.eval a = 0 := by
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, ha⟩) (sub_self a), mul_zero]
    rw [this, mul_zero]
  rw [h2] at h1
  have hc : (Z.count z₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Multiset.count_ne_zero.2 hz₀)
  have hQ : Q.eval z₀ ≠ 0 := by
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C]
    refine mul_ne_zero (fun h => h0 (h ▸ hz₀)) (Finset.prod_ne_zero_iff.2 fun a ha => sub_ne_zero.2 (Finset.ne_of_mem_erase ha).symm)
  exact mul_ne_zero hc hQ h1

private theorem exists_pow_trace {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (T : Module.End ℂ W) (hT : IsUnit T) : ∃ j : ℕ, 1 ≤ j ∧ LinearMap.trace ℂ W (T ^ j) ≠ 0 := by
  obtain ⟨u, rfl⟩ := hT
  let R : Representation ℂ (Multiplicative ℤ) W := (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨E, -, hE⟩ := GlobalTheory.IwahoriTraceProof.exists_exponents (G := Multiplicative ℤ) _ W R rfl
  have hR : ∀ j : ℕ, R (Multiplicative.ofAdd 1 ^ j) = (u : Module.End ℂ W) ^ j := fun j => by
    rw [map_pow]
    congr 1
  let Z : Multiset ℂ := E.map fun χ => ((χ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ)
  have hcard : (Module.finrank ℂ W : ℂ) = (E.card : ℂ) := by
    have h1 := hE 1
    rw [map_one, Module.End.one_eq_id, LinearMap.trace_id] at h1
    rw [h1]
    simp
  have hZ : Z ≠ 0 := by
    intro h
    have hE0 : E = 0 := by simpa [Z] using h
    rw [hE0] at hcard
    have : Module.finrank ℂ W = 0 := by exact_mod_cast hcard
    exact Module.finrank_pos.ne' this
  have h0 : (0 : ℂ) ∉ Z := by
    intro h
    obtain ⟨χ, -, h⟩ := Multiset.mem_map.1 h
    exact (χ (Multiplicative.ofAdd 1)).ne_zero h
  obtain ⟨j, hj, hne⟩ := psum_ne Z hZ h0
  refine ⟨j, hj, fun h => hne ?_⟩
  rw [← hR, hE] at h
  rw [← h, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun χ _ => ?_
  simp

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem fixed_eq (ρ : Representation ℂ G V) (I : Subgroup G) : fixed ρ I = fixd ρ I := by
  ext v
  rw [GlobalTheory.TwTrLevel.mem_fixed_iff]
  rfl

private theorem mem_orbit (I : Subgroup G) (x g : G) :
    (g : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ I) = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ I) = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

open scoped Classical in
private theorem levOp_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (x : G) (hx : FinOrb I I x) (f : G → ℂ)
    (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0) (v : fixd ρ I) :
    levOp ρ K I f LinearMap.id (v : V) = ((I.relIndex K : ℕ) : ℂ)⁻¹ • (hk ρ I x v : V) := by
  have hx' : (MulAction.orbit I (x : G ⧸ I)).Finite := hx
  have h1 : (hk ρ I x v : V) = ∑ q ∈ hx'.toFinset, ρ q.out v := by
    rw [hk, (hkApply ℂ G V ρ I I x hx).1 v, UpperTheory.V.Hi.dc,
      finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hx',
      LinearMap.sum_apply]
  have hmem : ∀ q : G ⧸ I, q ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, q.out = a * x * b := fun q => by
    rw [← mem_orbit, QuotientGroup.out_eq']
  have h2 : (∑ᶠ q : G ⧸ I, f q.out • (ρ q.out ∘ₗ LinearMap.id)) = ∑ q ∈ hx'.toFinset, ρ q.out := by
    rw [finsum_eq_sum_of_support_subset (s := hx'.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [hf, if_pos ((hmem q).1 (hx'.mem_toFinset.1 hq)), one_smul]
      rfl
    · intro q hq
      rw [Finset.mem_coe, hx'.mem_toFinset, hmem]
      by_contra hn
      exact hq (by show f q.out • _ = 0; rw [hf, if_neg hn, zero_smul])
  unfold levOp
  rw [h2, h1, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem trace_move {M M' : Submodule ℂ V} (h : M = M') (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v ∈ M)
    (B : Module.End ℂ M') (hB : ∀ v : M', L v = B v) :
    LinearMap.trace ℂ M (L.restrict hL) = LinearMap.trace ℂ M' B := by
  subst h
  congr 1
  ext v
  exact hB v

open scoped Classical in
private theorem twTr_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (x : G) (hx : FinOrb I I x) (f : G → ℂ)
    (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0) :
    twTr ρ K I f LinearMap.id = ((I.relIndex K : ℕ) : ℂ)⁻¹ * LinearMap.trace ℂ (fixd ρ I) (hk ρ I x) := by
  have hst : ∀ v ∈ fixed ρ I, levOp ρ K I f LinearMap.id v ∈ fixed ρ I := fun v hv => by
    rw [fixed_eq] at hv ⊢
    rw [levOp_eq ρ K I x hx f hf ⟨v, hv⟩]
    exact Submodule.smul_mem _ _ (hk ρ I x ⟨v, hv⟩).2
  unfold twTr
  rw [dif_pos hst, trace_move (fixed_eq ρ I) _ hst (((I.relIndex K : ℕ) : ℂ)⁻¹ • hk ρ I x)
    fun v => levOp_eq ρ K I x hx f hf v, map_smul, smul_eq_mul]

end Abs

section Lev

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

open scoped Classical in
private theorem trc_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hIo : IsOpen (I : Set G)) (hIc : IsCompact (I : Set G)) (hIK : I ≤ K) (x : G)
    (f : G → ℂ) (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0)
    (hfd : FiniteDimensional ℂ (fixed ρ I)) :
    trc ρ K f = twTr ρ K I f LinearMap.id :=
  _root_.UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc_eq ρ K I hKo hKc hIo hIc hIK x f hf hfd

end Lev

section Loc

open ValuativeRel GlobalTheory.SmGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem dom_pow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {a : Fin n → ℤ} (ha : Antitone a) :
    Dom fun i => ϖ ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 hϖ).2 (ha hij)

private theorem exists_hk_trace {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    {I : Subgroup (GL (Fin n) k)} (hI : iwC k n ⊤ = I) [FiniteDimensional ℂ (fixd ρ I)] [Nontrivial (fixd ρ I)]
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) :
    ∃ x : Fin n → ℤ, StrictAnti x ∧
      LinearMap.trace ℂ (fixd ρ I) (hk ρ I (diagT k (Fin n) fun i => ϖ ^ x i)) ≠ 0 := by
  subst hI
  obtain ⟨hmul, hunit, -⟩ := domMul k n ⊤ ℂ V ρ
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.2 (GlobalTheory.SplitWeil.one_lt_resCard k).ne_bot).isUnit
  let x₀ : Fin n → ℤ := fun i => -(i : ℤ)
  have hx₀ : StrictAnti x₀ := fun a b h => by
    have : (a : ℤ) < b := by exact_mod_cast h
    simp only [x₀]
    omega
  let T := hk ρ (iwC k n ⊤) (diagT k (Fin n) fun i => ϖ ^ x₀ i)
  have hT : IsUnit T := hunit hq _ (dom_pow hϖ hx₀.antitone)
  have hsa : ∀ j : ℕ, 1 ≤ j → StrictAnti (j • x₀) := fun j hj a b h => by
    have h1 := hx₀ h
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h1 (by exact_mod_cast hj)
  have hpow : ∀ j : ℕ, hk ρ (iwC k n ⊤) (diagT k (Fin n) fun i => ϖ ^ ((j + 1) • x₀) i) = T ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp [T]
    | succ j ih =>
      rw [pow_succ, ← ih]
      show _ = hk ρ (iwC k n ⊤) _ * hk ρ (iwC k n ⊤) _
      rw [hmul _ _ (dom_pow hϖ (hsa _ (by omega)).antitone) (dom_pow hϖ hx₀.antitone)]
      congr 2
      funext i
      simp only [Pi.mul_apply, Pi.smul_apply, ← _root_.zpow_add]
      congr 1
      simp only [nsmul_eq_mul]
      push_cast
      ring
  obtain ⟨j, hj, hne⟩ := exists_pow_trace T hT
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨(j + 1) • x₀, hsa _ hj, ?_⟩
  rw [hpow]
  exact hne

end Loc

private theorem v_lt_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (h : Formalism.UG.ordL x = 1) :
    Valued.v x < 1 := by
  unfold Formalism.UG.ordL at h
  split_ifs at h with h0
  · exact absurd h (by norm_num)
  · have h1 : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by omega
    have h2 : WithZero.unzero h0 < 1 := by
      show Multiplicative.toAdd (WithZero.unzero h0) < (0 : ℤ)
      omega
    rw [← WithZero.coe_unzero h0]
    exact_mod_cast h2

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open ValuativeRel GlobalTheory.SmGL GlobalTheory.LFun in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosTr :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosTr := by
  classical
  intro E _ _ _ n w ϖ hϖ τ hτ
  let I := iwGL n w
  have hI : iwC (w.adicCompletion E) n ⊤ = I := (memIwC (w.adicCompletion E) n ⊤).2.1
  have hIo : IsOpen (I : Set (GLw n w)) := GroundTheory.Automorphic.GLnLocal.isOpen_iwahori _ _
  have hIc : IsCompact (I : Set (GLw n w)) := GroundTheory.Automorphic.GLnLocal.isCompact_iwahori _ _
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hIK : I ≤ KGL w n := GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w n
  have hfd : FiniteDimensional ℂ (fixed τ.ρ I) :=
    (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds _ _ _ τ.ρ τ.smooth τ.irred).2 _ hIo hIc
  haveI hfd' : FiniteDimensional ℂ (UpperTheory.V.Hi.fixd τ.ρ I) := by
    rw [← fixed_eq]
    exact hfd
  haveI hnt : Nontrivial (UpperTheory.V.Hi.fixd τ.ρ I) := by
    rw [Submodule.nontrivial_iff_ne_bot, ← fixed_eq]
    intro hb
    refine hτ (eq_bot_iff.2 fun v hv => ?_)
    have hvI : v ∈ fixed τ.ρ I := by
      rw [GlobalTheory.TwTrLevel.mem_fixed_iff] at hv ⊢
      exact fun k hk => hv k (hIK hk)
    rw [hb] at hvI
    exact hvI
  have hv : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CjInv.lt_one_iff _ |>.2 (v_lt_one hϖ)
  obtain ⟨x, hx, hne⟩ := exists_hk_trace τ.ρ hI hv
  refine ⟨x, hx, ?_⟩
  have hfx : ∀ y, dcos n w (tdiag ϖ x) y = if ∃ a ∈ I, ∃ b ∈ I, y = a * tdiag ϖ x * b then 1 else 0 := fun y => rfl
  have hfin : UpperTheory.V.AlgebraTools.FinOrb I I (tdiag ϖ x) := by
    rw [← hI]
    exact (heckePairIwC (w.adicCompletion E) n ⊤).1 _
  rw [trc_eq τ.ρ (KGL w n) I hKo hKc hIo hIc hIK _ _ hfx hfd, twTr_eq τ.ρ _ I _ hfin _ hfx]
  refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 ?_)) hne
  haveI := GlobalTheory.TwTrLevel.finite_quot (KGL w n) (KGL w n) I hKc hKo hIo le_rfl
  exact Subgroup.index_ne_zero_of_finite
