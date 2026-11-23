import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter

noncomputable section

namespace GlobalTheory.NL.IoXQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL PowerSeries

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem q_eq (W : LocWach PD LL O v n) : W.q = ∑ i ∈ Finset.range PD.p, (1 + letπ) ^ i := by
  funext j
  have h : (X : O⟦X⟧) * W.q₀ = X * ∑ i ∈ Finset.range PD.p, (1 + X) ^ i := by
    rw [W.q₀_def, ← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have h2 := PowerSeries.X_mul_cancel h
  simpa [LocWach.q, letπ, Finset.sum_apply] using h2

theorem φA_one_add (W : LocWach PD LL O v n) : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add, map_one, W.φA_π, q_eq]
  linear_combination geom_sum_mul (1 + (letπ : LetA O n)) PD.p

theorem φA_pow_one_add (W : LocWach PD LL O v n) (k : ℕ) :
    (W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add, ← pow_mul, pow_succ']

theorem X_eq (W : LocWach PD LL O v n) : W.X = (1 + letπ) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [← φA_pow_one_add W, map_add, map_one, add_sub_cancel_left, LocWach.X]

theorem Q_eq (W : LocWach PD LL O v n) :
    W.Q = ∑ i ∈ Finset.range PD.p, ((1 + letπ) ^ (PD.p ^ (W.s - 1))) ^ i := by
  rw [LocWach.Q, q_eq, map_sum]
  simp only [map_pow, φA_pow_one_add]

theorem isUnit_φA_pow (W : LocWach PD LL O v n) {a : LetA O n} (ha : IsUnit (algebraMap _ W.EE a)) (k : ℕ) :
    IsUnit (algebraMap _ W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, LocWach.φA, ← W.φE_ext]
    exact ih.map W.φE

theorem isUnit_X (W : LocWach PD LL O v n) : IsUnit (algebraMap _ W.EE W.X) :=
  isUnit_φA_pow W W.EE_π _

theorem isUnit_Q (W : LocWach PD LL O v n) : IsUnit (algebraMap _ W.EE W.Q) := by
  have h := isUnit_φA_pow W (isUnit_X W) 1
  rw [pow_one, W.φA_X, map_mul] at h
  exact isUnit_of_mul_isUnit_right h

variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    (E : EtTie W RA RW inclR φR gR πA) (x : W.EE) : E.ioE (W.φE x) = φR (E.ioE x) := by
  obtain ⟨e, e₀, hspan, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : e₁ ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e₁
    have h1 : (⟨e₁, hm⟩ : W.one.L.T) ∈ Submodule.span O {e₀} := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    apply he₁
    have := congrArg Subtype.val hc
    simpa [h] using this.symm
  have hinj : Function.Injective (LinearMap.toSpanSingleton O W.one.L.T e₀) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : c • (e₀ : W.one.V) = 0 := congrArg Subtype.val hc
    rw [← algebraMap_smul LL, smul_eq_zero] at h1
    exact hO ((h1.resolve_right he₀).trans (map_zero _).symm)
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton O W.one.L.T e₀) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hspan]
  obtain ⟨f, hf⟩ : ∃ f : W.one.L.T ≃ₗ[O] O, f e₀ = 1 :=
    ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm, (LinearEquiv.symm_apply_eq _).2 (one_smul O e₀).symm⟩
  have h1 := E.jD_φ W.one (x • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, hj] at h1
  simp only [TWmap, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply] at h1
  have h2 := congrArg (fun z => TensorProduct.rid O RW (LinearMap.lTensor RW f.toLinearMap z)) h1
  simpa [hf] using h2

theorem io_X_gen {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) :
    E.io W.X = (1 + πA) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [X_eq, map_sub, map_pow, map_add, map_one, E.io_π]

theorem io_Q_gen {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) :
    E.io W.Q = ∑ i ∈ Finset.range PD.p, ((1 + πA) ^ (PD.p ^ (W.s - 1))) ^ i := by
  rw [Q_eq, map_sum]
  simp only [map_pow, map_add, map_one, E.io_π]

end Generic

theorem tmul_X {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]
    (t u : A) (m : ℕ) (h : t ^ m = u) :
    (1 + (1 : O) ⊗ₜ[Z] (t - 1)) ^ m - 1 = (1 : O) ⊗ₜ[Z] (u - 1) := by
  rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel,
    Algebra.TensorProduct.tmul_pow, one_pow, h, TensorProduct.tmul_sub]

theorem tmul_Q {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]
    (t u : A) (m p : ℕ) (h : t ^ m = u) :
    ∑ i ∈ Finset.range p, ((1 + (1 : O) ⊗ₜ[Z] (t - 1)) ^ m) ^ i = (1 : O) ⊗ₜ[Z] (∑ i ∈ Finset.range p, u ^ i) := by
  rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel,
    Algebra.TensorProduct.tmul_pow, one_pow, h, TensorProduct.tmul_sum]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow]

theorem εroot_pow {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) :
    AI.εroot (k + 1) ^ (l ^ k) = AI.ε1 := by
  induction k with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ k ih =>
    rw [pow_succ', pow_mul, ← ih]
    congr 1
    rw [LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} {s : ℕ}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)))

omit E in
theorem teich_pow (hs : W.s = s) : WittVector.teichmuller l (AI.εroot s) ^ ((P.PD K).p ^ (W.s - 1)) =
    WittVector.teichmuller l AI.ε1 := by
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by have := W.s_pos; omega⟩
  rw [← map_pow, P.PD_p K, hs, hk, Nat.add_sub_cancel, εroot_pow]

theorem io_X (hs : W.s = s) : E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ :=
  (io_X_gen E).trans (tmul_X _ _ _ (teich_pow hs))

theorem io_Q (hs : W.s = s) : E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.ξ :=
  ((io_Q_gen E).trans (tmul_Q _ _ _ _ (teich_pow hs))).trans
    (congrArg (fun p => (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ∑ i ∈ Finset.range p, (WittVector.teichmuller l AI.ε1) ^ i)
      (P.PD_p K))

theorem ioE_φ' (x : W.EE) : E.ioE (W.φE x) = φRW LL (E.ioE x) :=
  ioE_φ Subtype.val_injective E x

theorem incl_io_φ (a : AA K LL) : inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a)) :=
  ((E.ioE_ext _).symm.trans (congrArg E.ioE (W.φE_ext a).symm)).trans
    ((ioE_φ' E _).trans (congrArg (φRW LL) (E.ioE_ext a)))

open GlobalTheory.IoInj in
set_option maxHeartbeats 1000000 in

theorem ioE_inj_inter : Function.Injective E.ioE ∧
      ∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x := by
  classical
  obtain ⟨_, hc, hl0, hlu, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨hWc, hWtf, -, hsat, hμ⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  haveI : NeZero (Module.finrank ℚ_[l] (K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Nontrivial (RW LL) := Module.FaithfullyFlat.lTensor_nontrivial ℤ_[l] ↥(OL LL) (WCb l)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases N with _ | n
    · exact absurd (by simpa using hN) hlu
    · exact ⟨n, rfl⟩
  obtain ⟨u, hu⟩ := hN.symm
  have hm : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hO : ∀ a : ↥(OL LL), IsUnit a ∨ ϖ ∣ a := by
    intro a
    by_cases h : IsUnit a
    · exact Or.inl h
    · right
      rw [← Ideal.mem_span_singleton, ← hm]
      exact h
  have hOp : ∀ a : ℕ → ↥(OL LL), (∀ k k', k ≤ k' → (l : ↥(OL LL)) ^ k ∣ a k - a k') →
      ∃ L, ∀ k, (l : ↥(OL LL)) ^ k ∣ a k - L := by
    intro a ha
    have hiff : ∀ (k : ℕ) (x y : ↥(OL LL)),
        x ≡ y [SMOD (IsLocalRing.maximalIdeal ↥(OL LL) ^ k • ⊤ : Submodule ↥(OL LL) ↥(OL LL))] ↔ ϖ ^ k ∣ x - y := by
      intro k x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := a) (by
      intro k k' hk
      rw [hiff]
      refine (pow_dvd_pow_of_dvd ?_ k).trans (ha k k' hk)
      exact ⟨ϖ ^ n * u, by rw [← hu]; ring⟩)
    refine ⟨L, fun k => ?_⟩
    have h1 := (hiff _ _ _).mp (hL ((n + 1) * k))
    have h2 : (l : ↥(OL LL)) ^ k ∣ ϖ ^ ((n + 1) * k) := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd hN.dvd k
    have : a k - L = (a k - a ((n + 1) * k)) + (a ((n + 1) * k) - L) := by ring
    rw [this]
    exact dvd_add (ha _ _ (by nlinarith)) (h2.trans h1)
  have hp := P.PD_p K
  have hE := W.EE_complete
  have hdense := W.EE_dense
  have hEsat := W.EE_sat
  rw [hp] at hE hdense hEsat
  refine (fun h => ⟨h.1, h.2.2.2⟩) (abstract (algebraMap _ W.EE) E.ioE.toRingHom E.io.toRingHom
    (inclR LL).toRingHom E.ioE_ext l
    (fun _ => C ϖ) letπ (fun _ => C (u : ↥(OL LL))) n
    (Pi.isUnit_iff.mpr fun _ => u.isUnit.map C) ?_ (fun i => Pi.single i 1) ?_ ?_
    (letter_form ϖ hO) (prec_pi l hOp) W.EE_π hE (fun x => hdense x 1) hEsat
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)) hWtf hsat ?_ ?_)
  · funext i
    have := congrArg (C : ↥(OL LL) →+* _) hu
    rw [map_natCast, map_mul, map_pow] at this
    simp only [Pi.natCast_apply, Pi.mul_apply, Pi.pow_apply, ← this]
    ring
  · intro i
    rw [← Pi.single_mul, mul_one]
  · exact Finset.univ_sum_single (1 : LetA ↥(OL LL) _)
  · haveI := hμ _ (not_isUnit_εroot_sub_one AI s)
    change E.io letπ ∈ _
    rw [E.io_π]
    exact IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
  · exact idem_ne_zero (algebraMap _ W.EE) E.ioE.toRingHom W.φ₀ W.φE (φRW LL) (map_zero _) W.φE_ext (ioE_φ' E)

end Concrete

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  intro D HW F l _ K s LL h W E
  have hs : W.s = s := (HW l).W_s K s LL h
  exact ⟨io_X E hs, io_Q E hs, (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1, (ioE_inj_inter E).1, incl_io_φ E,
    (ioE_inj_inter E).2, fun j => ⟨isUnit_φA_pow W (isUnit_X W) j, isUnit_φA_pow W (isUnit_Q W) j⟩⟩

end GlobalTheory.NL.IoXQ
