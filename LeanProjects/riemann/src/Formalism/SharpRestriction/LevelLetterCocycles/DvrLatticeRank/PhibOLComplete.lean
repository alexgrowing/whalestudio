import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LiftingTheory

section PhiB

variable {O : Type} [CommRing O]

def phibY (O : Type) [CommRing O] (p : ℕ) : Polynomial O := (Polynomial.X + 1) ^ p - 1

theorem phib_coe (p : ℕ) :
    ((phibY O p : Polynomial O) : PowerSeries O) = (1 + PowerSeries.X) ^ p - 1 := by
  unfold phibY
  rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_one, add_comm]

theorem phib_monic [Nontrivial O] (p : ℕ) (hp : p.Prime) :
    (phibY O p).Monic ∧ (phibY O p).natDegree = p := by
  have h1 : ((Polynomial.X + 1 : Polynomial O) ^ p).Monic := by
    have := (Polynomial.monic_X_add_C (1 : O)).pow p
    simpa using this
  have h2 : ((Polynomial.X + 1 : Polynomial O) ^ p).natDegree = p := by
    have := (Polynomial.monic_X_add_C (1 : O)).natDegree_pow p
    rw [Polynomial.natDegree_X_add_C, mul_one] at this
    simpa using this
  have h3 : (1 : Polynomial O).degree < ((Polynomial.X + 1 : Polynomial O) ^ p).degree := by
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree h1.ne_zero, h2]
    exact_mod_cast hp.pos
  refine ⟨h1.sub_of_left h3, ?_⟩
  unfold phibY
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, h2]
  rw [h2, Polynomial.natDegree_one]
  exact hp.pos

theorem phib_dist [Nontrivial O] (p : ℕ) (hp : p.Prime) :
    (phibY O p).IsDistinguishedAt (Ideal.span {((p : ℕ) : O)}) := by
  refine ⟨⟨fun {k} hk => ?_⟩, (phib_monic p hp).1⟩
  rw [(phib_monic p hp).2] at hk
  unfold phibY
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
  by_cases h0 : k = 0
  · subst h0
    simp
  · rw [if_neg h0, sub_zero]
    exact Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast (hp.dvd_choose_self h0 hk))

theorem phib_div (p : ℕ) (hp : p.Prime) [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    (f : PowerSeries O) : ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < (p : WithBot ℕ) ∧
      f = ((1 + PowerSeries.X) ^ p - 1) * q + (r : PowerSeries O) := by
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨0, 0, by simp, Subsingleton.elim _ _⟩
  have hI : Ideal.span {((p : ℕ) : O)} ≠ ⊤ := by
    intro h
    have hH : IsHausdorff (Ideal.span {((p : ℕ) : O)}) O := inferInstance
    rw [h] at hH
    exact not_subsingleton O hH.subsingleton
  have H := phib_dist (O := O) p hp
  have hord : (phibY O p).natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map
    (phibY O p : PowerSeries O) 1
    (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  have Hd := (H.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod f
  refine ⟨(H.isWeierstrassDivisorAt hI).div f, (H.isWeierstrassDivisorAt hI).mod f, ?_, ?_⟩
  · have := Hd.degree_lt
    rw [← hord, (phib_monic p hp).2] at this
    exact this
  · rw [← phib_coe (O := O) p]
    exact Hd.eq_mul_add

theorem phib_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (x : O) :
    φ (PowerSeries.C x) = PowerSeries.C x := by
  have : PowerSeries.C x = algebraMap O (PowerSeries O) x := by simp
  rw [this, AlgHom.commutes]

theorem phib_shift (φ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℕ → O) :
    φ (PowerSeries.mk c) =
      PowerSeries.C (c 0) + φ PowerSeries.X * φ (PowerSeries.mk fun j => c (j + 1)) := by
  have h := PowerSeries.eq_X_mul_shift_add_const (PowerSeries.mk c)
  have h1 : (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (PowerSeries.mk c)) =
      PowerSeries.mk fun j => c (j + 1) := by
    ext
    simp
  have h2 : PowerSeries.constantCoeff (PowerSeries.mk c) = c 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  rw [h1, h2] at h
  conv_lhs => rw [h]
  rw [map_add, map_mul, phib_C]
  ring

theorem phib_poly (r : Polynomial O) (p : ℕ) (h : r.degree < (p : WithBot ℕ)) :
    (r : PowerSeries O) = ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * PowerSeries.C (r.coeff k) := by
  ext m
  rw [Polynomial.coeff_coe, map_sum,
    Fin.sum_univ_eq_sum_range
      (fun k => PowerSeries.coeff m (PowerSeries.X ^ k * PowerSeries.C (r.coeff k))) p]
  simp_rw [mul_comm (PowerSeries.X ^ _) (PowerSeries.C _), PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    exact_mod_cast not_lt.1 (fun hlt => hm (Finset.mem_range.2 hlt))

theorem phib_main (p : ℕ) (hp : p.Prime) [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : PowerSeries O) :
    ∃ e : Fin p → PowerSeries O, a = ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (e k) := by
  choose Dv Rm hDR using fun f : PowerSeries O => phib_div p hp f
  set Y : PowerSeries O := (1 + PowerSeries.X) ^ p - 1 with hY
  let qs : ℕ → PowerSeries O := fun m => Dv^[m] a
  let S : ℕ → PowerSeries O := fun m => ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
    φ (PowerSeries.mk fun j => (Rm (qs (j + m))).coeff k)
  have hq : ∀ m, qs m = Y * qs (m + 1) + (Rm (qs m) : PowerSeries O) := by
    intro m
    have := (hDR (qs m)).2
    have e : qs (m + 1) = Dv (qs m) := Function.iterate_succ_apply' Dv m a
    rw [e]
    exact this
  have hS : ∀ m, S m = Y * S (m + 1) + (Rm (qs m) : PowerSeries O) := by
    intro m
    rw [phib_poly _ p (hDR (qs m)).1]
    simp only [S]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phib_shift, hφ, zero_add]
    have : (fun j => (Rm (qs (j + 1 + m))).coeff (k : ℕ)) =
        fun j => (Rm (qs (j + (m + 1)))).coeff (k : ℕ) := by
      funext j
      rw [add_assoc, add_comm 1 m]
    rw [this]
    ring
  have hd : ∀ m, qs 0 - S 0 = Y ^ m * (qs m - S m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, hq m, hS m, pow_succ]
      ring
  have hXY : PowerSeries.X ∣ Y := by
    rw [PowerSeries.X_dvd_iff, hY]
    simp
  refine ⟨fun k => PowerSeries.mk fun j => (Rm (qs j)).coeff k, ?_⟩
  have h0 : qs 0 - S 0 = 0 := by
    ext m
    have h1 : PowerSeries.X ^ (m + 1) ∣ qs 0 - S 0 := by
      rw [hd (m + 1)]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXY _) _
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 h1 m (Nat.lt_succ_self m)
  exact sub_eq_zero.1 h0

end PhiB

section PhiBW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem PhiBasis_of (W : LocWach PD LL O v n)
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] : PhiBasis W := by
  intro a
  have hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
  choose e he using fun i : ZMod n => phib_main PD.p PD.hp W.φ₀ hφ (a i)
  refine ⟨fun k j => e (j + 1) k, ?_⟩
  funext i
  rw [Finset.sum_apply, he i]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = PowerSeries.X ^ (k : ℕ) * W.φ₀ (e (i - 1 + 1) k)
  rw [sub_add_cancel]

end PhiBW

section PhiBC

theorem phib_smodeq {M : Type} [CommRing M] (c x y : M) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {c}) ^ k • ⊤ : Submodule M M)] ↔ c ^ k ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem phib_complete {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) :
    IsAdicComplete (Ideal.span {algebraMap R M ϖ}) M := by
  have key : ∀ (x : M) (k : ℕ), (algebraMap R M ϖ) ^ k ∣ x ↔ ∀ j, ϖ ^ k ∣ b.equivFun x j := by
    intro x k
    constructor
    · rintro ⟨z, rfl⟩ j
      refine ⟨b.equivFun z j, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, map_smul]
      rfl
    · intro h
      choose d hd using h
      refine ⟨b.equivFun.symm d, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      rw [hd j]
      rfl
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.equivFun.injective
    rw [map_zero]
    funext j
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) R)
    intro k
    rw [phib_smodeq, sub_zero]
    have h := hx k
    rw [phib_smodeq, sub_zero] at h
    exact (key x k).1 h j
  · intro f hf
    have hc : ∀ j, ∃ L : R, ∀ k,
        b.equivFun (f k) j ≡ L [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule R R)] := by
      intro j
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) R)
      intro m k hmk
      rw [phib_smodeq]
      have h := hf hmk
      rw [phib_smodeq] at h
      have h' := (key _ m).1 h j
      rwa [map_sub] at h'
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun k => ?_⟩
    rw [phib_smodeq, key]
    intro j
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply]
    exact (phib_smodeq _ _ _ _).1 (hL j k)

theorem phib_OL_complete {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
  have h1 : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ℤ_[l] ↥LL.1) ℤ_[l] ↥LL.1)
  have h3 : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  have h4 : Module.IsTorsionFree ℤ_[l] ↥(OL LL) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (zl_inj_O LL)
  have h5 : Module.Free ℤ_[l] ↥(OL LL) := Module.free_of_finite_type_torsion_free'
  have h6 : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h7 := phib_complete ((l : ℕ) : ℤ_[l]) (Module.finBasis ℤ_[l] ↥(OL LL))
  rwa [map_natCast] at h7

end PhiBC

section PhiI1

variable {O : Type} [CommRing O]

theorem phii_shift (φ : PowerSeries O →ₐ[O] PowerSeries O) (f : PowerSeries O) :
    φ f = PowerSeries.C (PowerSeries.constantCoeff f) +
      φ PowerSeries.X * φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) f) := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
  rw [map_add, map_mul, phib_C]
  ring

theorem phii_step (p : ℕ) (hp : p.Prime) [IsHausdorff (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : Fin p → PowerSeries O) (h : ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0) :
    (∀ k, PowerSeries.constantCoeff (a k) = 0) ∧
      ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
        φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (a k)) = 0 := by
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨fun k => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hI : Ideal.span {((p : ℕ) : O)} ≠ ⊤ := by
    intro h'
    have hH : IsHausdorff (Ideal.span {((p : ℕ) : O)}) O := inferInstance
    rw [h'] at hH
    exact not_subsingleton O hH.subsingleton
  have H := phib_dist (O := O) p hp
  have hord : (phibY O p).natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map
    (phibY O p : PowerSeries O) 1
    (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  have hord' := (phib_monic (O := O) p hp).2.symm.trans hord
  set r : Polynomial O := ∑ k : Fin p,
    Polynomial.C (PowerSeries.constantCoeff (a k)) * Polynomial.X ^ (k : ℕ) with hr
  have hrd : r.degree < (p : WithBot ℕ) := Polynomial.degree_sum_fin_lt _
  have hrc : (r : PowerSeries O) = ∑ k : Fin p,
      PowerSeries.X ^ (k : ℕ) * PowerSeries.C (PowerSeries.constantCoeff (a k)) := by
    rw [hr, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, mul_comm]
  have e : (phibY O p : PowerSeries O) * (∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
      φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (a k))) + (r : PowerSeries O) =
      (phibY O p : PowerSeries O) * 0 + ((0 : Polynomial O) : PowerSeries O) := by
    rw [mul_zero, Polynomial.coe_zero, add_zero, ← h, hrc, phib_coe, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phii_shift φ (a k), hφ]
    ring
  obtain ⟨h1, h2⟩ := (H.isWeierstrassDivisorAt hI).eq_of_mul_add_eq_mul_add
    (by rw [← hord']; exact hrd) (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _) e
  refine ⟨fun k => ?_, h1⟩
  have h3 := congrArg (fun q : Polynomial O => q.coeff (k : ℕ)) h2
  simpa [hr, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using h3

theorem phii_indep (p : ℕ) (hp : p.Prime) [IsHausdorff (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : Fin p → PowerSeries O) (h : ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0) :
    ∀ k, a k = 0 := by
  have key : ∀ (m : ℕ) (a : Fin p → PowerSeries O),
      ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0 → ∀ k, PowerSeries.coeff m (a k) = 0 := by
    intro m
    induction m with
    | zero =>
      intro a h k
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (phii_step p hp φ hφ a h).1 k
    | succ m ih =>
      intro a h k
      have := ih _ (phii_step p hp φ hφ a h).2 k
      rwa [PowerSeries.coeff_mk] at this
  intro k
  ext m
  rw [map_zero]
  exact key m a h k

end PhiI1

section PhiI2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem phii_A (W : LocWach PD LL O v n) [IsHausdorff (Ideal.span {((PD.p : ℕ) : O)}) O]
    (a : Fin PD.p → LetA O n) (h : ∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k) = 0) :
    ∀ k, a k = 0 := by
  have hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
  intro k
  funext j
  have hj := congrFun h (j + 1)
  rw [Finset.sum_apply] at hj
  have e : ∀ k : Fin PD.p, ((letπ : LetA O n) ^ (k : ℕ) * W.φA (a k)) (j + 1) =
      PowerSeries.X ^ (k : ℕ) * W.φ₀ (a k j) := by
    intro k
    change PowerSeries.X ^ (k : ℕ) * W.φ₀ (a k (j + 1 - 1)) = _
    rw [add_sub_cancel_right]
  simp_rw [e] at hj
  exact phii_indep PD.p PD.hp W.φ₀ hφ (fun k => a k j) hj k

theorem phii_mod (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (a : Fin PD.p → LetA O n) (j : ℕ) (b : LetA O n)
    (h : ∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k) = ((PD.p : ℕ) : LetA O n) ^ j * b) :
    ∀ k, ∃ a' : LetA O n, a k = ((PD.p : ℕ) : LetA O n) ^ j * a' := by
  obtain ⟨e, he⟩ := PhiBasis_of W b
  have h0 : ∑ k : Fin PD.p, letπ ^ (k : ℕ) *
      W.φA (a k - ((PD.p : ℕ) : LetA O n) ^ j * e k) = 0 := by
    simp_rw [map_sub, map_mul, map_pow, map_natCast, mul_sub]
    rw [Finset.sum_sub_distrib, h, he, Finset.mul_sum]
    apply sub_eq_zero.2
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  intro k
  exact ⟨e k, sub_eq_zero.1 (phii_A W _ h0 k)⟩

theorem phii_EE (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (c : Fin PD.p → W.EE)
    (h : ∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) * W.φE (c k) = 0) :
    ∀ k, c k = 0 := by
  have claim : ∀ (j : ℕ) (k : Fin PD.p), ((PD.p : ℕ) : W.EE) ^ j ∣ c k := by
    intro j
    choose a m hm using fun k => W.EE_dense (c k) j
    set M : ℕ := ∑ k, m k with hM
    have hle : ∀ k, m k ≤ M := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hd : ∀ k, ∃ d : W.EE, c k * algebraMap (LetA O n) W.EE (letπ ^ M) =
        algebraMap (LetA O n) W.EE (a k * letπ ^ (M - m k)) + ((PD.p : ℕ) : W.EE) ^ j * d := by
      intro k
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hm k)
      refine ⟨d * algebraMap (LetA O n) W.EE (letπ ^ (M - m k)), ?_⟩
      have e1 : (letπ : LetA O n) ^ M = letπ ^ (m k) * letπ ^ (M - m k) := by
        rw [← pow_add, Nat.add_sub_cancel' (hle k)]
      rw [e1, map_mul, map_mul]
      linear_combination (algebraMap (LetA O n) W.EE (letπ ^ (M - m k))) * hd
    choose d hd using hd
    have h1 : algebraMap (LetA O n) W.EE
        (∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k * letπ ^ (M - m k))) =
        ((PD.p : ℕ) : W.EE) ^ j *
          (-∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) * W.φE (d k)) := by
      have h2 : ∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) *
          W.φE (c k * algebraMap (LetA O n) W.EE (letπ ^ M)) = 0 := by
        simp_rw [map_mul, ← mul_assoc]
        rw [← Finset.sum_mul, h, zero_mul]
      simp_rw [hd, map_add, map_mul, map_pow, map_natCast, mul_add] at h2
      rw [Finset.sum_add_distrib] at h2
      rw [map_sum, mul_neg, Finset.mul_sum]
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hext : ∀ a : LetA O n, algebraMap (LetA O n) W.EE (W.φA a) =
            W.φE (algebraMap (LetA O n) W.EE a) := fun a => (W.φE_ext a).symm
        rw [map_mul, map_pow, hext]
        simp only [map_mul, map_pow]
      · refine Finset.sum_congr rfl fun k _ => ?_
        ring
    obtain ⟨b, hb⟩ := W.EE_sat _ j (by rw [h1]; exact Ideal.mem_span_singleton.2 (Dvd.intro _ rfl))
    intro k
    obtain ⟨a', ha'⟩ := phii_mod W _ j b hb k
    have h3 : ((PD.p : ℕ) : W.EE) ^ j ∣ c k * algebraMap (LetA O n) W.EE (letπ ^ M) := by
      rw [hd k, ha', map_mul, map_pow, map_natCast]
      exact ⟨algebraMap (LetA O n) W.EE a' + d k, by ring⟩
    have hu : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ M)) := by
      rw [map_pow]
      exact W.EE_π.pow M
    exact (hu.dvd_mul_right).1 h3
  intro k
  have hH : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE := W.EE_complete.toIsHausdorff
  apply hH.haus
  intro j
  rw [phib_smodeq, sub_zero]
  exact claim j k

end PhiI2

section PhiI3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem phii_finite (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Module.Finite W.EE (W.DD T) := by
  obtain ⟨S, hS⟩ := W.N_fg T
  refine ⟨⟨S, top_le_iff.1 fun y _ => ?_⟩⟩
  refine (W.N_base T hT).inductionOn y (fun y => y ∈ Submodule.span W.EE (S : Set (W.DD T)))
    (Submodule.zero_mem _) (fun m => ?_) (fun e y hy => Submodule.smul_mem _ e hy)
    (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  have hm : (m : W.DD T) ∈ Submodule.span (LetA O n) (S : Set (W.DD T)) := by rw [hS]; exact m.2
  exact Submodule.span_le_restrictScalars (LetA O n) W.EE (S : Set (W.DD T)) hm

theorem phii_basis (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    {d : ℕ} (β : Module.Basis (Fin d) W.EE (W.DD T)) (c : Fin d → W.EE)
    (h : ∑ t, c t • W.φD T (β t) = 0) : c = 0 := by
  have hfin := phii_finite W T hT
  let L : (Fin d → W.EE) →ₗ[W.EE] W.DD T := Fintype.linearCombination W.EE fun t => W.φD T (β t)
  have hL : ∀ c, L c = ∑ t, c t • W.φD T (β t) := fun c => Fintype.linearCombination_apply _ _ _
  have hφ : ∀ y, W.φD T y ∈ LinearMap.range L := by
    intro y
    refine ⟨fun t => W.φE (β.equivFun y t), ?_⟩
    rw [hL]
    conv_rhs => rw [← β.sum_equivFun y, map_sum]
    exact Finset.sum_congr rfl fun t _ => (W.φD_smul T _ _).symm
  have hN : ∀ m ∈ W.N T, m ∈ LinearMap.range L := by
    intro m hm
    obtain ⟨k, hk⟩ := W.N_φinv T m hm
    have h1 : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
        (LinearMap.range L).restrictScalars (LetA O n) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, _, rfl⟩
      exact hφ y
    have h2 : W.Q ^ k • m ∈ LinearMap.range L := h1 hk
    rw [← algebraMap_smul W.EE, map_pow] at h2
    obtain ⟨u, hu⟩ := (liftb_Q_unit W).pow k
    rw [← hu] at h2
    have h3 := (LinearMap.range L).smul_mem ((u⁻¹ : W.EEˣ) : W.EE) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  have hsurj : Function.Surjective L := by
    intro y
    exact (W.N_base T hT).inductionOn y (fun y => y ∈ LinearMap.range L)
      (Submodule.zero_mem _) (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy)
      (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  have hinj : Function.Injective (L ∘ₗ β.equivFun.toLinearMap) :=
    OrzechProperty.injective_of_surjective_endomorphism _
      (hsurj.comp β.equivFun.surjective)
  have h0 : (L ∘ₗ β.equivFun.toLinearMap) (β.equivFun.symm c) = 0 := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hL, h]
  have h4 := hinj (h0.trans (map_zero _).symm)
  have h5 := congrArg β.equivFun h4
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

theorem phii_DD (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (x : Fin PD.p → W.DD T)
    (h : ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (x k) = 0) : ∀ k, x k = 0 := by
  rcases subsingleton_or_nontrivial W.EE with hE | hE
  · have := Module.subsingleton W.EE (W.DD T)
    exact fun k => Subsingleton.elim _ _
  have hfin := phii_finite W T hT
  have hfree := (W.DD_free T).1
  let β := Module.finBasis W.EE (W.DD T)
  have hx : ∀ k, W.φD T (x k) = ∑ t, W.φE (β.equivFun (x k) t) • W.φD T (β t) := by
    intro k
    conv_lhs => rw [← β.sum_equivFun (x k), map_sum]
    exact Finset.sum_congr rfl fun t _ => W.φD_smul T _ _
  have h1 : ∑ t, (∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) *
      W.φE (β.equivFun (x k) t)) • W.φD T (β t) = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul, hx, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul, ← map_pow, algebraMap_smul]
  have h2 := phii_basis W T hT β _ h1
  intro k
  apply β.equivFun.injective
  rw [map_zero]
  funext t
  exact phii_EE W (fun k => β.equivFun (x k) t) (congrFun h2 t) k

end PhiI3

end Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

end
