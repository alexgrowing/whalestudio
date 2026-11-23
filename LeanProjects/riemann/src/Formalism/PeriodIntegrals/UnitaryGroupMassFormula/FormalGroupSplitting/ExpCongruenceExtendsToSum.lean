import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.AddPreservesExpCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.OrthogonalSplitPolarizationVanishes

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

variable {K : Type} [Field K]

def AllIn (W : Subring K) {σ : Type} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ W

theorem allIn_mul {W : Subring K} {σ : Type} {F G : MvPowerSeries σ K} (hF : AllIn W F)
    (hG : AllIn W G) : AllIn W (F * G) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hF _) (hG _)

theorem allIn_one {W : Subring K} {σ : Type} : AllIn W (1 : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact W.one_mem
  · exact W.zero_mem

theorem allIn_X {W : Subring K} {σ : Type} (s : σ) : AllIn W (MvPowerSeries.X s : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact W.one_mem
  · exact W.zero_mem

theorem allIn_pow {W : Subring K} {σ : Type} {F : MvPowerSeries σ K} (hF : AllIn W F) (n : ℕ) :
    AllIn W (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact allIn_one
  | succ n ih => rw [pow_succ]; exact allIn_mul ih hF

theorem allIn_subst_X {W : Subring K} {σ τ : Type} (r : σ → τ)
    (ha : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)))
    {H : MvPowerSeries σ K} (hH : AllIn W H) :
    AllIn W (MvPowerSeries.subst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)) H) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_subst ha]
  refine finsum_induction (p := fun x => x ∈ W) W.zero_mem (fun _ _ => W.add_mem) fun d => ?_
  rw [smul_eq_mul]
  refine W.mul_mem (hH d) ?_
  have : AllIn W (∏ s ∈ d.support, (MvPowerSeries.X (r s) : MvPowerSeries τ K) ^ (d s)) :=
    Finset.prod_induction _ (AllIn W) (fun _ _ => allIn_mul) allIn_one
      fun s _ => allIn_pow (allIn_X _) _
  exact this e

theorem expMv_eq_subst [CharZero K] {σ : Type} {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv F = PowerSeries.subst F (PowerSeries.exp K) := by
  classical
  ext α
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [coeff_expMv, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hc
    apply hn
    have hdeg : (α.sum fun _ k => k) = Finsupp.degree α := rfl
    rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      (by rw [pow_one]; exact hF) (by omega), smul_zero]

section Rename₂

variable {ι ι' : Type} [Fintype ι]

theorem hasSubst_inl : MvPowerSeries.HasSubst
    (fun j : ι ⊕ ι => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

def rho : MvPowerSeries (ι ⊕ ι) K →ₐ[K] MvPowerSeries ((ι ⊕ ι) ⊕ ι') K :=
  MvPowerSeries.substAlgHom hasSubst_inl

theorem rho_apply (F : MvPowerSeries (ι ⊕ ι) K) :
    (rho (ι' := ι') F) = MvPowerSeries.subst
      (fun j : ι ⊕ ι => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)) F := by
  exact MvPowerSeries.substAlgHom_apply _ _

theorem rho_psubst (P : PowerSeries K) {y : MvPowerSeries (ι ⊕ ι) K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (PowerSeries.subst y P) = PowerSeries.subst (rho (ι' := ι') y) P := by
  rw [rho_apply, rho_apply]
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hy)) hasSubst_inl]

theorem rho_X (j : ι ⊕ ι) :
    rho (ι' := ι') (MvPowerSeries.X j : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.X (Sum.inl j) := by
  rw [rho_apply, MvPowerSeries.subst_X hasSubst_inl]

theorem rho_C (c : K) :
    rho (ι' := ι') (MvPowerSeries.C c : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.C c := by
  have e1 : ∀ (τ : Type), (MvPowerSeries.C c : MvPowerSeries τ K) = algebraMap K (MvPowerSeries τ K) c := by
    intro τ
    rw [MvPowerSeries.algebraMap_apply]
    rfl
  rw [e1, e1, AlgHom.commutes]

theorem cc_psubst {σ : Type} (P : PowerSeries K) (hP : PowerSeries.constantCoeff P = 0)
    {y : MvPowerSeries σ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst y P) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hy)]
  refine finsum_induction (p := fun x => x = 0) rfl (fun x z hx hz => by rw [hx, hz, add_zero]) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP, zero_smul]
  · rw [map_pow, hy, zero_pow hd.ne', smul_zero]

variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0

theorem cc_add {σ : Type} {x y : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.constantCoeff (g.add x y) = 0 := by
  unfold Dat.add Dat.pt Dat.lg
  exact cc_psubst _ hex0 (by rw [map_add, cc_psubst _ hl0 hx, cc_psubst _ hl0 hy, add_zero])

theorem rho_add {x y : MvPowerSeries (ι ⊕ ι) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (g.add x y) = g.add (rho x) (rho y) := by
  unfold Dat.add Dat.pt Dat.lg
  rw [rho_psubst _ (by rw [map_add, cc_psubst _ hl0 hx, cc_psubst _ hl0 hy, add_zero]), map_add,
    rho_psubst _ hx, rho_psubst _ hy]

theorem rho_be {x y : MvPowerSeries (ι ⊕ ι) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (g.be x y) = g.be (rho x) (rho y) := by
  unfold Dat.be Dat.phAt
  rw [map_sub, map_sub, rho_psubst _ (cc_add g hex0 hl0 hx hy), rho_psubst _ hx, rho_psubst _ hy,
    rho_add g hex0 hl0 hx hy]

theorem rho_lin {κ' : Type} [Fintype κ'] (c : κ' → K) (w : κ' → MvPowerSeries (ι ⊕ ι) K)
    (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0) :
    rho (ι' := ι') (g.lin c w) = g.lin c (fun j => rho (w j)) := by
  unfold Dat.lin Dat.pt Dat.lg
  have hs : ∀ (σ : Type) (v : κ' → MvPowerSeries σ K), (∀ j, MvPowerSeries.constantCoeff (v j) = 0) →
      MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (v j) g.l) = 0 := by
    intro σ v hv
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_psubst _ hl0 (hv j), mul_zero]
  have e : rho (ι' := ι') (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (w j) g.l) =
      ∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (rho (ι' := ι') (w j)) g.l := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, rho_C, rho_psubst _ (hw j)]
  rw [rho_psubst _ (hs _ w hw), e]

theorem rho_PhOn {κ : Type} [Fintype κ] (b : ι ⊕ ι → κ → K × K) :
    rho (ι' := ι') (g.PhOn b) = g.PhV b (fun e => MvPowerSeries.X (Sum.inl e)) := by
  unfold Dat.PhOn Dat.PhV
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hX : ∀ e : ι ⊕ ι, MvPowerSeries.constantCoeff (MvPowerSeries.X e : MvPowerSeries (ι ⊕ ι) K) = 0 :=
    fun e => MvPowerSeries.constantCoeff_X e
  have hlin : MvPowerSeries.constantCoeff
      (g.lin (fun e => (b e k).1) (fun e => (MvPowerSeries.X e : MvPowerSeries (ι ⊕ ι) K))) = 0 := by
    unfold Dat.lin Dat.pt Dat.lg
    refine cc_psubst _ hex0 ?_
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_psubst _ hl0 (hX j), mul_zero]
  unfold Dat.phAt
  rw [rho_psubst _ hlin, rho_lin g hex0 hl0 _ _ hX]
  simp only [rho_X]

theorem rho_beSum :
    rho (ι' := ι') (g.beSum ι) = ∑ e : ι, g.be (MvPowerSeries.X (Sum.inl (Sum.inl e)))
      (MvPowerSeries.X (Sum.inl (Sum.inr e))) := by
  unfold Dat.beSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [rho_be g hex0 hl0 (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _), rho_X, rho_X]

omit hex0 hl0 in
theorem simeqW_rho [CharZero K] {W : Subring K} {f h : MvPowerSeries (ι ⊕ ι) K}
    (hfh : SimeqW W f h) : SimeqW W (rho (ι' := ι') f) (rho h) := by
  unfold SimeqW at hfh ⊢
  obtain ⟨h0, hW⟩ := hfh
  have hcc : ∀ d : MvPowerSeries (ι ⊕ ι) K, MvPowerSeries.constantCoeff d = 0 →
      MvPowerSeries.constantCoeff (rho (ι' := ι') d) = 0 := by
    intro d hd
    rw [rho_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_subst hasSubst_inl]
    refine finsum_induction (p := fun x => x = 0) rfl (fun x z hx hz => by rw [hx, hz, add_zero])
      fun e => ?_
    by_cases he : e = 0
    · subst he
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hd, zero_smul]
    · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact he (Finsupp.ext hc)
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
        Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs)
          (by rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hs]), smul_zero]
  have hsub : rho (ι' := ι') f - rho h = rho (f - h) := (map_sub _ _ _).symm
  rw [hsub]
  refine ⟨hcc _ h0, fun n => ?_⟩
  rw [expMv_eq_subst (hcc _ h0), ← rho_psubst _ h0, ← expMv_eq_subst h0, rho_apply]
  exact allIn_subst_X Sum.inl hasSubst_inl hW n

end Rename₂

theorem expCongruenceExtendsToSum : S4 := by
  intro K _ _ W g hex0 hinv κ ι ι' _ _ _ b b' h
  have hl0 := (compositionalInverseSymm K g.l g.ex hex0 hinv).1
  have h1 := simeqW_rho (ι' := ι') h
  rw [rho_PhOn g hex0 hl0, rho_beSum g hex0 hl0] at h1
  exact h1

end PI.FglPhSplit.Wk

end
