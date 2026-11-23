import Formalism.LocalToGlobal.InertKernelTheory.StatementLoc
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.L2.PairingIndexBounds.PowerSeriesNecessity Finset

attribute [local instance] Formalism.L2.G.Pend.wittFractionAlgebraCp

namespace Formalism.L2.KerInert.Ent

variable {p : ℕ} [Fact p.Prime]

theorem geZ_iff (x : ℂ_[p]) : GeZ x ↔ x ∈ Formalism.L2.G.Pend.OcC p := by
  constructor
  · intro h
    have := h 0 1 one_pos (by simp)
    simpa using this
  · intro hx a b _ hab
    have ha : 0 ≤ -a := by
      have : (a : ℝ) ≤ 0 := by simpa using hab
      have : a ≤ 0 := by exact_mod_cast this
      omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hk, zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ hx b) (Subring.pow_mem _ (natCast_mem _ p) k)

def GeP {τ : Type} (a : MvPolynomial τ ℂ_[p]) : Prop := ∀ n, MvPolynomial.coeff n a ∈ Formalism.L2.G.Pend.OcC p

theorem geP_one {τ : Type} : GeP (1 : MvPolynomial τ ℂ_[p]) := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem geP_mul {τ : Type} {a b : MvPolynomial τ ℂ_[p]} (ha : GeP a) (hb : GeP b) : GeP (a * b) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact Subring.sum_mem _ fun xy _ => Subring.mul_mem _ (ha _) (hb _)

theorem geP_prod {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ ℂ_[p]) (h : ∀ i ∈ s, GeP (a i)) :
    GeP (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (geP_one : GeP (1 : MvPolynomial τ ℂ_[p]))
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact geP_mul (h x (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem geP_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ ℂ_[p]) (h : ∀ i ∈ s, GeP (a i)) :
    GeP (∑ i ∈ s, a i) := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact Subring.sum_mem _ fun i hi => h i hi n

theorem geP_smul {τ : Type} {a : MvPolynomial τ ℂ_[p]} {c : ℂ_[p]} (hc : c ∈ Formalism.L2.G.Pend.OcC p) (h : GeP a) :
    GeP (c • a) := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact Subring.mul_mem _ hc (h n)

variable (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p))

def PhB (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))

def FC (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  MvPowerSeries.map (algebraMap (K0 p) ℂ_[p]) (expS p (-PhB X be j v))

theorem PhB_supp (j : ℕ) (v : X.Pl) : PhB X be j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold PhB
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem FC_supp (j : ℕ) (v : X.Pl) : FC X be j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (PhB_supp X be j v)))

theorem PhB_const (hbe : BeProp p be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (PhB X be j v) = 0 := by
  unfold PhB
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

def ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) ℂ_[p]) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) ℂ_[p])) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (ploc X j I i0 v) := by
  unfold PIvS ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  rw [RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i i'
  simp [en_mapP, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, map_sum]

theorem geP_applyD_prod_FC_mul (j : ℕ) (hLow : ∀ v, LowZC X be j v)
    (U1 : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]) (hU1 : IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] U1))
    (I : X.ColCh j) :
    GeP (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j ((∏ v, FC X be j v) * U1))) := by
  classical
  have e1 : X.ThZA ℂ_[p] j ((∏ v, FC X be j v) * U1) = (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) *
      MvPowerSeries.subst (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) (inParamK p ℂ_[p] U1) := by
    rw [en_ThZA_mul, en_ThZA_prod]
    congr 1
    conv_lhs => rw [← en_Ec_inParamK p ℂ_[p] U1]
    unfold Sys.ThZA
    rw [MvPowerSeries.subst_comp_subst_apply (en_Ec_hs p ℂ_[p]) (en_coordZA_hs X ℂ_[p] j)]
  have ha : MvPowerSeries.HasSubst (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      MvPowerSeries.constantCoeff_subst_eq_zero (en_coordZA_hs X ℂ_[p] j) (en_coordZA_zero X ℂ_[p] j)
        (en_Ec_zero p ℂ_[p] i)
  rw [en_applyD_eq, e1]
  obtain ⟨B, hB⟩ := Gen.jp_subst_expand (en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (X.PI j I fun _ => 0))
    (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) ha (inParamK p ℂ_[p] U1)
  rw [hB]
  refine geP_sum _ _ fun β _ => geP_smul (hU1 β) ?_
  set Ub : X.Pl → MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] := fun v =>
    ∏ i ∈ β.support.filter (fun i => en_pi X j i = v), (en_Ec p ℂ_[p] i) ^ (β i) with hUb
  have e2 : (β.prod fun i e => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i) ^ e) = ∏ v, X.ThZA ℂ_[p] j (Ub v) := by
    unfold Finsupp.prod
    rw [← Finset.prod_fiberwise β.support (en_pi X j)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hUb, en_ThZA_prod]
    exact Finset.prod_congr rfl fun i _ => (en_ThZA_pow X ℂ_[p] j _ _).symm
  have e3 : (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) * ∏ v, X.ThZA ℂ_[p] j (Ub v) =
      ∏ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (en_ThZA_mul X ℂ_[p] j _ _).symm
  have hG : ∀ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v := fun v =>
    en_ThZA_supp X ℂ_[p] j v (Subring.mul_mem _ (FC_supp X be j v) (Subring.prod_mem _ fun i hi =>
      Subring.pow_mem _ (by
        have := en_Ec_supp p ℂ_[p] (en_pi X j) i
        rw [(Finset.mem_filter.1 hi).2] at this
        exact this) _))
  have e4 : ∏ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) =
      ∏ v, Gen.atP v (Gen.resP v (X.ThZA ℂ_[p] j (FC X be j v * Ub v))) :=
    Finset.prod_congr rfl fun v _ => Gen.eq_atP v _ (hG v)
  have e5 : en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (X.PI j I fun _ => 0) =
      ∏ v, MvPolynomial.rename (Sigma.mk v) (ploc X j I (fun _ => 0) v) := by
    rw [PI_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ => mapP_PIvS X j I _ v
  rw [e2, e3, e4, e5, Gen.jp_prod]
  refine geP_prod _ _ fun v _ => ?_
  have e6 : Gen.jp (ploc X j I (fun _ => 0) v) (Gen.resP v (X.ThZA ℂ_[p] j (FC X be j v * Ub v))) =
      applyD (X.PIv j I v) (X.ThZA ℂ_[p] j (FC X be j v * Ub v)) := by
    rw [← PIvS_zero X j I v, en_applyD_eq, mapP_PIvS]
    conv_rhs => rw [Gen.eq_atP v _ (hG v)]
    rw [Gen.jp_rename]
  rw [e6]
  have hint : IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] (Ub v)) := by
    rw [hUb, en_inParamK_prod]
    refine en_IntR_prod _ _ fun i _ => ?_
    rw [en_inParamK_pow, en_inParamK_Ec]
    exact en_IntR_pow (en_IntR_X i) _
  exact fun n => (geZ_iff _).1 (hLow v (Ub v) hint I n)

theorem first_kernel_product_factor (j : ℕ) {Th : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]}
    (hK : ExtensionGeneratorCondition p ℂ_[p] (Formalism.L2.G.Pend.OcC p) be Th) :
    ∃ U1 : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] U1) ∧
      Th = (∏ v, FC X be j v) * U1 := by
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hK
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, PhB X be j v := by
    unfold PhB
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, PhB X be j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) ℂ_[p]) (expS p (-(Ph - ∑ v, PhB X be j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, PhB X be j v))) = expK (inParam p (-(Ph - ∑ v, PhB X be j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) ℂ_[p], ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    show ‖Formalism.L2.G.Pend.k0ToC p (algebraMap (WW p) (K0 p) _)‖ ≤ 1
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.norm_wToC_le p _
  · have e2 : -Ph = ∑ v, (-PhB X be j v) + -(Ph - ∑ v, PhB X be j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-PhB X be j v)) * expS p (-(Ph - ∑ v, PhB X be j v)) := by
      have a1 : expK (∑ v, (-PhB X be j v) + -(Ph - ∑ v, PhB X be j v)) =
          expK (∑ v, (-PhB X be j v)) * expK (-(Ph - ∑ v, PhB X be j v)) :=
        expK_add (by
          rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, PhB_const X be hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-PhB X be j v)) = ∏ v, expK (-PhB X be j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, PhB_const X be hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

theorem ent_of_K1gen (j : ℕ) (hLow : ∀ v, LowZC X be j v) {Th : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]}
    (hK : ExtensionGeneratorCondition p ℂ_[p] (Formalism.L2.G.Pend.OcC p) be Th) (I : X.ColCh j) (n : X.FrI j →₀ ℕ) :
    GeZ (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j Th))) := by
  obtain ⟨U1, hU1, rfl⟩ := first_kernel_product_factor X be j hK
  exact (geZ_iff _).2 (geP_applyD_prod_FC_mul X be j hLow U1 hU1 I n)

end Formalism.L2.KerInert.Ent

namespace Formalism.L2.KerInert

theorem admissible_third_of_low_kernel_law : Adm3OfK1LowerBound := by
  intro p _ X _ E hfin be T pos F hLow H j hj L0 hL0 La' hL' φ I n
  exact Ent.ent_of_K1gen X be j (hLow j hj) (H j hj L0 hL0 La' hL' φ) I n

open Formalism.L2.G.Pend in

theorem low_order_vanishing_of_admissible (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p}
    (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X (pendT X E hfin hst hLT pos F) → ∀ j < X.mm, ∀ v, LowZC X (beLT hLT) j v :=
  fun h j hj v => h v j hj

open Formalism.L2.G.Pend in

theorem admissible_third_of_second_eleventh (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p}
    (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.MainNotions.FormalGroupSystem.adm2b D X (pendT X E hfin hst hLT pos F) → Formalism.MainNotions.FormalGroupSystem.adm11 D X (pendT X E hfin hst hLT pos F) →
      Formalism.MainNotions.FormalGroupSystem.adm3 D X (pendT X E hfin hst hLT pos F) :=
  fun h2b h11 => (adm_three_iff_representative D X E hfin hst hLT pos F).2
    (admissible_third_of_low_kernel_law X E hfin _ pos F (low_order_vanishing_of_admissible D X E hfin hst hLT pos F h11)
      ((adm_two_pendant_iff_representative D X E hfin hst hLT pos F).1 h2b))

end Formalism.L2.KerInert
