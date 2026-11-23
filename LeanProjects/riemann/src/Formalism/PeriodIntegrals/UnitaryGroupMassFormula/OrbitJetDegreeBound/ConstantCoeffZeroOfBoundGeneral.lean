import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.UnivEqBiUnion

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries PI.OrbJet PI.OrbJet.OrbW PI.OrbShared PI.OrbJet.OJ

section Lin

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} {l : ℕ} [Fact l.Prime]

theorem applyAt0_congr (T T' : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ)
    (h : ∀ μ ∈ P.support, coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T') :
    applyAt0 N0 N1 l T P = applyAt0 N0 N1 l T' P := by
  unfold OJ.applyAt0
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [h μ hμ]

theorem applyAt0_zero_left (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (0 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) P = 0 := by
  unfold applyAt0
  simp

theorem applyAt0_add_left (T T' : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (T + T') P = applyAt0 N0 N1 l T P + applyAt0 N0 N1 l T' P := by
  unfold OJ.applyAt0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_add, mul_add, map_add]

theorem applyAt0_smul_left (c : ℂ_[l]) (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (c • T) P = c • applyAt0 N0 N1 l T P := by
  unfold OJ.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPowerSeries.coeff_smul, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem applyAt0_sum_left {ι : Type*} (S : Finset ι) (c : ι → ℂ_[l]) (T : ι → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (∑ i ∈ S, c i • T i) P = ∑ i ∈ S, c i • applyAt0 N0 N1 l (T i) P := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact applyAt0_zero_left P
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, applyAt0_add_left, applyAt0_smul_left, ih]

end Lin

theorem norm_coeff_monomial_one {σ : Type*} {l : ℕ} [Fact l.Prime] (k m : σ →₀ ℕ) :
    ‖coeff m (monomial k (1 : ℂ_[l]))‖ ≤ 1 := by
  rw [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem constantCoeff_zero_of_bound_general (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : OJ.B3 l d be) :
    constantCoeff be = 0 := by
  by_contra hne
  have h1 := (h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
  apply h1
  simp [OJ.bideg]

variable (D : D7) (p : ℕ) [Fact p.Prime]

def Fk (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (k : ZMod (nP D p) × Fin N0 × Fin N1 →₀ ℕ) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  Tri.sol ep (fun w => C ep * jetLogG p (nP D p) w) (monomial k 1 * Eorb D p (N0 := N0) (N1 := N1) sg be)

def Pm (N0 N1 : ℕ) (ep : ℂ_[p]) (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (m : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∏ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (Fk D p N0 N1 ep (sg r) (be r) (resM D p r m))

theorem subst_Pm {N0 N1 : ℕ} (ep : ℂ_[p]) (hep : ep ≠ 0) {R : Finset (Pl D)} (hR : IsReps D p R)
    (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) (m : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) (Pm D p N0 N1 ep R sg be m) =
      monomial m 1 * subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)) := by
  have hG := (isTri_log D p (β := Fin N0 × Fin N1) ep).hasSubst
  rw [Pm, ← coe_substAlgHom hG, map_prod, E_eq D p R sg be hcc, mono_eq D p hR m, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [coe_substAlgHom, subst_rename, Fk, Tri.subst_sol hep (isTri_jet p (nP D p) ep), map_mul]

theorem orbAddUp_main : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E := by
  intro D E p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  obtain ⟨hep, _, hB⟩ := hbe
  have hcc : ∀ r ∈ R, constantCoeff (be r) = 0 := fun r hr => constantCoeff_zero_of_bound_general p (nP D p) (be r) (hB r hr).2.2.1
  have hep0 : ep ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hep
    exact zero_ne_one hep
  obtain ⟨U, hU, hEq⟩ := hTh
  have hTG := isTri_log D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))) ep
  have hFk : ∀ r ∈ R, ∀ k, KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s => E.nu u i (orbMap D p r s))
      (Fk D p (D.R.N i) (D.R.N (i + 1)) ep (sg r) (be r) k) (β r) := by
    intro r hr k
    apply hβ r hr
    refine ⟨monomial k 1, fun m => norm_coeff_monomial_one k m, ?_⟩
    · exact Tri.subst_sol hep0 (isTri_jet p (nP D p) ep) _
  have hPk : ∀ m, KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) (Pm D p _ _ ep R sg be m) (∑ r ∈ R, β r) :=
    fun m => kval_prod D p hR _ _ β (fun r hr => hFk r hr _)
  intro I mx
  set G := Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I with hGdef
  set n := G.support.sup (fun μ => (Finsupp.sumFinsuppEquivProdFinsupp μ).2.degree) + 1 with hn
  set S := (Finsupp.finite_of_degree_lt (σ := Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) n).toFinset with hS
  set Th' := ∑ m ∈ S, coeff m U • Pm D p _ _ ep R sg be m with hTh'
  set Eall := subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1)))) (OJ.expS ℂ_[p] (beAll D p R sg be))
    with hEall
  have hsub : subst (fun v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) => C ep * logPl D p v) (Th - Th') =
      (U - ∑ m ∈ S, monomial m (coeff m U)) * Eall := by
    rw [subst_sub hTG.hasSubst, hEq, hTh', ← coe_substAlgHom hTG.hasSubst, map_sum]
    simp_rw [map_smul, coe_substAlgHom, subst_Pm D p ep hep0 hR sg be hcc]
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_C_mul, ← mul_assoc, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  have hagree : ∀ κ : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ, κ.degree < n →
      coeff κ Th = coeff κ Th' := by
    have hv := Tri.vanish_of_subst hep0 hTG (Th - Th') n (by
      intro κ hκ
      rw [hsub, coeff_mul]
      refine Finset.sum_eq_zero fun ab hab => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hdeg : ab.1.degree < n := by
        have : κ.degree = ab.1.degree + ab.2.degree := by rw [← hab, map_add]
        omega
      have hmem : ab.1 ∈ S := by
        rw [hS, Set.Finite.mem_toFinset]
        exact hdeg
      rw [map_sub, map_sum, Finset.sum_eq_single ab.1]
      · rw [coeff_monomial, if_pos rfl, sub_self, zero_mul]
      · intro b _ hb
        rw [coeff_monomial, if_neg (Ne.symm hb)]
      · intro h; exact absurd hmem h)
    intro κ hκ
    have := hv κ hκ
    rwa [map_sub, sub_eq_zero] at this
  have hjet : applyAt0 (D.R.N i) (D.R.N (i + 1)) p Th G = applyAt0 (D.R.N i) (D.R.N (i + 1)) p Th' G := by
    refine applyAt0_congr Th Th' G fun μ hμ => hagree _ ?_
    rw [hn]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun μ => (Finsupp.sumFinsuppEquivProdFinsupp μ).2.degree) hμ)
  rw [hjet, hTh', applyAt0_sum_left, MvPolynomial.coeff_sum]
  have hpos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpos.le _) fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  refine (norm_mul_le _ _).trans ?_
  calc ‖coeff m U‖ * ‖MvPolynomial.coeff mx (applyAt0 (D.R.N i) (D.R.N (i + 1)) p (Pm D p _ _ ep R sg be m) G)‖
      ≤ 1 * (p : ℝ) ^ (-∑ r ∈ R, β r) :=
        mul_le_mul (hU m) (hPk m I mx) (norm_nonneg _) zero_le_one
    _ = (p : ℝ) ^ (-∑ r ∈ R, β r) := one_mul _

end PI.OrbJet.AU

end
