import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdRenameExpJetSeries

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem bound_place {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (β : Pl D → ℝ)
    (hβ : ∀ z, OneGe E p h5 u i z (β z)) (c : ℂ_[p]) (hc : ‖c‖ = 1) (ep sg : Pl D → ℂ_[p])
    (hep : ∀ z, ‖ep z‖ = 1) (hsg : ∀ z, sg z = 1 ∨ sg z = -1) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : ∀ z, OJ.B1 p 2 (be z) ∧ OJ.B2 p 2 (be z) ∧ OJ.B3 p 2 (be z) ∧ OJ.B4 p 2 (be z))
    (I : ColChoice (D.R.N (i + 1)) (E.nu u i)) (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
    (z : Pl D) (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ) :
    ‖MvPolynomial.coeff m' (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
      (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (T1 (D.R.N i) (D.R.N (i + 1)) c (ep z) (sg z) (be z) (kz D z k)))
      (∏ c' : Fin ((E.nu u i z).rowLen 0), minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')))‖
      ≤ (p : ℝ) ^ (-β z) := by
  have hadm := admissible_jet_term E h5 u i z c hc (ep z) (sg z) (hep z) (hsg z) (be z) (hbe z) (kz D z k)
  have hK := hβ z _ hadm
  have hP : MvPolynomial.rename (xzMap (N0 := D.R.N i) (N1 := D.R.N (i + 1)) (ptE D z))
      (Gxz (D.R.N i) (D.R.N (i + 1)) (fun _ : ZMod 1 => E.nu u i z) (fun _ c' => I z c')) =
      ∏ c' : Fin ((E.nu u i z).rowLen 0),
        minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := by
    simp only [Gxz, map_prod, rename_minorXZ, ptE_apply, Finset.prod_const, Finset.card_univ,
      ZMod.card, pow_one]
  rw [← hP, applyAt0_rename]
  exact norm_coeff_rename_le _ _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun m => hK _ m) m'

theorem order_psi_gt (c : ℂ_[p]) {τ : Type*} [Finite τ] (n : ℕ) (V X : MvPowerSeries τ ℂ_[p])
    (hV : (n : ℕ∞) < V.order) : (n : ℕ∞) < (subst (psiA p c) (V * X)).order := by
  have hs := hs_psiA (p := p) c (τ := τ)
  have h1 : (1 : ℕ∞) ≤ ⨅ v : τ, (psiA p c v).order := by
    refine le_iInf fun v => ?_
    refine MvPowerSeries.le_order fun d hd => ?_
    have hd1 : Finsupp.degree d < 1 := by exact_mod_cast hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd1)
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact cc_psubst (p := p) _ (by simp) _ (Ep_const (p := p))
  have h2 : V.order ≤ (V * X).order :=
    le_trans le_self_add MvPowerSeries.le_order_mul
  calc (n : ℕ∞) < V.order := hV
    _ ≤ (V * X).order := h2
    _ = 1 * (V * X).order := (one_mul _).symm
    _ ≤ (⨅ v : τ, (psiA p c v).order) * (V * X).order :=
      mul_le_mul_of_nonneg_right h1 (by simp)
    _ ≤ (subst (psiA p c) (V * X)).order := MvPowerSeries.le_order_subst hs _

theorem orbitsAddAtConjugate (D : D7) (E : Ent D) : OrbitsAddAtConjugate E := by
  intro p _ h5 hn u i _ β hβ Th hB I m
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hB
  have hep0' : ep0 ≠ 0 := by
    rintro rfl
    simp at hep0
  have hcc : ∀ z, constantCoeff (be z) = 0 := fun z => constantCoeff_zero_of_bound_two (be z) (hbe z).2.2.1
  have hphi : (fun v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) =>
      MvPowerSeries.C ep0 * logPl D p v) = phiA p ep0 := by
    funext v
    rw [logPl_one (p := p) D hn v]
    rfl
  have hEq' : subst (phiA p ep0) Th =
      U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) := by
    rw [← hphi]
    exact hEq
  have hTh : Th = subst (psiA p ep0)
      (U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be))) := by
    rw [← hEq', psi_phi (p := p) ep0 hep0' Th]
  have hdisj : ((Finset.univ : Finset (Pl D)) : Set (Pl D)).PairwiseDisjoint
      (fun z : Pl D => ({z} : Set (Pl D))) := by
    intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  have hprod : ∀ (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
      (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ),
      ‖MvPolynomial.coeff m' (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I))‖ ≤ (p : ℝ) ^ (-∑ z, β z) := by
    intro k m'
    have hT : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        SerIn {v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) | v.1 ∈ ({z} : Set (Pl D))}
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k))) := by
      intro z _
      refine SerIn.mono ?_ (serIn_rename (ptE D z) _)
      rintro v ⟨s, hs⟩
      rw [ptE_apply] at hs
      exact hs.symm
    have hP : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        (∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) ∈
        MvPolynomial.supported ℤ (xzLetter ⁻¹' ({z} : Set (Pl D))) := by
      intro z _
      exact Subalgebra.prod_mem _ fun c' _ => minorXZ_supported _ _ _
    have hG : Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I = ∏ z ∈ (Finset.univ : Finset (Pl D)),
        ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := rfl
    have happ : applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (∏ z ∈ (Finset.univ : Finset (Pl D)), ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) =
        ∏ z ∈ (Finset.univ : Finset (Pl D)), applyAt0 (D.R.N i) (D.R.N (i + 1)) p
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
          (∏ c' : Fin ((E.nu u i z).rowLen 0),
            minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) :=
      applyAt0_prod (l := p) _ _ hdisj _ _ hT hP
    rw [hG, happ, ← Finset.sum_neg_distrib,
      Real.rpow_sum_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos)]
    refine norm_coeff_prod_le _ ?_ ?_ m'
    · intro z _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro z _ m''
      exact bound_place E h5 u i β hβ ep0 hep0 ep sg hep hsg be hbe I k z m''
  have hfac := factor D hn (D.R.N i) (D.R.N (i + 1)) ep0 hep0' ep sg be hcc
  generalize subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
      (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) = L at hTh hfac
  obtain ⟨Sk, V, hUV, hV⟩ := trunc_split
    (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I).totalDegree U
  have hs := hs_psiA (p := p) ep0 (τ := Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)))
  have hmon : ∀ k, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) * L =
      MvPowerSeries.coeff k U • (MvPowerSeries.monomial k (1 : ℂ_[p]) * L) := by
    intro k
    rw [← smul_mul_assoc]
    congr 1
    have h := map_smul (MvPowerSeries.monomial k :
      ℂ_[p] →ₗ[ℂ_[p]] MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
      (MvPowerSeries.coeff k U) (1 : ℂ_[p])
    rw [smul_eq_mul, mul_one] at h
    exact h
  have hsplit : subst (psiA p ep0) (U * L) =
      ∑ k ∈ Sk, MvPowerSeries.coeff k U •
          subst (psiA p ep0) (MvPowerSeries.monomial k (1 : ℂ_[p]) * L)
        + subst (psiA p ep0) (V * L) := by
    conv_lhs => rw [hUV]
    rw [add_mul, Finset.sum_mul, ← MvPowerSeries.coe_substAlgHom (R := ℂ_[p]) hs, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmon k, map_smul]
  have hord := order_psi_gt ep0 _ V L hV
  rw [hTh, hsplit, applyAt0_addT, applyAt0_sumT, applyAt0_eq_zero_of_order (h := hord), add_zero]
  simp only [applyAt0_smulT, hfac]
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) fun k _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  calc _ ≤ 1 * (p : ℝ) ^ (-∑ z, β z) := mul_le_mul (hU k) (hprod k m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end PI.OrbJet.AO

end
