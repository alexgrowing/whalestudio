import Formalism.HermitianCurvature.HermitianCurvatureProofs.XepolNatDegree

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

private theorem natDegree_prod_X_add_C_le_card (S : Finset ℕ) (a : ℕ → ℂ) :
    (∏ i ∈ S, (X + C (a i))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => (Polynomial.natDegree_X_add_C (a i)).le)).trans ?_
  simp

private theorem xpol_natDegree_le (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k - 1 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1)) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1)).card = P.k - 1 := by rw [Nat.card_Icc]; omega
  unfold xpol
  omega

theorem xpol_half_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X + C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_halfm_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X - C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_sub_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_deg (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k := by
  have := xpol_natDegree_le P ρ
  omega

private theorem xepol_natDegree_le (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree ≤ P.k - 2 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1) \ {l}) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1) \ {l}).card = P.k - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]; omega
  unfold xepol
  omega

theorem xepol_deg (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).natDegree ≤ P.k := by
  have := xepol_natDegree_le P hl ρ
  exact (Polynomial.natDegree_C_mul_le c _).trans (by omega)

theorem xepol_coeff (P : M.Par) (hk : 2 ≤ P.k) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).coeff (P.k - 1) = 0 := by
  have := xepol_natDegree_le P hl ρ
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c _) (by omega))

theorem nab_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nab = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)) -
        e ρ • (d.κ (dl ρ) * d.L.ζb)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nab) +
        ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    simp_rw [e10 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_half_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0,
        lam j • ((C (fl P l ρ ρ0) * xepol P l ρ0).eval ((j : ℕ) : ℂ) • (d.SS l * d.κ (dl ρ0))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun ρ0 _ => ?_
      rw [comb hlam _ (xepol_deg P hl ρ0 _), xepol_coeff P hk hl, zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nab = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 1 0)) - ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nab = (∑ ρ, d.κ (dl ρ)) * d.L.nab := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

theorem nabs_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nabs = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)) -
        e ρ • (d.κ (dl ρ) * d.L.ζ)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nabs) +
        ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    simp_rw [e01 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_halfm_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1),
        lam j • ((xepol P l ρ).eval ((j : ℕ) : ℂ) • (d.κ (dl ρ) * star (d.SS l))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hd : (xepol P l ρ).natDegree ≤ P.k := by rw [xepol_natDegree P hl]; omega
      rw [comb hlam _ hd, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [xepol_natDegree P hl]; omega),
        zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nabs = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 0 1)) - ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nabs = (∑ ρ, d.κ (dl ρ)) * d.L.nabs := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

end ring

section fst

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem fst_mul' (a b : Q.Pr V) : (a * b).1 = a.1 * b.1 := rfl
theorem fst_add' (a b : Q.Pr V) : (a + b).1 = a.1 + b.1 := rfl
theorem fst_neg' (a : Q.Pr V) : (-a).1 = -a.1 := rfl
theorem fst_sub' (a b : Q.Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem fst_zero' : (0 : Q.Pr V).1 = 0 := rfl
theorem fst_smul' (c : ℂ) (a : Q.Pr V) : (c • a).1 = c • a.1 := by
  first
  | rfl
  | exact Prod.smul_fst _ _
theorem fst_sum' {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  first
  | exact Prod.fst_sum
  | exact map_sum (AddMonoidHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ) f s

end fst

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem radDZ_expr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (hT : ∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (lam : Fin (P.k + 1) → ℂ) (c : ℂ) (j0 : Fin 6) (hj0 : j0 = 0 ∨ j0 = 2) (a b : Fin 2) (ρ : M.Ty P) :
    RadDZ P Bs (X.fn 5 * (-(∑ j : Fin (P.k + 1), lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) a b)) -
      c • ((d.κ (dl ρ)).1 * X.fn j0))) := by
  have hpl := hH.1
  refine radDZ_fn_left P Bs hpl X 5 (Or.inr (Or.inr rfl)) ?_
  rw [sub_eq_add_neg]
  refine radDZ_add (radDZ_neg (radDZ_sum _ _ fun j _ => radDZ_smul ?_ _)) (radDZ_neg (radDZ_smul ?_ _))
  · exact radDZ_kap_left P Bs X d hH e he hk ρ (hT _ a b)
  · refine radDZ_kap_left P Bs X d hH e he hk ρ ?_
    have := radDZ_fn_left P Bs hpl X j0 (hj0.elim Or.inl fun h => Or.inr (Or.inl h)) (radDZ_one P Bs)
    rwa [mul_one] at this

theorem local_nabla_holds : GTCLNab := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT e he hk
  have hpl := hH.1
  have hk2 := hH.2.1
  have hL := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hQ := hH.2.2.2.2.2.2
  have hQt : ∀ (Y : ℂ) (a b : Fin 2), (d.QQ Y a b).1 = X.t Y a b := by
    intro Y a b
    rw [← hQ Y]
    rfl
  have hGGi : d.L.GGi.1 = X.fn 5 := by rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hζb : d.L.ζb.1 = X.fn 2 := by rw [hL.2.2.2.2.2.2.2.2.1]; rfl
  have hζ : d.L.ζ.1 = X.fn 0 := by rw [hL.2.2.2.2.2.2.1]; rfl
  obtain ⟨lam, c, hn⟩ := nab_eq d hR hk2
  obtain ⟨lam', c', hns⟩ := nabs_eq d hR hk2
  constructor
  · rw [hn, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζb]
    have hs : ∀ j : Fin (P.k + 1), (lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)).1 =
        lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 1 0) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam (c ρ) 2 (Or.inr rfl) 1 0 ρ
  · rw [hns, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζ]
    have hs : ∀ j : Fin (P.k + 1), (lam' j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)).1 =
        lam' j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 0 1) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam' (c' ρ) 0 (Or.inl rfl) 0 1 ρ

end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem local_nabla_holds : GTCLNab := LNab.local_nabla_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
