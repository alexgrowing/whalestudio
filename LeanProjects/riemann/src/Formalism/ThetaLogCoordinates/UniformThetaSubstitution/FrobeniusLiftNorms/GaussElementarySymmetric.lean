import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC
import Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

namespace CSym

section gen

variable {K σ : Type} [CommRing K] [Fintype σ]

def genE (x : σ → K) : PowerSeries K := ∏ i, (1 + PowerSeries.C (x i) * PowerSeries.X)

lemma eF_eq_sum (x : σ → K) (l : ℕ) :
    eF x l = ∑ s ∈ powersetCard l univ, ∏ i ∈ s, x i := by
  unfold eF
  simp [MvPolynomial.esymm, map_sum, map_prod]

lemma coeff_genE (x : σ → K) (l : ℕ) : PowerSeries.coeff l (genE x) = eF x l := by
  classical
  rw [eF_eq_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  unfold genE
  have hc : ∀ i, (1 + PowerSeries.C (x i) * PowerSeries.X : PowerSeries K) =
      PowerSeries.C (x i) * PowerSeries.X + 1 := fun i => add_comm _ _
  simp_rw [hc]
  rw [Finset.prod_add, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod,
    PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

lemma eF_zero (x : σ → K) : eF x 0 = 1 := by
  simp [eF, MvPolynomial.esymm_zero]

lemma eF_smul (c : K) (x : σ → K) (l : ℕ) : eF (fun i => c * x i) l = c ^ l * eF x l := by
  simp only [eF_eq_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_powersetCard.1 hs).2]

lemma eF_of_card_lt (x : σ → K) (l : ℕ) (h : Fintype.card σ < l) : eF x l = 0 := by
  rw [eF_eq_sum, Finset.powersetCard_eq_empty.2 (by simpa using h), Finset.sum_empty]

lemma eF_of_genE_mul {τ ρ : Type} [Fintype τ] [Fintype ρ] (z : σ → K) (x : τ → K) (y : ρ → K)
    (h : genE z = genE x * genE y) (n : ℕ) :
    eF z n = ∑ a ∈ range (n + 1), eF x a * eF y (n - a) := by
  rw [← coeff_genE, h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_genE]

lemma eF_isEmpty [IsEmpty σ] (x : σ → K) (l : ℕ) : eF x l = if l = 0 then 1 else 0 := by
  split_ifs with hl
  · subst hl
    exact eF_zero x
  · exact eF_of_card_lt x l (by rw [Fintype.card_eq_zero]; omega)

lemma eF_fin_succ {g : ℕ} (x : Fin (g + 1) → K) (l : ℕ) :
    eF x (l + 1) = eF (fun i : Fin g => x i.castSucc) (l + 1) +
      x (Fin.last g) * eF (fun i : Fin g => x i.castSucc) l := by
  have hg : genE x = genE (fun i : Fin g => x i.castSucc) *
      (1 + PowerSeries.C (x (Fin.last g)) * PowerSeries.X) := by
    unfold genE
    rw [Fin.prod_univ_castSucc]
  rw [← coeff_genE, hg, mul_add, mul_one, map_add,
    show genE (fun i : Fin g => x i.castSucc) * (PowerSeries.C (x (Fin.last g)) * PowerSeries.X) =
      PowerSeries.C (x (Fin.last g)) * genE (fun i : Fin g => x i.castSucc) * PowerSeries.X by ring,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul, coeff_genE, coeff_genE]

end gen

lemma conv_smul {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (f g : ℕ → K) (E : ℕ → V)
    (i : ℕ) :
    ∑ l ∈ range (i + 1), f l • ∑ l' ∈ range (i - l + 1), g l' • E (i - l - l') =
      ∑ n ∈ range (i + 1), (∑ a ∈ range (n + 1), f a * g (n - a)) • E (i - n) := by
  simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
  have hin : ∀ l ∈ range (i + 1), ∑ l' ∈ range (i - l + 1), (f l * g l') • E (i - l - l') =
      ∑ n ∈ Ico l (i + 1), (f l * g (n - l)) • E (i - n) := by
    intro l hl
    simp only [Finset.mem_range] at hl
    rw [Finset.sum_Ico_eq_sum_range, show i + 1 - l = i - l + 1 by omega]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [show l + l' - l = l' by omega, show i - (l + l') = i - l - l' by omega]
  rw [Finset.sum_congr rfl hin]
  exact Finset.sum_comm' (fun l n => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)

lemma sum_comp {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → B →ₗ[K] C) (g : A →ₗ[K] B) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  ext a
  simp [LinearMap.sum_apply]

lemma comp_sum {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → A →ₗ[K] B) (g : B →ₗ[K] C) :
    g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by
  ext a
  simp [LinearMap.sum_apply, map_sum]

section gauss

variable {K : Type} [Field K]

lemma beFam_castSucc (Q : K) (hQ : Q ≠ 0) (g : ℕ) (i : Fin g) :
    beFam Q (g + 1) i.castSucc = Q * beFam Q g i := by
  unfold beFam
  rw [show ((g + 1 : ℕ) : ℤ) - 1 - 2 * ((i.castSucc : Fin (g + 1)).val : ℤ) =
      ((g : ℤ) - 1 - 2 * (i.val : ℤ)) + 1 by simp; ring, zpow_add_one₀ hQ, mul_comm]

lemma beFam_last (Q : K) (g : ℕ) : beFam Q (g + 1) (Fin.last g) = Q ^ (-(g : ℤ)) := by
  unfold beFam
  congr 1
  simp
  ring

lemma eF_beFam_succ (Q : K) (hQ : Q ≠ 0) (g l : ℕ) :
    eF (beFam Q (g + 1)) (l + 1) =
      Q ^ (l + 1) * eF (beFam Q g) (l + 1) + Q ^ (-(g : ℤ)) * (Q ^ l * eF (beFam Q g) l) := by
  rw [eF_fin_succ]
  simp_rw [beFam_castSucc Q hQ]
  rw [eF_smul, eF_smul, beFam_last]

lemma gauss_zpow (Q : ℕ) (hQ : (Q : K) ≠ 0) : ∀ g l : ℕ,
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) =
      (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) * eF (beFam (Q : K) g) l
  | g, 0 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_right, eF_zero]; simp
  | 0, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_succ, eF_of_card_lt _ _ (by simp)]; simp
  | g + 1, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_succ_succ, eF_beFam_succ _ hQ]
    push_cast
    rw [gauss_zpow Q hQ g l, gauss_zpow Q hQ g (l + 1)]
    push_cast
    generalize eF (beFam (Q : K) g) l = E0
    generalize eF (beFam (Q : K) g) (l + 1) = E1
    have h1 : (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (-(g : ℤ)) *
          (Q : K) ^ l := by
      rw [← zpow_natCast, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
      congr 1
      ring
    have h2 : ((Q : K) ^ 2) ^ (l + 1) * (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) - ((l : ℤ) + 1))) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (l + 1) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast (Q : K) (l + 1), ← zpow_add₀ hQ,
        ← zpow_add₀ hQ]
      congr 1
      push_cast
      ring
    linear_combination E0 * h1 + E1 * h2

end gauss

end CSym

open CSym

theorem gauss_elementary_symmetric : GaussEsymm := by
  intro K _ Q g l hQ
  rw [gauss_zpow Q hQ g l]
  rcases le_or_gt l g with h | h
  · rw [show ((l : ℤ) * ((g : ℤ) - l)) = ((l * (g - l) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring,
      zpow_natCast]
  · rw [eF_of_card_lt _ _ (by simpa using h)]
    simp

theorem hecke_convolution : HEConvolution := by
  intro K σ _ _ _ x n hn
  have h := Formalism.FT.SymmetricSeries.esymm_hsymm_rel (σ := σ) (R := K) n hn
  have h2 := congrArg (MvPolynomial.eval x) h
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at h2
  rw [← Finset.sum_range_reflect]
  have hterm : ∀ j ∈ range (n + 1), (-1 : K) ^ (n + 1 - 1 - j) * hF x (n + 1 - 1 - j) * eF x (n - (n + 1 - 1 - j)) =
      (-1) ^ n * ((-1) ^ j * MvPolynomial.eval x (MvPolynomial.esymm σ K j) *
        MvPolynomial.eval x (MvPolynomial.hsymm σ K (n - j))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
    have e : (-1 : K) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have e2 : (-1 : K) ^ (n - j) = (-1) ^ n * (-1) ^ j := by
      rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    unfold hF eF
    rw [e2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, h2, mul_zero]

namespace CSym

lemma genE_FFam_succ {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) :
    genE (FFam Q t m (j + 1)) =
      genE (fun x => m (j + 1) * beFam Q (t + 1) x) * genE (FFam Q t m j) := by
  unfold genE
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Fin.prod_univ_castSucc, mul_comm]
  rfl

end CSym

theorem iterate_statement : Iterate := by
  intro K _ M _ _ Kk e Q t m J hI j
  induction j with
  | zero =>
    intro _ i
    simp only [Kc, LinearMap.comp_id, LinearMap.id_comp]
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [eF_isEmpty, if_neg hl, zero_smul])
      (by simp), eF_isEmpty, if_pos rfl, one_smul, Nat.sub_zero]
  | succ j ih =>
    intro hj i
    have ih' := ih (by omega)
    show (e (j + 1) i).comp ((Kk j).comp (Kc Kk j)) =
      ((Kk j).comp (Kc Kk j)).comp (∑ l ∈ range (i + 1), eF (FFam Q t m (j + 1)) l • e 0 (i - l))
    rw [← LinearMap.comp_assoc, hI j (by omega) i, LinearMap.comp_assoc, CSym.sum_comp]
    simp_rw [LinearMap.smul_comp, ih', ← LinearMap.comp_smul, ← CSym.comp_sum]
    rw [← LinearMap.comp_assoc]
    congr 1
    rw [conv_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eF_of_genE_mul _ _ _ (genE_FFam_succ Q t m j) n]

theorem inversion_formula : Inversion := by
  intro K _ M _ _ Kk e Q t m J hI j hj r
  have hit := iterate_statement K M Kk e Q t m J hI j hj
  rw [CSym.sum_comp]
  simp_rw [LinearMap.smul_comp, hit, ← LinearMap.comp_smul, ← CSym.comp_sum]
  congr 1
  rw [conv_smul, Finset.sum_eq_single 0]
  · simp [hF, eF_zero, MvPolynomial.hsymm_zero]
  · intro n _ hn0
    rw [hecke_convolution K _ (FFam Q t m j) n (by omega), zero_smul]
  · intro h
    simp at h

theorem theorem_c_i : ThmCi := by
  intro K ι _ M _ _ Kk Tm pp ν k t r j Ev Od lam w m hpp hrk hI
  set Q := pp ^ ν with hQdef
  have hQ : Q ≠ 0 := pow_ne_zero _ hpp
  have hinv := inversion_formula K M Kk (fun a i => (Q ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i)
    Q t m j hI j le_rfl r
  have hZ : Zop pp ν Ev Od lam w m k t r j (Tm j) =
      (pp ^ (NprimeZ Ev Od lam (w j) r) * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r))) •
        ∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) •
          ((Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ))))) • Tm j (r - l)) := by
    unfold Zop
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlr : l ≤ r := by simp only [Finset.mem_range] at hl; omega
    unfold cCoef Ttil
    simp only [smul_smul]
    congr 1
    have h1 : pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) *
        pp ^ (NprimeZ Ev Od lam (w j) (r - l)) = pp ^ (NprimeZ Ev Od lam (w j) r) := by
      rw [← zpow_add₀ hpp]
      ring_nf
    have h2 : Q ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) =
        Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
          Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) := by
      rw [← zpow_add₀ hQ]
      congr 1
      push_cast [Nat.cast_sub hlr]
      ring
    rw [h2]
    linear_combination ((-1 : K) ^ l * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
      Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) * hF (FFam Q t m j) l) * h1
  rw [hZ, LinearMap.smul_comp, hinv]
  simp only [LinearMap.comp_smul, smul_smul]
  congr 1
  have hQz : ∀ z : ℤ, Q ^ z = pp ^ ((ν : ℤ) * z) := fun z => by rw [zpow_mul, zpow_natCast]
  rw [hQz, hQz, ← zpow_add₀ hpp, ← zpow_add₀ hpp, ← zpow_add₀ hpp]
  congr 1
  unfold NprimeZ PrZ ArZ NN
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

end Formalism.InvariantFactorPaths.G7
