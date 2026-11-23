import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
import Formalism.LocalToGlobal.Columns.FactorialSumLePowMulProd
import Formalism.LocalToGlobal.Columns.CoefColLemmas

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem max_slope_twisted_lattice (hS : FockSubNorm) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (g : ι → GL (Fin n) K)
    (hg : ∀ τ, ∀ x ∈ M τ, ∀ a, ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K))
    (hpos : ∀ v τ, 0 < gN K g v τ)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0) (hI : (I : Submodule (𝓞 K) K) = twId lam M)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    (tenH K lam M).muMax ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + ∑ τ, (dW (lam τ) : ℝ) * ((1 / (nPl K : ℝ)) * ∑ v, Real.log (gN K g v τ)) := by
  have hΔ : Submodule.IsLattice K (delK lam M) := (nabDelLattice K ι n lam M hM).2
  have hA0 : delK lam M ≠ ⊥ := isLattice_ne_bot hΔ
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
  have hinj := cfMap_injective lam g
  have hφx0 : cfMap lam g x0 ≠ 0 := fun h => hx00 (hinj (by rw [h, map_zero]))
  have hne : cfMap lam g ≠ 0 := fun h => hφx0 (by rw [h]; rfl)
  have hNE : Nonempty (MonI lam) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hφx0 (funext fun m => hE.elim m)
  have hX : ∀ v, IsUnit ((tenH K lam M).X v).det :=
    (formH_spec (bVV K lam) (pairK lam fun _ => 1) (tensor_pairing_pos_def K lam) (delK lam M)).1
  have hX' : ∀ v : InfinitePlace K, IsUnit ((monD lam)⁻¹).det := fun _ => Matrix.isUnit_nonsing_inv_det _ (monD_det lam)
  set L0 : Submodule (𝓞 K) (MonI lam → K) := ⨆ m : MonI lam, Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K)) with hL0
  have hL0fg : L0.FG := by
    have : L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K)) := by simp [hL0]
    rw [this]
    exact Submodule.fg_biSup _ _ fun m _ => Submodule.fg_span (Set.finite_singleton _)
  have hsingle : ∀ m : MonI lam, (Pi.single m 1 : MonI lam → K) ∈ L0 := fun m =>
    (le_iSup (fun m : MonI lam => Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K))) m) (Submodule.mem_span_singleton_self _)
  have hsne : ∀ m : MonI lam, (Pi.single m 1 : MonI lam → K) ≠ 0 := fun m h => by
    have := congrFun h m
    simp at this
  have hL00 : L0 ≠ ⊥ := fun h => by
    obtain ⟨m⟩ := hNE
    have := hsingle m
    rw [h, Submodule.mem_bot] at this
    exact hsne m this
  have hF3 : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) L0 ≤ -Real.log c0 :=
    max_slope_orthogonal_neg_log (monH K lam L0) (monH_frameOK K lam L0) (fun m : MonI lam => (Pi.single m 1 : MonI lam → K)) hsne
      (fun m m' h v => monH_orth K lam v m m' h) c0 hc0 (fun m v => by
        have := monH_norm_single K lam v m
        exact (hc m).trans (le_of_eq this.symm))
  obtain ⟨hBfg, -, hBmax, -⟩ := Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K (MonI lam → K) (MonI lam) (Pi.basisFun K (MonI lam))
    (fun _ => (monD lam)⁻¹) hX' I hI0 L0 hL0fg hL00
  have hle : (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    rintro _ ⟨x, hx, rfl⟩
    have e : (cfMap lam g).restrictScalars (𝓞 K) x = ∑ m, cfMap lam g x m • (Pi.single m 1 : MonI lam → K) := by
      funext m'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [e]
    refine sum_mem fun m _ => Submodule.subset_span ⟨_, ?_, _, hsingle m, rfl⟩
    rw [hI]
    exact coefficient_map_mem_twisted lam M g hg x hx m
  have hmap0 : (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) ≠ ⊥ := fun h => by
    have : (cfMap lam g).restrictScalars (𝓞 K) x0 ∈ (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) := ⟨x0, hx0, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hφx0 this
  have hSI := ((slope_inequality_mean K (VV K lam) (VVIdx lam) (MonI lam → K) (MonI lam) (tenH K lam M).b (tenH K lam M).X
    (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) hX hX' (cfMap lam g) (delK lam M) hΔ.fg hmap0).2
      (idealSmul (I : Submodule (𝓞 K) K) L0) hBfg hle).2 hinj.injOn
  have hH := coefficient_map_height_bound K lam hS g M hne hpos
  show muMaxDef (tenH K lam M).b (tenH K lam M).X (delK lam M) ≤ _
  rw [hBmax] at hSI
  linarith

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (coeff m P)‖ ^ 2 = ((coeff m P : ℚ) : ℝ) * ((coeff m P : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

theorem fock_norm_extremal_bound (hC : HwNormBound) {κ : ℕ} (lam : DomWeight (κ + 1)) :
    fockN (extremal ℂ (κ + 1) lam) ≤
      (∏ i, ((lam.natW i).factorial : ℝ)) * ((lam.natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := by
  rw [← Formalism.L2.DIV.map_extremal (algebraMap ℚ ℂ) (κ + 1) lam, fock_norm_rational_eq]
  have h := hC κ lam.natW (natural_weight_antitone lam)
  have h' : ((Formalism.GradedWeylDivisibility.fockQ (extremal ℚ (κ + 1) lam) (extremal ℚ (κ + 1) lam) : ℚ) : ℝ) ≤
      (((((∏ i, (lam.natW i).factorial : ℕ) : ℚ) * ((lam.natW 0 + κ + 1 : ℕ) : ℚ) ^ ((κ + 1) * κ / 2) : ℚ)) : ℝ) := by
    exact_mod_cast h
  refine h'.trans (le_of_eq ?_)
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem multi_factorial_eq_triple_prod (m : (ι × Fin n × Fin n) →₀ ℕ) : mfact m = ∏ τ : ι, ∏ s : Fin n, ∏ a : Fin n, (m (τ, a, s)).factorial := by
  unfold mfact
  rw [Finset.prod_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    rw [Finsupp.notMem_support_iff.1 hk, Nat.factorial_zero]), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fintype.prod_prod_type, Finset.prod_comm]

theorem factorial_prod_le_monomial (lam : ι → DomWeight n) (m : MonI lam) :
    ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ n ^ (∑ τ, dW (lam τ)) * mfact m.1 := by
  rw [multi_factorial_eq_triple_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun τ _ => ?_
  unfold dW
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← m.2 τ s]
  exact factorial_sum_le_pow_mul_prod fun a => m.1 (τ, a, s)

def monC {κ : ℕ} (lam : ι → DomWeight (κ + 1)) : ℝ :=
  (((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2))⁻¹

theorem monC_pos {κ : ℕ} (lam : ι → DomWeight (κ + 1)) : 0 < monC lam := by
  unfold monC
  have : ∀ τ, (0 : ℝ) < (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := fun τ => by positivity
  have h2 := Finset.prod_pos fun τ (_ : τ ∈ Finset.univ) => this τ
  positivity

theorem monomial_weight_lower_bound (hC : HwNormBound) {κ : ℕ} (lam : ι → DomWeight (κ + 1)) (m : MonI lam) : monC lam ≤ monW lam m := by
  unfold monC monW
  have hE : extremalFockNormProduct lam ≤ (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => fockN_nonneg _) fun τ _ => fock_norm_extremal_bound hC (lam τ)
  have hM : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤ ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * (mfact m.1 : ℝ) := by
    exact_mod_cast factorial_prod_le_monomial lam m
  have hP : 0 < ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
    Finset.prod_pos fun τ _ => by positivity
  have hk : (0 : ℝ) < ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hk hP) (extR_pos lam), one_mul]
  calc extremalFockNormProduct lam ≤ (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := hE
    _ ≤ (((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * (mfact m.1 : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
        mul_le_mul_of_nonneg_right hM hP.le
    _ = _ := by ring

theorem neg_log_monomial_constant {κ : ℕ} (lam : ι → DomWeight (κ + 1)) :
    -Real.log (monC lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log ((κ : ℝ) + 1)
      + ((κ : ℝ) + 1) * (κ : ℝ) / 2 * Real.log (((lam τ).natW 0 : ℝ) + κ + 1)) := by
  unfold monC
  have hP : 0 < ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
    Finset.prod_pos fun τ _ => by positivity
  have hk : (0 : ℝ) < ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) := by positivity
  rw [Real.log_inv, neg_neg, Real.log_mul hk.ne' hP.ne', Real.log_pow, Real.log_prod (fun τ _ => by positivity),
    Finset.sum_add_distrib, Nat.cast_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_pow, triangular_number_cast]

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι]

theorem degree_weight_cast_eq {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : (dW lam : ℝ) = (wt (plus (castW h lam)) : ℝ) := by
  subst h
  unfold dW wt
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact_mod_cast natural_weight_cast_eq lam i

theorem det_shift_eq_last_weight {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : lam.detShift = castW h lam (Fin.last κ) := by
  subst h
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos κ)]
  rfl

theorem max_slope_twisted_general (hS : FockSubNorm) (hC : HwNormBound) {n κ : ℕ} (h : κ + 1 = n) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) (g : ι → GL (Fin n) K)
    (hg : ∀ τ, ∀ x ∈ M τ, ∀ a, ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K))
    (hpos : ∀ v τ, 0 < gN K g v τ)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0) (hI : (I : Submodule (𝓞 K) K) = twId lam M) :
    (tenH K lam M).muMax ≤
      ∑ τ, ((wt (plus (castW h (lam τ))) : ℝ) * (Real.log ((κ : ℝ) + 1) + (1 / (nPl K : ℝ)) * ∑ v, Real.log (gN K g v τ))
        + ((κ : ℝ) + 1) * (κ : ℝ) / 2 * Real.log ((plus (castW h (lam τ)) 0 : ℝ) + (κ : ℝ) + 1))
      - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  subst h
  have h1 := max_slope_twisted_lattice K lam hS M hM g hg hpos I hI0 hI (monC lam) (monC_pos lam) (monomial_weight_lower_bound hC lam)
  rw [neg_log_monomial_constant] at h1
  refine h1.trans (le_of_eq ?_)
  have e : ∀ τ, (((lam τ).natW 0 : ℕ) : ℝ) = (plus (castW rfl (lam τ)) 0 : ℝ) := fun τ => by
    exact_mod_cast natural_weight_cast_eq (lam τ) 0
  simp only [e, degree_weight_cast_eq rfl]
  rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by ring

end Gen

end Formalism.L2.Col
