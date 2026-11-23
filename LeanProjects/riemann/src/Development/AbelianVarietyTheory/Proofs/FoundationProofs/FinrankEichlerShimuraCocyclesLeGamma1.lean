import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAddStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeActionStatement

section

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by
  rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  · rw [polySlash_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by
  rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem polySlash_one (w : ℕ) (p : ℂ[X]) (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  have h : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  conv_rhs => rw [p.as_sum_range' (w + 1) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_X_eq_monomial]

theorem polySlash_action (w : ℕ) :
    (∀ (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w g p ∈ degreeLT ℂ (w + 1)) ∧
      (∀ p ∈ degreeLT ℂ (w + 1), slP w 1 p = p) ∧
      ∀ (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w (g * h) p = slP w h (slP w g p) :=
  ⟨polySlash_mem_degreeLT w, polySlash_one w, fun g h p => (polySlash_polySlash w g h p).symm⟩

theorem dvd_trace_sub_two (N : ℕ) (x g : SL(2, ℤ)) (h : x * g * x⁻¹ ∈ CongruenceSubgroup.Gamma1 N) :
    (N : ℤ) ∣ (mat g).trace - 2 := by
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have ht : (mat (x * g * x⁻¹)).trace = (mat g).trace := by
    change (mat (x * g) * mat x⁻¹).trace = _
    rw [Matrix.trace_mul_comm]
    change (mat (x⁻¹ * (x * g))).trace = _
    rw [inv_mul_cancel_left]
  rw [← ht, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Matrix.trace_fin_two]
  push_cast
  rw [h.1, h.2.1]
  norm_num

theorem not_conj_mem (N : ℕ) (hN : 5 ≤ N) (x g : SL(2, ℤ)) (h1 : -2 ≤ (mat g).trace) (h2 : (mat g).trace < 2) :
    x * g * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have := Int.le_of_dvd (by omega) ((dvd_neg).2 (dvd_trace_sub_two N x g h))
  omega

theorem torsion_not_mem (N : ℕ) (hN : 5 ≤ N) (x : SL(2, ℤ)) (k : ℕ) (hk : 0 < k) :
    (k < 4 → x * ModularGroup.S ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) ∧
      (k < 6 → x * (ModularGroup.S * ModularGroup.T) ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) := by
  constructor <;> intro hk' <;> interval_cases k <;> exact not_conj_mem N hN x _ (by decide) (by decide)

end GlobalTheory.HeckeFamilyMatrices.CocBound

end

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

def rho (w : ℕ) (g : SL(2, ℤ)) : degreeLT ℂ (w + 1) →ₗ[ℂ] degreeLT ℂ (w + 1) :=
  ((slP w (mat g)).comp (degreeLT ℂ (w + 1)).subtype).codRestrict _ (fun p => (polySlash_action w).1 _ _)

theorem rho_mul (w : ℕ) (g h : SL(2, ℤ)) (v : degreeLT ℂ (w + 1)) :
    rho w (g * h) v = rho w h (rho w g v) := by
  apply Subtype.ext
  change slP w (mat (g * h)) v = slP w (mat h) (slP w (mat g) v)
  rw [← (polySlash_action w).2.2]
  rfl

theorem rho_one (w : ℕ) (v : degreeLT ℂ (w + 1)) : rho w 1 v = v := by
  apply Subtype.ext
  change slP w (mat 1) v = v
  exact (polySlash_action w).2.1 _ v.2

theorem rho_pow (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) : rho w g ^ m = rho w (g ^ m) := by
  induction m with
  | zero => ext1 v; simp [rho_one]
  | succ m ih => ext1 v; rw [pow_succ', pow_succ, rho_mul, ← ih]; rfl

theorem rho_pow_eq_one (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) (h : g ^ m = 1) : rho w g ^ m = 1 := by
  rw [rho_pow, h]; ext1 v; exact rho_one w v

def zMap (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Z1 Γ w →ₗ[ℂ] cocyc Γ (rho w) where
  toFun z := ⟨fun γ => ⟨z.1 γ, z.2.1 γ⟩, fun γ δ => Subtype.ext (z.2.2 γ δ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zMap_injective (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Function.Injective (zMap Γ w) := by
  intro z z' h
  apply Subtype.ext
  funext γ
  exact congrArg (fun f : cocyc Γ (rho w) => (f.1 γ : ℂ[X])) h

open ModularGroup in
theorem closure_S_ST : Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  have hU : S * T ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  intro x hx
  rcases hx with rfl | rfl
  · exact hS
  · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hS) hU
    simpa using this

end GlobalTheory.HeckeFamilyMatrices.CocBound

namespace GlobalTheory.HeckeFamilyMatrices

open CocBound ModularGroup in

theorem finrank_eichlerShimuraCocycles_le_Gamma1 (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (hN : 5 ≤ N)
    (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hfi : Γ.FiniteIndex) :
    FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  have hE : FiniteDimensional ℂ (degreeLT ℂ (w + 1)) := inferInstance
  have hr : Module.finrank ℂ (degreeLT ℂ (w + 1)) = w + 1 := by
    rw [(degreeLTEquiv ℂ (w + 1)).finrank_eq]; simp
  have hS4 : S ^ 4 = 1 := by decide
  have hU6 : (S * T) ^ 6 = 1 := by decide
  have hSU : S ^ 2 = (S * T) ^ 3 := by decide
  have hU3 : ((S * T) ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hU6
  obtain ⟨-, h4⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ S (rho w S) 4 hfi hE (by norm_num) hS4 (rho_pow_eq_one w _ _ hS4)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).1 hk' (hΓ h))
  obtain ⟨-, h6⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ (S * T) (rho w (S * T)) 6 hfi hE (by norm_num) hU6 (rho_pow_eq_one w _ _ hU6)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).2 hk' (hΓ h))
  obtain ⟨f2, h2⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ ((S * T) ^ 3) (rho w ((S * T) ^ 3)) 2 hfi hE (by norm_num) hU3
    (rho_pow_eq_one w _ _ hU3) (fun x k hk hk' h => by
      obtain rfl : k = 1 := by omega
      rw [pow_one] at h
      exact (torsion_not_mem N hN x 3 (by norm_num)).2 (by norm_num) (hΓ h))
  obtain ⟨fC, hC⟩ := GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le Γ (rho w) (S * T) (rho_mul w) (rho_one w) hU6 f2
  obtain ⟨fB, hB⟩ := GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add Γ (rho w) S (S * T) (rho_mul w) (rho_one w) hSU closure_S_ST hE fC
  obtain ⟨fA, hA⟩ := GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension Γ (rho w) S (rho_mul w) (rho_one w) hS4 fB
  have hZ := LinearMap.finrank_le_finrank_of_injective (zMap_injective Γ w)
  refine ⟨Module.Finite.of_injective _ (zMap_injective Γ w), ?_⟩
  rw [hr] at h4 h6 h2 hB
  have : (w + 1) * (12 + Γ.index) = 12 * (w + 1) + Γ.index * (w + 1) := by ring
  omega

end GlobalTheory.HeckeFamilyMatrices
