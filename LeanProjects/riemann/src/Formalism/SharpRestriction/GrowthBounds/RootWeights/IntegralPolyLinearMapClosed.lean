import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def halfFactorialValuation (p : ℕ) {σ : Type} (m : σ →₀ ℕ) : WithTop ℚ := (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)

theorem mem_fock_lattice_iff_coeff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, 0 ≤ vK p (F.coeff m) + halfFactorialValuation p m := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [InBB, vBB, Finset.le_inf_iff]
  constructor
  · intro h m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm, hV0, top_add]
      exact le_top
  · intro h m _
    exact h m

theorem fock_lattice_zero_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} : InBB (O := O) p (0 : MvPolynomial σ (KK O)) := by
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  refine (mem_fock_lattice_iff_coeff hV 0).2 fun m => ?_
  rw [coeff_zero, hV0, top_add]
  exact le_top

theorem fock_lattice_add_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} {F G : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) (hG : InBB (O := O) p G) : InBB (O := O) p (F + G) := by
  obtain ⟨-, -, hVadd, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF hG ⊢
  intro m
  rw [coeff_add]
  calc (0 : WithTop ℚ)
      ≤ min (vK p (F.coeff m) + halfFactorialValuation p m) (vK p (G.coeff m) + halfFactorialValuation p m) := le_min (hF m) (hG m)
    _ = min (vK p (F.coeff m)) (vK p (G.coeff m)) + halfFactorialValuation p m := min_add_add_right _ _ _
    _ ≤ vK p (F.coeff m + G.coeff m) + halfFactorialValuation p m := add_le_add_left (hVadd _ _) _

theorem fock_lattice_sum_mem {p : ℕ} (hV : ValuationProperties p O) {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ (KK O))
    (h : ∀ i ∈ s, InBB (O := O) p (f i)) : InBB (O := O) p (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (InBB (O := O) p) (fun _ _ => fock_lattice_add_mem hV) (fock_lattice_zero_mem hV) h

theorem fock_lattice_smul_mem {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (o : O) {F : MvPolynomial σ (KK O)}
    (hF : InBB (O := O) p F) : InBB (O := O) p (o • F) := by
  obtain ⟨-, hVmul, -, -, -, hVint⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV] at hF ⊢
  intro m
  rw [coeff_smul, Algebra.smul_def, hVmul]
  have ho : 0 ≤ vK p (algebraMap O (KK O) o) := (hVint _).2 ⟨o, rfl⟩
  calc (0 : WithTop ℚ) ≤ vK p (F.coeff m) + halfFactorialValuation p m := hF m
    _ ≤ vK p (algebraMap O (KK O) o) + vK p (F.coeff m) + halfFactorialValuation p m :=
        add_le_add_left (le_add_of_nonneg_left ho) _

theorem fock_lattice_monomial_iff {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m : σ →₀ ℕ) (c : KK O) :
    InBB (O := O) p (monomial m c) ↔ 0 ≤ vK p c + halfFactorialValuation p m := by
  classical
  obtain ⟨hV0, -, -, -, -, -⟩ := id hV
  rw [mem_fock_lattice_iff_coeff hV]
  constructor
  · intro h
    have hm := h m
    rwa [coeff_monomial, if_pos rfl] at hm
  · intro h m'
    rw [coeff_monomial]
    split_ifs with hm
    · rw [← hm]
      exact h
    · rw [hV0, top_add]
      exact le_top

theorem fock_lattice_iff_monomials {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (F : MvPolynomial σ (KK O)) :
    InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m)) := by
  rw [mem_fock_lattice_iff_coeff hV]
  exact forall_congr' fun m => (fock_lattice_monomial_iff hV m _).symm

theorem fock_lattice_linear_map_closed {p : ℕ} (hV : ValuationProperties p O) {σ : Type}
    (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c)))
    (F : MvPolynomial σ (KK O)) (hF : InBB (O := O) p F) : InBB (O := O) p (u F) := by
  rw [← F.support_sum_monomial_coeff, map_sum]
  exact fock_lattice_sum_mem hV _ _ fun m _ => h m _ ((fock_lattice_iff_monomials hV F).1 hF m)

theorem valuation_intCast_padicVal {p : ℕ} (hV : ValuationProperties p O) (z : ℤ) (hz : z ≠ 0) :
    vK p (z : KK O) = ((padicValInt p z : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, hVnat, hVneg, -⟩ := id hV
  have hn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  have e : padicValInt p z = padicValNat p z.natAbs := rfl
  rw [e]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
    exact hVnat _ hn
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, hVneg]
    exact hVnat _ hn

theorem fock_lattice_monomial_rescale {p : ℕ} (hV : ValuationProperties p O) {σ : Type} (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ)
    (h : InBB (O := O) p (monomial m c))
    (hz : z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) :
    InBB (O := O) p (monomial m' (c * (z : KK O))) := by
  obtain ⟨hV0, hVmul, -, -, -, -⟩ := id hV
  rw [fock_lattice_monomial_iff hV] at h ⊢
  by_cases hz0 : z = 0
  · rw [hz0, Int.cast_zero, mul_zero, hV0, top_add]
    exact le_top
  have hz' : padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m') :=
    hz.resolve_left hz0
  rw [hVmul, valuation_intCast_padicVal hV z hz0]
  have hq : ((padicValNat p (expFact m) : ℚ) / 2) ≤
      (padicValInt p z : ℚ) + (padicValNat p (expFact m') : ℚ) / 2 := by
    have : (padicValNat p (expFact m) : ℚ) ≤ 2 * (padicValInt p z : ℚ) + padicValNat p (expFact m') := by
      exact_mod_cast hz'
    linarith
  have hw : halfFactorialValuation p m ≤ ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := by
    simp only [halfFactorialValuation]
    rw [← WithTop.coe_add]
    exact WithTop.coe_le_coe.2 hq
  calc (0 : WithTop ℚ) ≤ vK p c + halfFactorialValuation p m := h
    _ ≤ vK p c + (((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m') := add_le_add_right hw _
    _ = vK p c + ((padicValInt p z : ℚ) : WithTop ℚ) + halfFactorialValuation p m' := (add_assoc _ _ _).symm

theorem mem_integral_poly_iff_map {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∃ F0 : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) F0 = F := by
  simp only [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply]
  rfl

theorem mem_integral_poly_iff_coeff {σ : Type} (F : MvPolynomial σ (KK O)) :
    F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o := by
  rw [mem_integral_poly_iff_map]
  constructor
  · rintro ⟨F0, rfl⟩ m
    exact ⟨F0.coeff m, coeff_map _ _ _⟩
  · intro h
    choose g hg using h
    refine ⟨∑ m ∈ F.support, monomial m (g m), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← F.support_sum_monomial_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_monomial, hg]

theorem integer_monomial_mem_integral {σ : Type} (m : σ →₀ ℕ) (z : ℤ) : monomial m (z : KK O) ∈ IntPol O σ := by
  exact (mem_integral_poly_iff_map _).2 ⟨monomial m (z : O), by rw [map_monomial, map_intCast]⟩

theorem integral_poly_linear_map_closed {σ : Type} (u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O))
    (h : ∀ m, u (monomial m 1) ∈ IntPol O σ) (F : MvPolynomial σ (KK O)) (hF : F ∈ IntPol O σ) :
    u F ∈ IntPol O σ := by
  choose g hg using (mem_integral_poly_iff_coeff F).1 hF
  rw [← F.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have e : monomial m (F.coeff m) = (algebraMap O (KK O) (g m)) • monomial m (1 : KK O) := by
    rw [smul_monomial, smul_eq_mul, mul_one, hg]
  rw [e, map_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (h m)

theorem fock_lattice_closure_holds {p : ℕ} (hV : ValuationProperties p O) : FockLatticeClosure p O :=
  fun _ => ⟨fock_lattice_zero_mem hV, fun _ _ => fock_lattice_add_mem hV, fun o _ => fock_lattice_smul_mem hV o,
  fun m c => fock_lattice_monomial_iff hV m c, fock_lattice_iff_monomials hV, fun u h F hF => fock_lattice_linear_map_closed hV u h F hF,
  fun m m' c z h hz => fock_lattice_monomial_rescale hV m m' c z h hz, fun u h F hF => integral_poly_linear_map_closed u h F hF,
  fun m z => integer_monomial_mem_integral m z, mem_integral_poly_iff_coeff⟩

end Formalism.MainNotions.G.GLWeightTheory
