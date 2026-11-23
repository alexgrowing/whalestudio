import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.EmbSep

theorem v_intCast_eq_zero {C : Type} [Field C] (V : VF C) {n : ℤ} (hn : ¬ (V.l : ℤ) ∣ n) : V.v (n : C) = 0 := by
  have hint : ∀ m : ℤ, V.Ge 0 (m : C) := fun m => by
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) k
    · simpa using (VF.ge_natCast (V := V) k).neg
  have hp : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hn
  have h1 : (a : C) * (V.l : C) + (b : C) * (n : C) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) hab
  refine le_antisymm ?_ (hint n)
  by_contra hc
  have hc' : 0 < V.v (n : C) := lt_of_not_ge hc
  have h2 : 0 < V.v ((a : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (hint a))
  have h3 : 0 < V.v ((b : C) * (n : C)) := by
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hc' (le_add_of_nonneg_left (hint b))
  have h4 := V.v.map_lt_add h2 h3
  rw [h1, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem exists_v_sub_eq_zero {C : Type} [Field C] (V : VF C) {I : Type} [Fintype I] (M : Matrix I I C)
    (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) {j j' : I} (hj : j ≠ j') :
    ∃ i, V.v (M i j - M i j') = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ i, 0 < V.v (M i j - M i j') := fun i =>
    lt_of_le_of_ne ((h i j).sub (h i j')) (hc i).symm
  have hd0 : M.det ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hd
    exact WithTop.top_ne_zero hd
  have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (Ne.isUnit hd0)
  have h1 := congrFun (congrFun hM j) j
  have h2 := congrFun (congrFun hM j) j'
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply, Matrix.one_apply_ne hj] at h2
  have h3 : ∑ i, M⁻¹ j i * (M i j - M i j') = 1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have h4 : 0 < V.v (∑ i, M⁻¹ j i * (M i j - M i j')) := by
    refine V.v.map_lt_sum WithTop.zero_ne_top fun i _ => ?_
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (hpos i) (le_add_of_nonneg_left (inv_int M h hd j i))
  rw [h3, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem cmEmbeddings_integral_and_distinct_mod_maximal' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  refine ⟨hint, fun τ τ' hne => ?_⟩
  let b : (E →+* ℂ) → 𝓞 E := fun i => RingOfIntegers.basis E (equivReindex E i)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) c.F := Matrix.of fun i σ => embK c σ (b i)
  have hM : (algebraMap c.F ℂ).mapMatrix M = basisMatrix E := by
    ext i σ
    simp only [basisMatrix, Matrix.of_apply, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  have hdet : M.det ^ 2 = (discr E : c.F) := by
    apply (algebraMap c.F ℂ).injective
    rw [map_pow, RingHom.map_det, hM, map_intCast, discr_eq_basisMatrix_det_sq]
  let N : Matrix (E →+* ℂ) (E →+* ℂ) C := (ι.comp io).mapMatrix M
  have hN : N.det ^ 2 = (discr E : C) := by
    rw [← RingHom.map_det, ← map_pow, hdet, map_intCast]
  have hNi : ∀ i j, V.Ge 0 (N i j) := fun i j => hint j (b i)
  have hv : V.v N.det = 0 := by
    have h1 := v_intCast_eq_zero V hd
    rw [← hN, pow_two, V.v.map_mul] at h1
    have h0 : 0 ≤ V.v N.det := det_int N hNi
    refine le_antisymm ?_ h0
    rw [← h1]
    exact le_add_of_nonneg_right h0
  obtain ⟨i, hi⟩ := exists_v_sub_eq_zero V N hNi hv hne
  exact ⟨b i, hi⟩

end GlobalTheory.EmbSep
