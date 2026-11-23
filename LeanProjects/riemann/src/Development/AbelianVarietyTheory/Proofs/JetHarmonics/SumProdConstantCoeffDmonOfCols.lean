import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfCongrJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolCols

theorem colM_apply {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]

theorem sum_degree_colM {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]

theorem exists_col {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]

end GlobalTheory.SymbolCols

namespace GlobalTheory

open SymbolCols in

theorem sum_prod_constantCoeff_dmonOf_cols :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (u : ι → Fin d → k) (lam : Fin n → ι → Fin d → k) (α : ι → k) (al : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) k) (g E : Fin n → PS k 1 d), P.IsHomogeneous al.degree → (∀ b l l', al (l, b) ≠ 0 → (∃ mo ∈ P.support, mo (l', b) ≠ 0) → ∑ i, lam b l i * u l' i = if l = l' then α l else 0) → (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (g b) = coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) = P.coeff al * ∏ b, ((∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b)) := by
  intro R k _ _ φ d G ι _ _ n u lam α al P g E hP hpair hg
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hP (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) =
        if colM mo b = colM al b then
          (∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b) else 0 := by
    intro mo hmo b hb
    have hle : (colM mo b).degree ≤ al.degree := by
      rw [← hdeg mo hmo, ← sum_degree_colM]
      exact Finset.single_le_sum (f := fun b => (colM mo b).degree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    rw [constantCoeff_DmonOf_congr_jet k d (G.mapF φ) ι u (colM mo b) _ _
      (fun m hm => coeff_mul_congr al.degree _ _ (E b) (hg b) m (hm.trans hle))]
    have := constantCoeff_dmonOf_prod_linear R k φ d G ι u (lam b) α (colM al b) (colM mo b) (E b)
      (fun l l' hl hl' => hpair b l l' (by rwa [colM_apply] at hl)
        ⟨mo, hmo, by rwa [colM_apply] at hl'⟩) hb
    simpa only [colM_apply] using this
  rw [Finset.sum_eq_single al]
  · by_cases hal : al ∈ P.support
    · congr 1
      exact Finset.prod_congr rfl fun b _ => by rw [hval al hal b le_rfl, if_pos rfl]
    · rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul, zero_mul]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal
    rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul]

end GlobalTheory
