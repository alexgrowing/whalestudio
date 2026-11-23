import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def HomUniqSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ψ ψ' : Pt k 1 d),
    (∀ i, constantCoeff (ψ i) = 0) → (∀ i, constantCoeff (ψ' i) = 0) →
    comp1 ψ (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ (pt k (n := 2) d 0)) (comp1 ψ (pt k (n := 2) d 1)) →
    comp1 ψ' (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ' (pt k (n := 2) d 0)) (comp1 ψ' (pt k (n := 2) d 1)) →
    dLin ψ = dLin ψ' → ψ = ψ'

namespace HomUniqPf

open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz1 {n : ℕ} (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0) : CZ (![a] : Fin 1 → Pt k n d) := by
  intro j i
  fin_cases j
  exact ha i

theorem cz_pt {n : ℕ} (j : Fin n) : ∀ i, constantCoeff (pt k (n := n) d j i) = 0 := fun i => by
  unfold pt
  exact MvPowerSeries.constantCoeff_X _

private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']

theorem cz_comp1 {n : ℕ} (φ : Pt k 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (a : Pt k n d)
    (ha : ∀ i, constantCoeff (a i) = 0) : ∀ i, constantCoeff (comp1 φ a i) = 0 := by
  unfold comp1
  intro i
  rw [cc_ev_lemma (cz1 a ha), hφ i]

end HomUniqPf

end ReciprocityTheory.ChartRestriction.G.TB
