import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetMul

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section Rename₂

variable {Lt Lt' : Type} {N0 N1 : ℕ}

def pEmb (φ : Lt ↪ Lt') (γ : Type) : Lt × γ ↪ Lt' × γ := φ.prodMap (Function.Embedding.refl γ)

theorem pEmb_apply (φ : Lt ↪ Lt') (γ : Type) (v : Lt × γ) : pEmb φ γ v = (φ v.1, v.2) := rfl

def xzMap (φ : Lt ↪ Lt') : XZ Lt N0 N1 → XZ Lt' N0 N1 :=
  Sum.map (pEmb φ (ℕ × Fin N0)) (pEmb φ (Fin N0 × Fin N1))

def xzEmb (φ : Lt ↪ Lt') : XZ Lt N0 N1 ↪ XZ Lt' N0 N1 :=
  ⟨xzMap φ, Function.Injective.sumMap (pEmb φ _).injective (pEmb φ _).injective⟩

theorem rename_minorXZ (φ : Lt ↪ Lt') (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) φ) (minorXZ N0 N1 s p I) = minorXZ N0 N1 (φ s) p I := by
  unfold minorXZ
  have h := RingHom.map_det (MvPolynomial.rename (R := ℤ) (xzMap (N0 := N0) (N1 := N1) φ)).toRingHom
    (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
      MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext i k
  simp [xzMap, pEmb]

theorem minorXZ_supported (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I ∈ MvPolynomial.supported ℤ (xzLetter (Lt := Lt) (N0 := N0) (N1 := N1) ⁻¹' {s}) := by
  unfold minorXZ
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  simp only [Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ ?_ ?_
  · exact MvPolynomial.X_mem_supported.mpr (by simp [xzLetter])
  · exact MvPolynomial.X_mem_supported.mpr (by simp [xzLetter])

theorem split_embDomain (φ : Lt ↪ Lt') (μ : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp (Finsupp.embDomain (xzEmb φ) μ) =
      (Finsupp.embDomain (pEmb φ (ℕ × Fin N0)) (Finsupp.sumFinsuppEquivProdFinsupp μ).1,
        Finsupp.embDomain (pEmb φ (Fin N0 × Fin N1)) (Finsupp.sumFinsuppEquivProdFinsupp μ).2) := by
  refine Prod.ext ?_ ?_
  · ext y
    rw [Finsupp.fst_sumFinsuppEquivProdFinsupp]
    by_cases hy : y ∈ Set.range (pEmb φ (ℕ × Fin N0))
    · obtain ⟨y0, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.fst_sumFinsuppEquivProdFinsupp,
        show (Sum.inl (pEmb φ (ℕ × Fin N0) y0) : XZ Lt' N0 N1) = xzEmb φ (Sum.inl y0) from rfl,
        Finsupp.embDomain_apply_self]
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hy, Finsupp.embDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      cases x with
      | inl x => exact hy ⟨x, Sum.inl_injective hx⟩
      | inr x => cases hx
  · ext y
    rw [Finsupp.snd_sumFinsuppEquivProdFinsupp]
    by_cases hy : y ∈ Set.range (pEmb φ (Fin N0 × Fin N1))
    · obtain ⟨y0, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.snd_sumFinsuppEquivProdFinsupp,
        show (Sum.inr (pEmb φ (Fin N0 × Fin N1) y0) : XZ Lt' N0 N1) = xzEmb φ (Sum.inr y0) from rfl,
        Finsupp.embDomain_apply_self]
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hy, Finsupp.embDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      cases x with
      | inl x => cases hx
      | inr x => exact hy ⟨x, Sum.inr_injective hx⟩

variable [Fintype Lt] [DecidableEq Lt] [Fintype Lt'] [DecidableEq Lt'] (l : ℕ) [Fact l.Prime]

theorem applyTerm_rename (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyTerm l (MvPowerSeries.rename (pEmb φ (Fin N0 × Fin N1)) T) (Finsupp.embDomain (xzEmb φ) μ) c =
      MvPolynomial.rename (pEmb φ (ℕ × Fin N0)) (applyTerm l T μ c) := by
  unfold applyTerm
  rw [split_embDomain, MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain]
  congr 2
  · rw [Finsupp.prod_embDomain]
  · exact MvPowerSeries.coeff_embDomain_rename _ _ _

theorem applyAt0_rename (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (MvPowerSeries.rename (pEmb φ (Fin N0 × Fin N1)) T) (MvPolynomial.rename (xzMap φ) P) =
      MvPolynomial.rename (pEmb φ (ℕ × Fin N0)) (applyAt0 N0 N1 l T P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, applyAt0_monomial, applyAt0_monomial,
      show Finsupp.mapDomain (xzMap φ) μ = Finsupp.embDomain (xzEmb φ) μ from
        (Finsupp.embDomain_eq_mapDomain (xzEmb φ) μ).symm]
    exact applyTerm_rename l φ T μ c
  | add P Q hP hQ => rw [map_add, applyAt0_add, applyAt0_add, hP, hQ, map_add]

end Rename₂

theorem serIn_rename {Lt Lt' γ K : Type*} [CommSemiring K] (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × γ) K) :
    SerIn {v : Lt' × γ | v.1 ∈ Set.range φ}
      (MvPowerSeries.rename (φ.prodMap (Function.Embedding.refl γ)) T) := by
  intro ν hν v hv
  by_contra hvr
  apply hν
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨ν', rfl⟩
  rw [← Finsupp.embDomain_eq_mapDomain] at hv
  by_cases h : v ∈ Set.range (φ.prodMap (Function.Embedding.refl γ))
  · obtain ⟨w, rfl⟩ := h
    exact hvr ⟨w.1, rfl⟩
  · exact hv (Finsupp.embDomain_of_notMem_range _ _ _ h)

theorem norm_coeff_rename_le {σ τ K : Type*} [NormedCommRing K] (f : σ ↪ τ) (A : MvPolynomial σ K) {b : ℝ}
    (hb : 0 ≤ b) (hA : ∀ m, ‖MvPolynomial.coeff m A‖ ≤ b) (m : τ →₀ ℕ) :
    ‖MvPolynomial.coeff m (MvPolynomial.rename f A)‖ ≤ b := by
  by_cases h : ∃ m', Finsupp.mapDomain f m' = m
  · obtain ⟨m', rfl⟩ := h
    rw [MvPolynomial.coeff_rename_mapDomain f f.injective]
    exact hA m'
  · rw [MvPolynomial.coeff_rename_eq_zero f A m (fun u hu => absurd ⟨u, hu⟩ h)]
    simpa using hb

end PI.OrbJet.OJ

end
