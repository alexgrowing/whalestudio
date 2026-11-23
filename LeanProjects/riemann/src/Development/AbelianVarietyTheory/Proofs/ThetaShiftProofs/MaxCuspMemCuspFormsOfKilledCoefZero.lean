import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoordsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusActionStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

namespace MaxCuspBwd

open MeasureTheory Complex GlobalTheory.TorusFourier

theorem integral_eq_zero_of_coeffs {ι : Type} [Fintype ι] {N : ℕ} {Γ : AddSubgroup (ι → ℝ)}
    {D : Set (ι → ℝ)} (hD : IsAddFundamentalDomain Γ D volume) (h0 : volume D ≠ 0)
    (h1 : volume D ≠ ⊤) (L : (ι → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (g : (Fin N → ℝ) → ℂ) (hc : Continuous g)
    (hper : ∀ u (n : Fin N → ℤ), g (u + fun i => (n i : ℝ)) = g u)
    (hL : ∀ p ∈ Γ, ∀ k, ∃ z : ℤ, L p k = z) (ν : ι → ℝ)
    (hν : ∀ p ∈ Γ, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k)
    (h : ∀ m : Fin N → ℤ, (∀ s, ∑ k, (m k : ℝ) * L s k = 2 * ∑ τ, ν τ * s τ) →
      ∫ t in cube N, g t * chr (fun k => (m k : ℝ)) t = 0) :
    ((volume D).toReal : ℂ)⁻¹ *
      ∫ s in D, g (L s) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) = 0 := by
  classical
  set ν' : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ τ, (2 * ν τ) • LinearMap.proj τ with hν'd
  have hν'a : ∀ s, ν' s = 2 * ∑ τ, ν τ * s τ := fun s => by
    simp [hν'd, Finset.mul_sum, mul_assoc]
  have hf : ∀ i x, g (x + Pi.basisFun ℝ (Fin N) i) = g x := fun i x => by
    rw [← hper x (Pi.single i 1)]
    congr 2
    funext k
    by_cases hk : k = i <;> simp [hk]
  have hf₁ : ∀ l ∈ Γ, ∀ x, g (x + L l) = g x := fun l hl x => by
    choose z hz using hL l hl
    rw [← hper x z]
    congr 2
    funext k
    exact hz k
  have key := ((partialCoeff_spec_cube (Pi.basisFun ℝ (Fin N)) hD h0 h1 L hc hf hf₁).1 ν'
    (fun l hl => by rw [hν'a]; exact hν l hl)).2.2.2.2 (fun χ hχ hχL => by
      choose m hm using hχ
      have hsum : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t => by
        simpa using (Pi.basisFun ℝ (Fin N)).sum_repr t
      have hχa : ∀ t : Fin N → ℝ, χ t = ∑ k, t k * (m k : ℝ) := fun t => by
        conv_lhs => rw [← hsum t]
        simp only [map_sum, map_smul, hm, smul_eq_mul]
      have h2 := h m fun s => by
        rw [← hν'a, ← hχL, LinearMap.comp_apply, hχa]
        simp only [mul_comm]
      rw [← h2, cubeCoeff, cube, Set.pi_univ_Icc]
      simp only [hsum, eNeg, chr, hχa]
      rfl)
  have h3 := congrFun key 0
  rw [partialCoeff, coeff_eq] at h3
  simp only [zero_add, hν'a, Pi.zero_apply] at h3
  rw [← h3, Measure.real]
  congr 2
  funext s
  congr 2
  push_cast
  ring

end MaxCuspBwd

open MeasureTheory Complex in

theorem maxCusps_mem_SSgt_of_coef_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) → (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la → (∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0) → P ∈ X.SSgt la c := by
  intro E _ _ _ r ρ X hcu hbas la hchi c P hP hK
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  obtain ⟨cu, hspan⟩ := hcu ξ hξ
  obtain ⟨η, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hspan
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  obtain ⟨L, hflow, hph, hLint⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hξ.1
  have hη : η ≠ 0 := by
    rintro rfl
    exact hξ.2.2 (by simp)
  have hsec : X.IsSec la P := hP.1.1
  unfold Data.fj
  split_ifs with hfreq hdom
  · obtain ⟨-, hD, h0, h1⟩ := hdom.choose_spec
    simp only [hflow]
    refine MaxCuspBwd.integral_eq_zero_of_coeffs hD h0.ne' h1.ne L (fun u => P (zAct X cu u x))
      ?_ (maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx) (hLint la) ν hfreq fun m hm => ?_
    · exact hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x)
        fun t => zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) t x hx
    · obtain ⟨χ, hχ, hχm⟩ := GlobalTheory.T.hermitian_matrix_realizes_cusp_coords E r ρ X cu hb m
      have hνχ : ∀ τ : X.Ψ, (τ.1 (hq χ η)).re = ν τ := fun τ => by
        classical
        have h2 := hph χ hχ (Pi.single τ 1)
        simp only [hχm] at h2
        rw [hm] at h2
        simpa [Pi.single_apply] using h2.symm
      have h3 := hK cu χ ⟨hχ, fun k => ⟨m k, hχm k⟩⟩
        ⟨η, hη, hξ.1, by simpa only [hνχ] using hν⟩ x hx
      rw [show phZ X cu χ = fun k => (m k : ℝ) from funext hχm] at h3
      exact h3
  · rfl
  · rfl

end GlobalTheory
