import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsConeComplexBaseChange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]

omit [Fintype σ] in

theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange

open ConeComplexBaseChange in

theorem ConeComplexBaseChange.proof : ConeComplexBaseChange.Statement := by
  intro K _ ι _ P n s W' Wa hV hs hW hWh hWa
  obtain ⟨-, ⟨hPp, -, -⟩, hPh, hdim⟩ := hV
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [map_int_complex_eq, ← Ideal.map_map]; rfl
  have : W'.IsPrime := hW.1.1.1
  refine ⟨?_, fun Q hQ => ⟨?_, ?_⟩, ?_⟩
  · rw [hmapP]
    exact ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map _
  · have hQ' := hQ
    rw [hmapP] at hQ'
    rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
    rw [hdim, show n + 2 + Fintype.card K = (n + Fintype.card K + 1) + 1 by omega] at hQdim
    exact dim_cancel_one hQdim
  · intro hsQ
    apply hs
    rw [← comap_of_minimal P hPh Q hQ]
    exact hsQ
  · have hco : Wa.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W' := comap_of_minimal W' hWh Wa hWa
    have hPW : P ⊔ Ideal.span {s} ≤ W' := hW.1.1.2
    refine ⟨⟨hWa.1.1, le_trans (Ideal.map_mono hPW) hWa.1.2⟩, ?_⟩
    rintro Q' ⟨hQ'p, hQ'le⟩ hQ'W
    have h1 : P ⊔ Ideal.span {s} ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      Ideal.map_le_iff_le_comap.mp hQ'le
    have h2 : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W' := hco ▸ Ideal.comap_mono hQ'W
    have h3 : W' ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      hW.1.2 ⟨Ideal.comap_isPrime _ _, h1⟩ h2
    exact hWa.2 ⟨hQ'p, Ideal.map_le_iff_le_comap.mpr h3⟩ hQ'W

end GroundTheory.Heights₂.Heights.Targets
