import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Prodint
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumval
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUltraUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
import Mathlib

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.prodVal :
    ∀ (N : ℕ) [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ w : ℕ → ℕ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (w l : ℝ) * Real.log l ≤ (charSet ℂ P).ncard * Real.log (bnd N k)) ∧ ∀ (l : ℕ) [Fact l.Prime] (T : Finset (DirichletCharacter (PadicAlgCl l) N)), (T : Set _) ⊆ charSet (PadicAlgCl l) P → ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ (w l : ℝ) * Real.log l := by
  intro N _ k P hk hP
  obtain ⟨M, hM0, hlog, hprod⟩ := b_prodint k P hk hP
  refine ⟨fun l => padicValInt l M, fun T hT => (b_sumval M hM0 T hT).trans hlog, ?_⟩
  intro l _ T hTS
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hS : (charSet (PadicAlgCl l) P).Finite := Set.toFinite _
  have hint : ∀ χ ∈ charSet (PadicAlgCl l) P, IsIntegral ℤ (((1 : ℕ) : PadicAlgCl l) * alN k χ) := by
    intro χ _
    rw [Nat.cast_one, one_mul]
    exact (b_primmem k χ).2.2.1
  have hpr : ∏ᶠ (χ : DirichletCharacter (PadicAlgCl l) N) (_ : χ ∈ charSet (PadicAlgCl l) P),
      ((1 : ℕ) : PadicAlgCl l) * alN k χ = (M : PadicAlgCl l) := by
    simp only [Nat.cast_one, one_mul]
    exact hprod (PadicAlgCl l)
  have hu := b_ultra l hnorm (charSet (PadicAlgCl l) P) (fun χ => alN k χ) 1 M hS hM0 hint hpr
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hu
  calc ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ ∑ χ ∈ T, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum fun χ _ => le_max_right _ _
    _ ≤ ∑ χ ∈ hS.toFinset, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun χ hχ => hS.mem_toFinset.mpr (hTS (Finset.mem_coe.mpr hχ))) (fun _ _ _ => le_max_left _ _)
    _ ≤ _ := hu
