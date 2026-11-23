import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVerticalTwistGenDeg

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

theorem exists_multilinear_gen {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P (d + 1)) :
    ∃ F : MultilinearMap ℤ (fun _ : Fin d => K → ℤ) ℤ,
      ∀ bs, F bs = NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) bs := by
  have hX : IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) d := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  exact ⟨intNumMultilinear _ d hXN.multiHomog hXN.relevant hd, fun _ => rfl⟩

end SheetDecomposition
