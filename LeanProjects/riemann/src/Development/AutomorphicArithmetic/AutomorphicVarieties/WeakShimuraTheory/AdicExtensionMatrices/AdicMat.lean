import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {Γ S ι : Type} [TopologicalSpace Γ] [Fintype ι] (f : Γ → Matrix ι ι S)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  exact this.mono fun y hy => Matrix.ext hy

theorem UpperTheory.V.Ws.sxAdicMat :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (M : Γ → M4 R), (∀ i j, AdicCont I fun g => M g i j) → (∀ n, AdicCont I fun g => (M g).charpoly.coeff n) ∧ ∀ (U V : M4 R) i j, AdicCont I fun g => (U * M g * V) i j := by
  intro Γ R _ _ I M h
  have hl : ∀ N : ℕ, IsLocallyConstant fun g => (M g).map (Ideal.Quotient.mk (I ^ N)) :=
    fun N => lc_mat _ fun i j => h i j N
  refine ⟨fun n N => ?_, fun U V i j N => ?_⟩
  · have := (hl N).comp fun A => A.charpoly.coeff n
    convert this using 2 with g
    simp only [Function.comp, Matrix.charpoly_map, Polynomial.coeff_map]
  · have := (hl N).comp fun A =>
      (U.map (Ideal.Quotient.mk (I ^ N)) * A * V.map (Ideal.Quotient.mk (I ^ N))) i j
    convert this using 2 with g
    simp only [Function.comp, ← Matrix.map_mul, Matrix.map_apply]
