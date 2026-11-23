import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma realTrace_toLin (g : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) :
    ((LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) : ℝ) : ℂ) =
      H.trace + (starRingEnd ℂ) H.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin g))),
    LinearMap.restrictScalars_toMatrix]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.comp_apply, Matrix.map_apply]
  have hb : ∀ z : ℂ, ∑ a, Algebra.leftMulMatrix Complex.basisOneI z a a = 2 * z.re := by
    intro z
    rw [← Algebra.trace_complex_apply, Algebra.trace_eq_matrix_trace Complex.basisOneI]
    rfl
  simp only [hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', map_sum, ← Finset.sum_add_distrib,
    Complex.add_conj]
  push_cast
  rfl

private lemma trace_of_basis (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ)
    (P : L →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ) (hf : ∀ x, P (f x) = H *ᵥ P x) :
    ((LinearMap.trace ℤ L f : ℤ) : ℝ) =
      LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let Lsub : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  have hcar : (Lsub : Set (Fin g → ℂ)) = Set.range P := LinearMap.coe_range _
  haveI : DiscreteTopology Lsub := hd
  haveI : IsZLattice ℝ Lsub := ⟨by rw [hcar]; exact hs⟩
  let e : L ≃ₗ[ℤ] Lsub := LinearEquiv.ofInjective P.toIntLinearMap hinj
  let bV := (b.map e).ofZLatticeBasis ℝ Lsub
  have hbV : ∀ i, bV i = P (b i) := fun i => by
    simp [bV, e]
    rfl
  rw [LinearMap.trace_eq_matrix_trace ℤ b, LinearMap.trace_eq_matrix_trace ℝ bV]
  have hM : LinearMap.toMatrix bV bV ((Matrix.toLin' H).restrictScalars ℝ) =
      (LinearMap.toMatrix b b f).map (Int.cast : ℤ → ℝ) := by
    ext i j
    have hsum : (Matrix.toLin' H).restrictScalars ℝ (bV j) =
        ∑ k, ((b.repr (f (b j)) k : ℤ) : ℝ) • bV k := by
      rw [LinearMap.restrictScalars_apply, hbV, Matrix.toLin'_apply, ← hf]
      conv_lhs => rw [← b.sum_repr (f (b j))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, hbV, Int.cast_smul_eq_zsmul]
    rw [LinearMap.toMatrix_apply, hsum, Matrix.map_apply, LinearMap.toMatrix_apply, bV.repr_sum_self]
  rw [hM, Matrix.trace, Matrix.trace]
  simp

theorem UpperTheory.Gal.W2.traceLat_of :
    UpperTheory.Gal.W2.TraceLat := by
  intro L _ _ _ g P hinj hd hs f H hf
  rw [← realTrace_toLin, ← trace_of_basis L g P hinj hd hs f H hf]
  push_cast
  rfl
