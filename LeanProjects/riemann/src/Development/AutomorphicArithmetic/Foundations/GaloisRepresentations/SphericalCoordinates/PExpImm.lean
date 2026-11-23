import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.expImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PbFlat → UpperTheory.Gal.W2.ExpImm0 → UpperTheory.Gal.W2.ExpImm := by
  intro hcomp hpre hpb h0 X A _ g y e he z₀ w hw
  apply h0 X A g y e he w
  have hsplit : ∀ z, e z = e (-z₀) * e (z₀ + z) := by
    intro z
    rw [← he.1, neg_add_cancel_left]
  have hhol : IsHolTo Set.univ (fun z => Over.Hom.left (e (z₀ + z))) :=
    GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp (φ := fun z => z₀ + z) he.2.2.1 isOpen_univ
      (by fun_prop) (Set.mapsTo_univ _ _)
  have hflat : Flat (fun z => Over.Hom.left (e (z₀ + z))) 0 w := by
    have hd : HasFDerivAt (fun z : Fin g → ℂ => z₀ + z) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
      (hasFDerivAt_id 0).const_add z₀
    refine (hpre (Fin g → ℂ) (Fin g → ℂ) A.left Set.univ (fun z => Over.Hom.left (e z)) he.2.2.1
      (fun z => z₀ + z) _ 0 w hd (Set.mem_univ _)).2 ?_
    simpa using hw
  have hpbA : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct A A)
  have h1 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (fst A A).left) =
      fun _ => (e (-z₀)).left := by
    funext z
    rw [← Over.comp_left, lift_fst]
  have h2 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (snd A A).left) =
      fun z => (e (z₀ + z)).left := by
    funext z
    rw [← Over.comp_left, lift_snd]
  have hconstHol : IsHolTo Set.univ (fun _ : Fin g → ℂ => (e (-z₀)).left) := by
    intro U f
    refine ⟨?_, differentiableOn_const _⟩
    by_cases hU : ⊤ ≤ (e (-z₀)).left ⁻¹ᵁ U
    · simp [hU]
    · simp [hU]
  have hconstFlat : Flat (fun _ : Fin g → ℂ => (e (-z₀)).left) 0 w := by
    intro U f _
    simp
  have hs : Flat (fun z => (lift (e (-z₀)) (e (z₀ + z))).left) 0 w := by
    refine hpb (Fin g → ℂ) _ A.left A.left X (fst A A).left (snd A A).left A.hom A.hom hpbA Set.univ
      _ 0 w isOpen_univ (Set.mem_univ _) ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h1]
      exact hconstHol
    · beta_reduce
      rw [h2]
      exact hhol
    · beta_reduce
      rw [h1]
      exact hconstFlat
    · beta_reduce
      rw [h2]
      exact hflat
  have hfe : (fun z => (e z).left) =
      fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (μ : A ⊗ A ⟶ A).left := by
    funext z
    rw [← Over.comp_left, ← Hom.mul_def, ← hsplit]
  rw [hfe]
  exact hcomp (Fin g → ℂ) _ A.left (μ : A ⊗ A ⟶ A).left _ 0 w hs
