import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonvanishingPoint

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_functional_ne_zero_projective {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] {m : M} (hm : m ≠ 0) : ∃ l : M →ₗ[B] B, l m ≠ 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B M)
  by_contra hall
  push_neg at hall
  apply hm
  have h0 : s m = 0 := by
    ext a
    simpa using hall (Finsupp.lapply a ∘ₗ s)
  have := LinearMap.congr_fun hs m
  simpa [h0] using this.symm

private theorem exists_point_nonvanishing_reduced (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [IsReduced B] {c : B} (hc : c ≠ 0) :
    ∃ x : B →ₐ[k] k, x c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced k B hc

theorem UpperTheory.Gal.Ord.dz1 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] [Module.Projective B Ω[B⁄k]] (r : B),
      (∀ v : B →ₐ[k] DualNumber k, TrivSqZeroExt.snd (v r) = 0) → KaehlerDifferential.D k B r = 0 := by
  intro k _ _ B _ _ _ _ _ r hv
  by_contra hne
  obtain ⟨l, hl⟩ := exists_functional_ne_zero_projective (B := B) hne
  obtain ⟨x, hx⟩ := exists_point_nonvanishing_reduced k B hl
  let d : B →ₗ[k] k := x.toLinearMap ∘ₗ (l.restrictScalars k) ∘ₗ (KaehlerDifferential.D k B).toLinearMap
  have hd : ∀ b, d b = x (l (KaehlerDifferential.D k B b)) := fun _ => rfl
  let f : B →ₗ[k] DualNumber k :=
    Algebra.linearMap k (DualNumber k) ∘ₗ x.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ d
  have hal : ∀ c : k, algebraMap k (DualNumber k) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hfst : ∀ b, TrivSqZeroExt.fst (f b) = x b := fun b => by simp [f, hal]
  have hsnd : ∀ b, TrivSqZeroExt.snd (f b) = d b := fun b => by simp [f, hal]
  let v : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap f
    (by
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hsnd, hd])
    (by
      intro a b
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hfst, hsnd, hd, Derivation.leibniz, mul_comm, add_comm])
  apply hx
  have := hv v
  simpa [v, hsnd, hd] using this
