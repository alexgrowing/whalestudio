import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

private theorem relDim_eq_of_smoothOfRelativeDimension_grp {X Y : Scheme.{0}} (f : X ⟶ Y) (n m : ℕ) (x : X)
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hQ⟩ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  have hp := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra! H
    exact hp.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 H))
  have : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : algebraMap Γ(X, V) (Localization.Away t) 1 = 0 := Subsingleton.elim _ _
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at h0
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := h0
    have hc' : t ^ k = 0 := by simpa using hc
    exact htp (hp.mem_of_pow_mem k (by rw [hc']; exact Ideal.zero_mem _))
  have hn' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    (Localization.Away t) t _ h
  have hm' := hQ t ht
  let := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) (Localization.Away t) := hn'
  have a1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have : Algebra.IsStandardSmoothOfRelativeDimension m Γ(Y, U) (Localization.Away t) := hm'
  have a2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast a1.symm.trans a2

private theorem exists_limit_fan_smooth_relDim_mul {S : Scheme.{0}} (A : Over S) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom) :
    ∀ k : ℕ, ∃ c : Fan (fun _ : Fin k => A), Nonempty (IsLimit c) ∧
      SmoothOfRelativeDimension (k * g) c.pt.hom := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fan.mk (𝟙_ (Over S)) (fun i => Fin.elim0 i), ⟨Fan.IsLimit.mk _
      (fun s => CartesianMonoidalCategory.toUnit s.pt) (fun _ i => Fin.elim0 i)
      (fun _ _ _ => CartesianMonoidalCategory.toUnit_unique _ _)⟩, ?_⟩
    rw [zero_mul]
    show SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ k ih =>
    obtain ⟨c, ⟨hc⟩, hsm⟩ := ih
    refine ⟨extendFan (f := fun _ : Fin (k + 1) => A) c
      (BinaryFan.mk (CartesianMonoidalCategory.fst A c.pt) (CartesianMonoidalCategory.snd A c.pt)),
      ⟨extendFanIsLimit (fun _ : Fin (k + 1) => A) hc
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct A c.pt)⟩, ?_⟩
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (k * g)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (k * g)
    have h1 : SmoothOfRelativeDimension (k * g) (pullback.fst A.hom c.pt.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback A.hom c.pt.hom).flip hsm
    have h2 := smoothOfRelativeDimension_comp (n := k * g) (m := g) (pullback.fst A.hom c.pt.hom) A.hom
    rw [Nat.succ_mul]
    exact h2

theorem rank_and_g_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j), D'.rank = j * D.rank ∧ D'.P.g = j * D.P.g := by
  intro R _ _ j D D' pD
  rcases pD with ⟨pw, w, wg, wr, xe, cpr, wpsi⟩
  refine ⟨?_, ?_⟩
  · have e : D'.X ≃ₗ[ℤ] (Fin j → D.X) := xe.toIntLinearEquiv
    unfold DegPre.rank
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rcases pw with ⟨pr, hom, lim⟩
    obtain ⟨c, ⟨hc⟩, hsm⟩ := exists_limit_fan_smooth_relDim_mul D.P.A D.P.g D.P.5 j
    let e := IsLimit.conePointUniqueUpToIso lim hc
    have hw : e.hom.left ≫ c.pt.hom = D'.P.A.hom := Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := j * D.P.g) e.hom.left c.pt.hom
    rw [hw, zero_add] at h3
    let := D'.P.2
    have p : (𝟙_ (Over (Spec (CommRingCat.of R)))).left := (inferInstance : Nonempty (PrimeSpectrum R)).some
    exact relDim_eq_of_smoothOfRelativeDimension_grp D'.P.A.hom _ _ ((η[D'.P.A]).left p) D'.P.5 h3

end GlobalTheory
