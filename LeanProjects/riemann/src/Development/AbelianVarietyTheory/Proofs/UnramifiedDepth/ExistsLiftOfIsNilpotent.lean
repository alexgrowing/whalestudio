import Mathlib
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TangentLift

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_lift_of_isNilpotent {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] {B C : CommRingCat.{0}} (π : B ⟶ C)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π.hom)) (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X)
    (h : x₀ ≫ f = Spec.map π ≫ s) (e : X) (he : ∀ p, x₀ p = e) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair f e (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap π.hom) := by
      rw [range_comap_of_surjective _ _ hπ, (PrimeSpectrum.zeroLocus_eq_univ_iff _).2]
      · trivial
      · obtain ⟨n, hn⟩ := hn
        intro a ha
        exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow ha n⟩
    obtain ⟨p', rfl⟩ := hp
    have e' : f (x₀ p') = s (Spec.map π p') := congr($h p')
    have : s (Spec.map π p') ∈ U := by
      rw [← e', he p']
      exact hVU hxV
    exact this
  · rintro _ ⟨p, rfl⟩
    rw [he]
    exact hxV
  · intro R A _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

variable {k : Type} [Field k]

theorem smooth_q (φ : Fib k) : Smooth φ.q.left := by
  have := φ.q_flat
  have := φ.q_surj
  have := φ.q_affine
  have := (H1.torus_dim (Sp k) φ.X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback φ.i φ.q φ.isKernel).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact φ.q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

def toDual : JetR k Unit 1 →ₐ[k] DualNumber k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun _ => DualNumber.eps)
    (aeval_kill 1 _ (Ideal.span {DualNumber.eps}) (fun _ => Ideal.subset_span rfl) (by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
      exact DualNumber.eps_pow_two))

end GlobalTheory.TangentLift
