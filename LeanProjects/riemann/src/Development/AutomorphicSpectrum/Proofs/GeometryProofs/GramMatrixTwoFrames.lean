import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem valAt_sum_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
    (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (b : I → L) (x : I → V)
    (hx : ∀ p, M.ValAt z (b p) (Mz.pt (x p))) (a : I → Ω) (c : I → ℂ) (hc : ∀ p, ValAt ξ z (a p) (c p)) :
    M.ValAt z (∑ p ∈ s, a p • b p) (Mz.pt (∑ p ∈ s, c p • x p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Mz.pt_zero] using M.valAt_zero hz
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp, Mz.add]
    refine LieModel.ValAt.add ?_ ih
    obtain ⟨h1, g, hg, hg'⟩ := hc p
    have := (hx p).smul h1 g
    rw [hg, hg', ← Mz.pt_smul] at this
    exact this

theorem gramAt_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li)
    (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ)
    (hP : HodgeMetric.PolarisedAt 𝔐.t z) (hG : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) (hG' : 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ')
    (hb : ∀ q, b' q = ∑ p, T p q • b p) (hT : ∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) :
    Γ' = Tz.conjTranspose * Γ * Tz := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V Mz hP
  obtain ⟨v, hv, hΓ⟩ := hG
  obtain ⟨v', hv', hΓ'⟩ := hG'
  choose x hx using fun p => Mz.onto (v p) (hv p).isTanAt
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have key : ∀ q, Mz.pt (∑ p, Tz p q • x p) = v' q := fun q => by
    have h1 := valAt_sum_smul 𝔐.M Mz hz Finset.univ b x (fun p => by rw [hx]; exact hv p)
      (fun p => T p q) (fun p => Tz p q) (fun p => hT p q)
    rw [← hb q] at h1
    exact h1.unique 𝔐.tie.gen (hv' q)
  have e1 : ∀ p q, Γ p q = h (x p) (x q) := fun p q =>
    (hh _ _ _).1 (by rw [hx, hx]; exact hΓ p q)
  have e2 : ∀ p q, Γ' p q = h (∑ i, Tz i p • x i) (∑ j, Tz j q • x j) := fun p q =>
    (hh _ _ _).1 (by rw [key, key]; exact hΓ' p q)
  ext p q
  rw [e2]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1, map_sum, LinearMap.sum_apply, map_smul,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
