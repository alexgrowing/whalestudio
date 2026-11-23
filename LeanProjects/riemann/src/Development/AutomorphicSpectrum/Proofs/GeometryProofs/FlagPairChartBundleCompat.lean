import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGeneratedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGenerationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangularStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair

open GroundTheory.Heights₂.Heights.NumbersDVR (IsVerticalDivisor ratDiv)

theorem mem_dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {r : ℕ}
    (R : Subalgebra O Ω) (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

def dualBundle {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {ι : Type} {x : ι → Ω} {r : ℕ}
    (B : ChartBundle O x r (Fin r → Ω)) : ChartBundle O x r (Fin r → Ω) where
  lat c := dotDual (chartRing O x c) (B.lat c)
  stable c a ha e he := by
    rw [mem_dualBundle] at he ⊢
    intro l hl
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (he l hl)
  frame := GlobalTheory.T.chart_bundle_local_generation O Ω ι x r B (GlobalTheory.T.chart_bundle_finitely_generated O Ω ι x r B)
  overlap := GlobalTheory.T.chart_bundle_lattice_generators O Ω ι x r B.lat B.stable B.overlap (GlobalTheory.T.chart_bundle_finitely_generated O Ω ι x r B)

def dotForm (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) add_dotProduct (fun c a b => smul_dotProduct c a b) dotProduct_add
    (fun c a b => dotProduct_smul c a b)

theorem dotForm_apply (Ω : Type) [Field Ω] (r : ℕ) (a b : Fin r → Ω) : dotForm Ω r a b = a ⬝ᵥ b := rfl

theorem dotForm_flip_bijective (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotForm Ω r).flip := by
  have hinj : Function.Injective (dotForm Ω r).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    funext q
    have := LinearMap.congr_fun hb (Pi.single q 1)
    simpa [dotForm_apply, single_one_dotProduct] using this
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Subspace.dual_finrank_eq])).1 hinj

theorem isVerticalDivisor_swap {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O]
    {P : Ideal (MvPolynomial (Σ k, ι k) O)} {ϖ : O} {b : K → ℤ} {f g : MvPolynomial (Σ k, ι k) O}
    (h : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f where
  degrees := by
    obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
    exact ⟨bg, bf, hg, hf, by rw [← hb]; funext k; simp⟩
  num_not_mem := h.den_not_mem
  den_not_mem := h.num_not_mem
  vertical W hW := h.vertical W (by
    intro h0; apply hW; simp only [ratDiv] at h0 ⊢; omega)
  unit_off_special W hp hPW hrel hϖ := by
    obtain ⟨u, v, hu, hv, h1⟩ := h.unit_off_special W hp hPW hrel hϖ
    exact ⟨v, u, hv, hu, by rw [← neg_sub]; exact P.neg_mem h1⟩

theorem dualPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  intro O _ _ _ Ω _ _ K _ _ J _ y ϖ r B B' w w' x x' f g h
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_reversed_dual_basis Ω r w
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_reversed_dual_basis Ω r w'
  obtain ⟨htri, hdiag⟩ := GlobalTheory.T.reversed_dual_triangular Ω r w w' v v' hv hv' h.sameFlag
  have hdual : ∀ B₀ : ChartBundle O (segreVec y) r (Fin r → Ω),
      IsDualLat O y (dotForm Ω r) B₀.lat (dualBundle B₀).lat := by
    intro B₀
    refine ⟨dotForm_flip_bijective Ω r, fun s _ e => ?_⟩
    exact mem_dualBundle _ _ _
  refine ⟨dualBundle B, dualBundle B', v, v', fun c _ => ⟨rfl, rfl⟩, ?_⟩
  refine ⟨?_, ?_, htri, fun i => ?_, fun i => ?_⟩
  · exact GlobalTheory.T.dual_lattice_flag_frame O Ω K J y r (Fin r → Ω) (Fin r → Ω) B (dualBundle B) (dotForm Ω r) (hdual B) w x h.flag v
      (fun i j => by rw [dotForm_apply]; exact hv i j)
  · exact GlobalTheory.T.dual_lattice_flag_frame O Ω K J y r (Fin r → Ω) (Fin r → Ω) B' (dualBundle B') (dotForm Ω r) (hdual B') w' x'
      h.flag' v' (fun i j => by rw [dotForm_apply]; exact hv' i j)
  · have := isVerticalDivisor_swap (h.vertical i.rev)
    convert this using 1
    funext k
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  · show aeval y (g i.rev) = v.repr (v' i) i * aeval y (f i.rev)
    rw [h.generic i.rev, ← mul_assoc, hdiag i, one_mul]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair
