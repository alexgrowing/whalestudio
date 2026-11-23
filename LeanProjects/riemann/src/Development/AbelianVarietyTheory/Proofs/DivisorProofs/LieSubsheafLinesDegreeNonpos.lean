import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSquaringPathWithTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPathStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlacesStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem linesLE_zero_of_sub_lie : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → LinesLE g 0 := by
  intro k K _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s g hV₀ hs hg hloc
  intro E _ _ _ _ _ ρ hρ w hw
  simp only [zero_mul]
  by_contra hpos
  push_neg at hpos
  have hpos' : 0 < degLine (pullAd ρ g) w := by exact_mod_cast hpos
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  letI : Algebra ℚ E := DivisionRing.toRatAlgebra

  have hne : Nonempty (Place k E) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [degLine, finsum_of_isEmpty] at hpos'
  obtain ⟨p₀⟩ := hne
  obtain ⟨b₀, V, t, V', h₀, h₁, hxV, M, -, -, -, -, -⟩ := hloc (ρ p₀)
  set b : Sp E ⟶ C := spMap (algebraMap K E) ≫ x with hb
  have hbV : ⊤ ≤ b ⁻¹ᵁ V₀ := by
    intro z _
    have hz := h₀ (hxV (show (spMap (algebraMap K E)).base z ∈ (⊤ : (Sp K).Opens) from trivial))
    show b.base z ∈ V₀
    simpa [hb] using hz
  haveI : QuasiSeparated G.hom := inferInstance
  obtain ⟨ξ, hξ, htan⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G E hG.smooth inferInstance b r V₀ (fun j => i.app V₀ (s j)) w hbV

  have hvec : ∀ p : Place k E, (pullAd ρ g p).mulVec w ≠ 0 := by
    intro p h
    have hdet : (pullAd ρ g p).det ≠ 0 := by
      simp only [pullAd]
      have e := RingHom.map_det (algebraMap K E) (g (ρ p))
      rw [RingHom.mapMatrix_apply] at e
      rw [← e]
      exact (map_ne_zero _).mpr (hg.1 (ρ p))
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
  have hu : ∀ p : Place k E, ∃ u : E, u ≠ 0 ∧ p.1 u = nrm p ((pullAd ρ g p).mulVec w) ∧
      ordVec p ((pullAd ρ g p).mulVec w) = ord p u := by
    intro p
    obtain ⟨j, hj0, hj1, hj2, -⟩ := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k E p).2.2.2.2.2.2.1) r _ (hvec p)
    exact ⟨_, hj0, hj1.symm, hj2⟩
  choose u hu0 hu1 hu2 using hu
  have hsum : ∑ᶠ p, ord p (u p) = degLine (pullAd ρ g) w := by
    unfold degLine; exact finsum_congr fun p => (hu2 p).symm
  have hfin : {p | ord p (u p) ≠ 0}.Finite := by
    by_contra hinf
    have : ∑ᶠ p, ord p (u p) = 0 := finsum_of_infinite_support (by simpa [Function.support] using hinf)
    omega
  have hint := fun p => GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath k K E C x hx G hG W r i V₀ s ρ hρ p (g (ρ p)) (hloc (ρ p)) w (u p) (hu0 p) (hu1 p) ξ hξ htan
  have hrat := GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces k K E C x hx G ξ u hu0 hfin (by omega) hint
  have htriv : ξ = triv G b := GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian C G hG E b ξ hξ hrat
  rw [htriv] at htan
  exact hw (GlobalTheory.T.tangent_constantPath_eq_zero k K E C x hx G hG W r i hi V₀ s hV₀ hs w htan)

end GlobalTheory.Nef
