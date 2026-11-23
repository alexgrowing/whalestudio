import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.TwistNoBasePoint

section
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.NoBasePoint

theorem exists_sec_of_unitAt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt L φ ε y) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), y ∈ nonzeroLocus s := by
  obtain ⟨s, hs⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact ⟨s, (mem_nonzeroLocus s y).2 ⟨fun i => J (𝟙 _ ≫ φ i), Good.mem hJ φ (𝟙 _), hs J hJ⟩⟩

theorem unitAt_twist (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K))
    (x : baseOver (Sp K) ⟶ P.A) (p : (baseOver (Sp K)).left) (m : ℕ) (b : baseOver (Sp K) ⟶ P.A) :
    UnitAt P.L ![(translPt P.A b).left, (snd (baseOver (Sp K)) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left p) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  let t : Spec (CommRingCat.of K) ⟶ Sp K := 𝟙 _
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 : Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L (1 : ℕ) (Over.mk t)) = 1 ^ P.g :=
    hL.globalSectionsRank K P 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let y : (Over.mk t ⊗ P.A).left := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square _ P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m b

end

theorem exists_sec_twist :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ), 4 ≤ n → ∀ c x : Out.baseOver (Sp k) ⟶ P.A, ∃ s : LB.Sec (Out.twistLB P.A P.L n c), ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) := by
  intro hL _ k _ _ P n hn c x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let p : (Out.baseOver (Sp k)).left := IsLocalRing.closedPoint k
  have h : H1.SquareUnits.UnitAt P.L (K := Fin 2)
      ![(snd (Out.baseOver (Sp k)) P.A).left, (Out.translPt P.A c).left] ![((m + 2 : ℕ) : ℤ) - 1, 1]
      ((Out.ptSecT P.A x).left p) := by
    refine H1.SquareUnits.UnitAt.congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_) (unitAt_twist hL k P x p m c)
    simp [Fin.sum_univ_succ]
    module
  obtain ⟨s, hs⟩ := exists_sec_of_unitAt P.isLB h
  refine ⟨s, fun q _ => ?_⟩
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact hs

end GlobalTheory.TwistNoBasePoint
