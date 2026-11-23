import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bichar_mem {C RC : Type} [Field C] [IsAlgClosed C] [CommRing RC] [IsDomain RC] [Algebra RC C]
    {v : Valuation C NNReal} (hv : v.Integers RC) {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup RC T)
    (β : T →* T →* RCˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap RC _ ((β a b : RCˣ) : RC)) :
    (fun z : T × T => ((β z.1 z.2 : RCˣ) : RC)) ∈ prodSpan (Γ.btOrder ⊤) := by
  haveI : ValuationRing RC := ValuationRing.of_integers v hv
  exact PositivityTheory.HtPt.Twpair.bichar_mem_prodSpan (PositivityTheory.HtPt.Twpair.henselian hv)
    (fun P => (PositivityTheory.HtPt.Twpair.prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h)
    Γ β s hs

theorem tens_of_bc {R RC C N : Type} [CommRing R] [CommRing RC] [Field C] [Algebra R RC] [Algebra RC C]
    [AddCommGroup N] (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (algebraMap R RC r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} {A' : Subalgebra RC (Multiplicative N → RC)}
    (ee : RC ⊗[R] A ≃ₐ[RC] A') (hee : ∀ (a : A) t, (ee (1 ⊗ₜ a)).1 t = algebraMap R RC (a.1 t))
    (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∀ g ∈ prodSpan A', (fun z : N × N =>
      algebraMap RC C (g (Multiplicative.ofAdd z.1, Multiplicative.ofAdd z.2))) ∈ GR.tens M M := by
  have lem : ∀ x : RC ⊗[R] A, (fun y => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd y))) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      convert M.zero_mem using 1
      funext y
      simp
    | tmul r a =>
      have e1 : r ⊗ₜ[R] a = r • ((1 : RC) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (fun y => algebraMap RC C ((ee (r ⊗ₜ[R] a)).1 (Multiplicative.ofAdd y))) =
          r • fun y => φ (a.1 (Multiplicative.ofAdd y)) := by
        funext y
        rw [e1, map_smul]
        simp [hee, hφ, Algebra.smul_def]
      rw [e2, hM]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a.1, a.2, rfl⟩)
    | add x y hx hy =>
      have e2 : (fun t => algebraMap RC C ((ee (x + y)).1 (Multiplicative.ofAdd t))) =
          (fun t => algebraMap RC C ((ee x).1 (Multiplicative.ofAdd t))) +
            (fun t => algebraMap RC C ((ee y).1 (Multiplicative.ofAdd t))) := by
        funext t
        simp
      rw [e2]
      exact M.add_mem hx hy
  have lem' : ∀ a ∈ A', (fun y => algebraMap RC C (a (Multiplicative.ofAdd y))) ∈ M := by
    intro a ha
    obtain ⟨x, hx⟩ := ee.surjective ⟨a, ha⟩
    have k := lem x
    rw [hx] at k
    exact k
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    refine Submodule.subset_span ⟨_, lem' a ha, _, lem' b hb, ?_⟩
    funext z
    simp
  | zero =>
    convert (GR.tens M M).zero_mem using 1
    funext z
    simp
  | add g₁ g₂ _ _ h₁ h₂ =>
    convert (GR.tens M M).add_mem h₁ h₂ using 1
    funext z
    simp
  | smul r g _ h =>
    convert (GR.tens M M).smul_mem r h using 1
    funext z
    simp [Algebra.smul_def]

end PositivityTheory.Xgn.TestGroupPoint
