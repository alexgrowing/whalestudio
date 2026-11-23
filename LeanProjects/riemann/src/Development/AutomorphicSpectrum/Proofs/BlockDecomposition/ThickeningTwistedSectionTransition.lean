import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mul_mul_cancel_of_eq_one {A : Type*} [CommRing A] (a b c : A) (h : b * c = 1) :
    a * b * c = a := by
  rw [mul_assoc, h, mul_one]

theorem mul_mul_cancel_of_eq_one' {A : Type*} [CommRing A] (a b c : A) (h : c * b = 1) :
    a * b * c = a := by
  rw [mul_assoc, mul_comm b, h, mul_one]

theorem mulT_bijective_of_inverse :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  intro R _ I Y β hβ N v hN d ι D e t S σ y h
  have hc : ∀ i : (N e).ι, @HMul.hMul (Γ((Y e).left, D e S ⊓ (N e).U i)) (Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ (GlobalTheory.LB.coord σ i) (GlobalTheory.LB.coord y i) = 1 := by
    intro i
    have := congrArg (fun z : SecOn (pw (N e) (d + -d)) (D e S) =>
      GlobalTheory.LB.coord z (show (pw (N e) (d + -d)).ι from i)) h
    exact this
  let g : Tm I Y N D d e (t + 1) S →ₗ[R] Tm I Y N D d e t S :=
    mulRight (toR I Y e) (show d * (t + 1) + -d = d * t by ring) y
  refine Function.bijective_iff_has_inverse.2 ⟨g, ?_, ?_⟩
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one' (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
