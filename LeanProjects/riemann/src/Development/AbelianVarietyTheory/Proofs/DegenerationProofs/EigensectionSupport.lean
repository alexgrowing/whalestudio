import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.UT

theorem eigensection_support : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (q : QkPt D.toPre F N) τ, q.y = 0 → IsTor τ q.g → ∀ x, QkToAkU U.toUnifPre F N q x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) (s : Fam D.toPre F N) (c : F), U.ExpandsF F N w₀ t s → IsActOf A.A A.L N θ t t' → (∀ j, t'.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j) → ∀ β, (τ (Multiplicative.ofAdd β)).val ≠ c → ∀ j, (s.s β).f j = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN q τ hy hτ x hx θ hθ w₀ hw₀ t t' s c hs hact ht β hβ j
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hI D F N hN q).1
  have h₁ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).2 F N w₀ t t t' s s (c - 1) hs hs (fun i => by
    rw [ht i]
    simp only [liftFun, map_sub, map_one, sub_mul, _root_.one_mul, sub_add_cancel])
  have h₂ := symLift_acts_as_phi hL R I hI D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s _ hs h₁ hact
  have h₃ := ((TorusWeight.torus_weight hL R I hI D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 h₂ β j
  rw [sub_smul, one_smul, sub_add_cancel, DVR.smul_f, constBF_eq] at h₃
  have key : ∀ {S : Type} [CommRing S] (g : F →+* S) (a b : F) (y : S), a ≠ b → g b * y = g a * y → y = 0 := by
    intro S _ g a b y hab e
    have hu : IsUnit (g (a - b)) := (IsUnit.mk0 _ (sub_ne_zero.2 hab)).map g
    exact hu.mul_right_eq_zero.1 (by rw [map_sub, sub_mul, e, sub_self])
  exact key ((((DegPre.BF D.toPre F).left.presheaf.map (homOfLE le_top).op).hom).comp (gF D.toPre F)) _ c _ hβ h₃

end GlobalTheory.UT
