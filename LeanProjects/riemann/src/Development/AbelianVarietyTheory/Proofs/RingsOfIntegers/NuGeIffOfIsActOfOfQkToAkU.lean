import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nuGe_iff_of_isActOf_of_qkToAkU : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G), Geo.Tor.ExpBijF U.toUnifPre → ∀ (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := V) F)) (p : QkPt D.toPre F k), QkToAkU U.toUnifPre F k p θ.pt → ∀ (n : ℕ), 1 ≤ n → θ.pt ^ n = 1 → LB.Gen.Corr A.L _ _ _ _ (Out.powGen A.A A.L (k : ℤ) θ n) (LB.oneGen A.L) → ∀ (t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam D.toPre F k), U.ExpandsF F k w t s → U.ExpandsF F k w t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U hB Q hQ F _ _ v hv k hk w hw θ p hp n hn hx hc t t' s s' hs hs' hact r
  obtain ⟨w₀, hw₀, hΦθ⟩ := (hp w hw).2 θ rfl
  obtain ⟨hB₁, hB₂⟩ := hB F k hk w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w₀ hw₀
  choose act hact' using fun x : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)) =>
    (VVRank.exists_isTwistPull A.A A.isLB θ.isGen x : ∃ y, IsActOf A.A A.L (k : ℤ) θ x y)
  have hfin : FinOrd D F k p w₀ 1 := by
    refine ⟨n, hn, fun ss ts hss => ?_⟩
    obtain ⟨t₀, ht₀, -⟩ := hB₂ (ss 0)
    have key : ∀ (i : ℕ) (hi : i < n + 1), U.ExpandsF F k w (act^[i] t₀) (ss ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero => exact fun _ => ht₀
      | succ i ih =>
        intro hi
        obtain ⟨s₁, hs₁, -⟩ := hB₁ (act^[i + 1] t₀)
        have h₁ := (hΦ _ _).1 (hΦθ _ _ _ _ (ih (by omega)) hs₁
          (by rw [Function.iterate_succ_apply']; exact hact' _))
        obtain ⟨h₂, h₃⟩ := hss ⟨i, by omega⟩
        have h₄ : ss ⟨i + 1, hi⟩ = s₁ :=
          ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h₃).trans
            ((one_smul F _).trans (((hΦ _ _).1 h₂).trans h₁.symm))
        rw [h₄]; exact hs₁
    have hcyc := thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB (k : ℤ) _ θ n hx hc
      (fun i => act^[i.val] t₀) (fun i => by
        show IsActOf _ _ _ θ (act^[i.val] t₀) (act^[i.val + 1] t₀)
        rw [Function.iterate_succ_apply']; exact hact' _)
    have he : act^[n] t₀ = t₀ := by
      have ext : ∀ a b : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)), (∀ j, a.f j = b.f j) → a = b := by
        rintro ⟨a, _⟩ ⟨b, _⟩ h
        obtain rfl : a = b := funext h
        rfl
      exact ext _ _ hcyc
    have h₅ := key n (Nat.lt_succ_self n)
    rw [he] at h₅
    have h₆ : ss (Fin.last n) = ss 0 := (hB₁ t₀).unique h₅ ht₀
    intro α j
    rw [h₆]
  exact galois_fixed_adelic_matrices_descend hL hTW V ϖ hϖ D Q hQ F v hv k hk p w₀ hw₀ 1 one_ne_zero hfin s s' s'
    (hΦθ t t' s s' hs hs' hact) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 (one_smul F _).symm) r

end GlobalTheory
