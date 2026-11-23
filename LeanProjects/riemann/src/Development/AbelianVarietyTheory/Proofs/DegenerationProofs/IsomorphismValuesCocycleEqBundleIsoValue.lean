import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoValuesConstantOfSameCubeTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.IsoValCocycle
open GlobalTheory.TorusExt GlobalTheory.IsoValConst

theorem exists_th_ne_zero (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type}
    [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) {n : ℕ} (hn : 2 ≤ n)
    (hF : (n : F) ≠ 0) (a : N.A) : ∃ t, t ^ n = 1 ∧ N.th (a * t) ≠ 0 := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  obtain ⟨th, ρ, hth, hv⟩ := ThetaInValues.exists_th ν y
  obtain ⟨x, hx, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P (jFK (R := R) F ≫ jK R) hn hF th
    (ThetaCoset.ne_zero_of_isGenSec hL₂.secBaseChangeAny D.P _ hth) (ν.eA a)
  obtain ⟨t, rfl⟩ := ν.eA.surjective x
  refine ⟨t, ν.eA.injective (by rw [map_pow, map_one]; exact hx), fun h => ?_⟩
  have q := hu y ν.J (ThetaInValues.good ν y)
  have e := hv (a * t)
  rw [h, MulZeroClass.zero_mul, map_zero, map_mul] at e
  exact not_isUnit_zero ((congrArg IsUnit e).mp q)

theorem cocycle_eq_val : Laws → Laws2 → ∀ (R O' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (f : O' →+* R) (P : DegPre R) (D₀ : DegPre O') (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (N' N : NumD C) (ν' : NumOf P C N') (ν : NumOf D₀ C N) (ψ : P.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (I : NumB.Iso N.toNumB N'.toNumB), IsGrpPullback P.P.A D₀.P.A (spMap f) ψ → w.IsGen → (∀ x : N.A, (ν'.eA (I.φ x)).left ≫ ψ = (ν.eA x).left) → (∀ x, wVal ν' ν w x ≠ 0) ∧ ∀ x : N.A, (I.h x : C) * wVal ν' ν w (I.φ x) = wVal ν' ν w 1 := by
  intro hL hL₂ R O' _ _ _ _ _ _ f P D₀ C _ _ _ _ _ hf N' N ν' ν ψ w I gp hw he
  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := good ν z
  have hJ' := good ν' z
  have hT : (TF (R := R) C).hom ≫ spMap f = (TF (R := O') C).hom := ArcTransport.base_comm fun r => (hf r).symm
  have hp : ∀ x : N.A, ArcTransport.pushF gp hT (ν'.eA (I.φ x)) = ν.eA x := fun x => Over.OverMorphism.ext (he x)
  have hW : ∀ x : N'.A, stalkConst z (wVal ν' ν w x) = (ArcTransport.wVal w z ν.J ν'.J (ν'.eA x)).val := fun x =>
    toStk_valF (ν'.eA x).left ((D₀.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA x).left ≫ ψ)) ⊓ P.P.L.U (ν'.J (ν'.eA x).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA x).left ≫ ψ)), hJ' _⟩ _
  refine ⟨fun x h => ?_, ?_⟩
  · have := hW x
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  let Ω : N.A → ((Sp C).presheaf.stalk z)ˣ := fun x => ArcTransport.wVal w z ν.J ν'.J (ν'.eA (I.φ x))
  have hΩ : ∀ x, stalkUnits z (I.h x) * Ω x = stalkUnits z (I.h 1) * Ω 1 := by
    refine const_of_cube (fun x => stalkUnits z (I.h x) * Ω x) (fun a b c => ?_) (fun a => N.th a ≠ 0) ?_ 2
      (fun x => ?_) (exists_th_ne_zero hL hL₂ ν le_rfl (Nat.cast_ne_zero.2 two_ne_zero))
    · have e := ArcTransport.thS_push gp hT ((isGen_iff _).1 hw) hL.globalFns hJ hJ' (ν'.eA (I.φ a)) (ν'.eA (I.φ b))
        (ν'.eA (I.φ c))
      rw [hp, hp, hp, ← map_one ν'.eA, ← map_one I.φ, ← stalk_θ, ← stalk_θ] at e
      simp only [← map_mul ν'.eA, ← map_mul I.φ] at e
      have e₁ : stalkUnits z (N.θ a b c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
        Ω c * (Ω 1)⁻¹ * stalkUnits z (N'.θ (I.φ a) (I.φ b) (I.φ c)) := e
      have e₂ := congrArg (stalkUnits z) (I.θ_eq a b c)
      rw [I.h_one, map_one]
      clear_value Ω
      apply Additive.ofMul.injective
      replace e₁ := congrArg Additive.ofMul e₁
      replace e₂ := congrArg Additive.ofMul e₂
      simp only [map_mul, ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ ⊢
      linear_combination (norm := abel) -e₁ - e₂
    · obtain ⟨s, hs⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => 𝟙 P.P.A.left)
        (φ := fun _ : Fin 1 => 𝟙 D₀.P.A.left) (h := ψ) hw D₀.P.isLB P.P.isLB
        (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) ν.th
      obtain ⟨κ, hκ⟩ := sval_eq ν' z s
      obtain ⟨ρ, hρ⟩ := stalk_th ν z
      obtain ⟨ρ', hρ'⟩ := stalk_th ν' z
      have key : ∀ a : N.A, N.th a ≠ 0 →
          ρ.val = (stalkUnits z (I.h a) * Ω a).val * (κ * stalkConst z I.lam * ρ'.val) := fun a ha => by
        have e := hs.sval (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
          (show Sp C ⟶ _ from (ν'.eA (I.φ a)).left) hJ hJ'
        rw [Fin.prod_univ_one, Category.comp_id] at e
        replace e := e.trans (congrArg (fun q : ((Sp C).presheaf.stalk z)ˣ => q.val * _) (zpow_one _))
        have e' : stalkConst z (N.th a) * ρ.val = (Ω a).val * (κ * (stalkConst z (N'.th (I.φ a)) * ρ'.val)) :=
          (hρ a).trans ((congrArg (fun q => sval (Z := Sp C) ν.th q z ν.J) (he a).symm).trans (e.trans
            (congrArg _ ((hκ _).trans (congrArg _ (hρ' _).symm)))))
        refine ((IsUnit.mk0 _ ha).map (stalkConst z)).mul_left_cancel (e'.trans ?_)
        rw [I.th_eq, Units.val_mul, Units.val_mul, stalkUnits_val, map_mul, map_mul]
        ring
      intro a b ha hb
      have hu : IsUnit (κ * stalkConst z I.lam * ρ'.val) := isUnit_of_mul_isUnit_right (key a ha ▸ ρ.isUnit)
      exact Units.ext (hu.mul_right_cancel ((key a ha).symm.trans (key b hb)))
    · obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D₀.P (jFK (R := O') C ≫ jK O') (ν.eA x) one_le_two
      exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  intro x
  apply (stalkConst z).injective
  have e := congrArg Units.val (hΩ x)
  rw [I.h_one, map_one, _root_.one_mul, Units.val_mul, stalkUnits_val] at e
  rw [map_mul, hW, hW, ← map_one I.φ]
  exact e

end GlobalTheory.IsoValCocycle
end
