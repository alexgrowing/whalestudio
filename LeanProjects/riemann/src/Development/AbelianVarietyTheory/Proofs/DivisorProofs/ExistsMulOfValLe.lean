import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {V : Type} [CommRing V] [IsDomain V]

theorem torsion_points (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) :
    ∃ x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
      (∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
        (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧
      ∀ z : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :) (by simp)) ρ.pt (S.r * S.N)
    ρ.pt_add (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

theorem frames (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) (lb : LBIso A.L (ρ.P.L.pull φ))
    (x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A))
    (hx : ∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
      (ρ.pt a).left) :
    ∃ (rig : LB.Gen (A.L.pull (eSec A.A)))
      (e : ∀ a, LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) (AlgebraicClosure (FractionRing V))).left) (K := Fin 1)
        (fun _ => (x a).left) (fun _ => 1))),
      rig.IsGen ∧ (∀ a, IsTorsFrame A rig (S.r * S.N) (x a) (e a)) ∧
      ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))),
        ∃ t : SecA A (AlgebraicClosure (FractionRing V)) k, ∀ (a : S.Gam) (c : S.R),
          IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) →
          ∀ z J, Good A.L z J → sA t (ptSecT A.A (x a)).left z J =
            @id ((TFK (R := V) (AlgebraicClosure (FractionRing V))).left.presheaf.stalk z)
              (cst (R := V) (AlgebraicClosure (FractionRing V)) z
                ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK c)) *
            (val (powFrame A.A A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  have hh : (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _)))
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := GlobalTheory.FrameMove.exists_move (T := baseOver (Sp S.R))
    (T' := TFK (R := V) (AlgebraicClosure (FractionRing V))) cart lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (GlobalTheory.FrameMove.gs_spMap _ z c))⟩

end GlobalTheory.ThetaDvr
end

namespace GlobalTheory.ThetaDvr

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_mul_of_val_le {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {x y : FractionRing V} (hy : y ≠ 0)
    (h : v (algebraMap (FractionRing V) F y) ≤ v (algebraMap (FractionRing V) F x)) :
    ∃ w : V, x = algebraMap V (FractionRing V) w * y ∧
      (v (algebraMap (FractionRing V) F y) < v (algebraMap (FractionRing V) F x) → w ∈ IsLocalRing.maximalIdeal V) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero, zero_mul], fun _ => zero_mem _⟩
  obtain ⟨n, u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ x hx
  obtain ⟨m, u', hu'⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ y hy
  have hn := hv x n ⟨u, hu⟩
  have hm := hv y m ⟨u', hu'⟩
  rw [hn, hm, WithTop.coe_le_coe, Int.cast_le] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hu'1 : algebraMap V (FractionRing V) (↑u'⁻¹ : V) * algebraMap V (FractionRing V) (u' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨ϖ ^ k * u * ↑u'⁻¹, ?_, fun hlt => ?_⟩
  · rw [hu, hu', hk, zpow_add₀ hϖ0, zpow_natCast, map_mul, map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ k *
      algebraMap V (FractionRing V) (u : V))) * hu'1
  · rw [hn, hm, WithTop.coe_lt_coe, Int.cast_lt] at hlt
    have hk0 : k ≠ 0 := by omega
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ k (Nat.pos_of_ne_zero hk0)))
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.ThetaDvr
