import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericPullInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

lemma pullSectionOn_injective_of_basis_of_app (hPB : PullbackBasis.Statement.{0})
    {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules) {W : Z.Opens} {n : ℕ} {t : Fin n → Γ(M, W)}
    (ht : IsBasisOn M W t) (hg : Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M W) := by
  have hb := (hPB _ _ g M W n t ht).bijective_self
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => g.app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum g M W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hg (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]

lemma pullSectionOn_injective_of_app (hPB : PullbackBasis.Statement.{0}) {T Z : Scheme.{0}}
    (g : T ⟶ Z) (M : Z.Modules) (hM : IsVectorBundle M) (V : Z.Opens)
    (hg : ∀ W : Z.Opens, W ≤ V → Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M V) := by
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  apply modules_eq_of_locally M τ 0
  intro x hx
  obtain ⟨U, -, hxU, n, t, ht⟩ := hM x
  refine ⟨U ⊓ V, inf_le_right, ⟨hxU, hx⟩, ?_⟩
  rw [map_zero]
  apply pullSectionOn_injective_of_basis_of_app hPB g M (ht.restrict inf_le_left)
    (hg _ inf_le_right)
  rw [pullSectionOn_res g M inf_le_right (homOfLE ((Opens.map g.base).monotone inf_le_right)) τ,
    hτ, map_zero, map_zero]

theorem GenericPullInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackBasis.Statement.{0}) : GenericPullInj.Statement := by
  intro X f _ _ a ha G hG
  obtain ⟨m, hm, hinj⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn V hV => ?_⟩
  have hk0 : (a : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hn.ne')
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ hk0
  have hle : invOpen f ((a : ℤ) * n) ≤ invOpen f a := invOpen_mul_le_left f a n
  have hcomp : toInvOpen f ℚ ((a : ℤ) * n) hk ≫ X.homOfLE hle =
      toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) :=
    toInvOpen_homOfLE _ _ _ _ hle
  apply pullSectionOn_injective_of_app h₂ _ G hG V
  intro W hW
  have hWr : W ≤ (X.homOfLE hle).opensRange := by
    rw [Scheme.opensRange_homOfLE]
    exact hW.trans hV
  have hiso : IsIso ((X.homOfLE hle).app W) := Scheme.Hom.isIso_app _ W hWr
  have hj : Function.Injective ((X.homOfLE hle).app W) :=
    (ConcreteCategory.bijective_of_isIso ((X.homOfLE hle).app W)).1
  have hq : Function.Injective ((toInvOpen f ℚ ((a : ℤ) * n) hk).app ((X.homOfLE hle) ⁻¹ᵁ W)) :=
    hinj _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _) _
  rw [← hcomp, Scheme.Hom.comp_app]
  intro x y hxy
  exact hj (hq hxy)

end

end GroundTheory.Heights₂.Heights.Model
