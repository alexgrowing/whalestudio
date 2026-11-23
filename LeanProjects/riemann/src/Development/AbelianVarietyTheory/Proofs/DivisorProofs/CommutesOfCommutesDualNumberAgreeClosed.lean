import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EpsRigid

theorem fst_ker_le_nilradical (k : Type) [Field k] :
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ≤ nilradical (DualNumber k) := by
  intro x hx
  have h0 : TrivSqZeroExt.fst x = 0 := hx
  have hx' : x = TrivSqZeroExt.inr (TrivSqZeroExt.snd x) := by
    ext
    · simp [h0]
    · simp
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [pow_two, hx', TrivSqZeroExt.inr_mul_inr]

theorem quot_mk_eq (k : Type) [Field k] :
    ∃ e : k →+* DualNumber k ⧸ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom,
      Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) = e.comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  refine ⟨(RingHom.quotientKerEquivOfSurjective hs).symm.toRingHom, ?_⟩
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.eq_symm_apply]
  rfl

theorem comm_of_comm :
    ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := by
  intro k _ S G' _ hG G _ g₂ φ₁ φ₂ h₂ h0 u _ v _ hu
  have hsq : (φ₂ ≫ v.left) ≫ G.hom = G'.hom ≫ g₂ := by
    rw [Category.assoc, Over.w v, h₂.1.w]
  let w : G' ⟶ G' := Over.homMk (h₂.1.lift (φ₂ ≫ v.left) G'.hom hsq) (h₂.1.lift_snd _ _ _)
  have hw : w.left ≫ φ₂ = φ₂ ≫ v.left := h₂.1.lift_fst _ _ _
  suffices huw : u = w by rw [huw, hw]
  obtain ⟨e, he⟩ := quot_mk_eq k
  have hsp : spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)) =
      spMap e ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
    rw [he, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient _ (fst_ker_le_nilradical k) G' G' hG u w ?_ ?_
  · have hj : ∀ x : pullback G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ⟶ G'.left,
        x ≫ G'.hom = pullback.fst G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ≫ G'.hom →
        x ≫ φ₁ = x ≫ φ₂ := by
      intro x hx
      refine h0 _ x (pullback.snd _ _ ≫ spMap e) ?_
      rw [hx, pullback.condition, Category.assoc, hsp]
    apply h₂.1.hom_ext
    · have a1 := hj (pullback.fst _ _ ≫ u.left) (by rw [Category.assoc, Over.w u])
      have a2 := hj (pullback.fst _ _) rfl
      simp only [Category.assoc] at a1 a2 ⊢
      rw [hw, ← a1, hu, ← Category.assoc, a2, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w u, Over.w w]
  · rw [IsMonHom.one_hom]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply h₂.1.hom_ext
    · rw [Category.assoc, hw, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂,
        Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
    · rw [Category.assoc, Over.w w]

end GlobalTheory.EpsRigid
