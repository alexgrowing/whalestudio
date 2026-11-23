import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSumTmulLinearIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isUnit_scal_comp_specMap {R F : Type} [CommRing R] [CommRing F] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (r : R) (h : IsUnit (φ r)) :
    IsUnit (scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r) := by
  have e : scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
    have := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    unfold scal
    rw [this]
    rfl
  rw [e]
  exact (h.map _).map _

theorem sval_eq_zero_of_forall_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_lift_pair {S : Scheme.{0}} (T₀ B : Over S) {T : Scheme.{0}} (r₁ r₂ : T ⟶ (T₀ ⊗ B).left)
    (h : r₁ ≫ (fst T₀ B).left = r₂ ≫ (fst T₀ B).left) :
    ∃ (q : T ⟶ S) (ρ : Over.mk q ⟶ T₀) (x y : Over.mk q ⟶ B), (lift ρ x).left = r₁ ∧ (lift ρ y).left = r₂ := by
  have w : r₂ ≫ (T₀ ⊗ B).hom = r₁ ≫ (T₀ ⊗ B).hom := by
    rw [← Over.w (fst T₀ B), ← Category.assoc, ← Category.assoc, h]
  let u₁ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₁ rfl
  let u₂ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₂ w
  have e : u₁ ≫ fst T₀ B = u₂ ≫ fst T₀ B := Over.OverMorphism.ext h
  refine ⟨_, u₁ ≫ fst T₀ B, u₁ ≫ snd T₀ B, u₂ ≫ snd T₀ B, ?_, ?_⟩
  · rw [lift_comp_fst_snd]; rfl
  · rw [e, lift_comp_fst_snd]; rfl

theorem addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA
  have := D.P.isAb.proper
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsProper (fst (TF (R := R) F) D.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (TF (R := R) F ⊗ D.P.A).left := isIntegral_tensor_left_of_smooth_grpObj _ _ _
  have key := fun α β : D.X => GlobalTheory.tensor_sections_eq_zero_iff F _ D.P.L D.P.isLB _ _ (fst (TF (R := R) F) D.P.A).left
    (fst (TF (R := R) F) D.P.A).left _ _ (DegPre.famφ D F α) (DegPre.famε 2) (DegPre.famφ D F β) (DegPre.famε 2) n
    (fun i => SecMod.mk _ (s i α)) (fun i => SecMod.mk _ (s' i β))
  refine ⟨fun a b => ⟨fun hne => ?_, fun ⟨ha, hb⟩ h0 => ?_⟩, fun α β hαβ => ?_⟩
  · by_contra hc
    refine hne ((key _ _).2 fun T r₁ r₂ h z J hJ => ?_)
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    refine ((hA (Over.mk q) ρ x y z J hJ).1 a b _ _ rfl rfl).trans ?_
    rcases not_and_or.1 hc with hc | hc
    · have := sval_eq_zero_of_forall_eq_zero (s₀ a) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y)).left z J
      exact (congrArg (_ * ·) ((congrArg (· * _) this).trans (zero_mul _))).trans (mul_zero _)
    · have := sval_eq_zero_of_forall_eq_zero (s₀ b) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y⁻¹)).left z J
      exact (congrArg (_ * ·) ((congrArg (_ * ·) this).trans (mul_zero _))).trans (mul_zero _)
  · let z := genericPoint (TF (R := R) F ⊗ D.P.A).left
    choose J hJ using fun χ : (TF (R := R) F ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have hG : Good D.P.L z J := hJ
    have h1 := (key _ _).1 h0 _ (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left
      (lift (fst (TF (R := R) F) D.P.A) (1 : _ ⟶ D.P.A)).left
      (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z J hG
    have h2 := ((hA (TF (R := R) F ⊗ D.P.A) (fst _ _) (snd _ _) 1 z J hG).1 a b _ _ rfl rfl).symm.trans h1
    rw [inv_one, _root_.mul_one, lift_fst_snd] at h2
    have hu : IsUnit (scal (TF (R := R) F ⊗ D.P.A).hom r) := by
      have e : (TF (R := R) F ⊗ D.P.A).hom = (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
        rw [← Over.w (fst (TF (R := R) F) D.P.A), CommRingCat.ofHom_comp, Spec.map_comp]; rfl
      rw [e]
      refine isUnit_scal_comp_specMap _ _ r (IsUnit.mk0 _ ?_)
      exact (map_ne_zero (algebraMap (FractionRing R) F)).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have hu' : IsUnit (gs (𝟙 _) z ⊤ (scal (TF (R := R) F ⊗ D.P.A).hom r)) := by
      rw [gs_eq _ z ⊤ trivial]
      exact (hu.map _).map _
    exact mul_ne_zero (mul_ne_zero hu'.ne_zero (Units.ne_zero _))
      (mul_ne_zero ((exists_ne_zero_iff_sval_ne_zero (s₀ a) hG).1 ha)
        ((exists_ne_zero_iff_sval_ne_zero (s₀ b) hG).1 hb)) h2
  · refine (key _ _).2 fun T r₁ r₂ h z J hJ => ?_
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    exact (hA (Over.mk q) ρ x y z J hJ).2 α β hαβ

end GlobalTheory
