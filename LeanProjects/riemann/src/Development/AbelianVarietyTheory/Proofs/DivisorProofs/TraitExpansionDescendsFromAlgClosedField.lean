import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitDescent

theorem gs_one {Y Z : Scheme.{0}} (p : Z ⟶ Y) (z : Z) : gs p z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq p z ⊤ trivial, map_one, map_one]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) (a b : A) :
    scal g (a * b) = scal g a * scal g b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) : scal g 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem gs_scal_eq {A F : Type} [CommRing A] [Field F] {Y Z : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (io : A →+* F) (p : Z ⟶ Y) (q : Z ⟶ Spec (CommRingCat.of F)) (h : p ≫ g = q ≫ spMap io) (z : Z) (w : A) :
    gs p z ⊤ (scal g w) = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w)) := by
  have e1 := gs_pull p g z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e2 := gs_pull q (spMap io) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e3 : ((spMap io).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w) := by
    have := congrArg (fun f => f.hom w) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom io))
    exact this.symm
  unfold scal
  rw [← e3]
  exact e1.trans (h ▸ e2.symm)

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem expBy_scale {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u a : W) {k : ℕ}
    {σ : SecK C.P.L.L T.β k} {F₀ : IntFam (maximalIdeal R) D.toPre k} (h : T.ExpBy u σ F₀) :
    ∃ σ₂ : SecK C.P.L.L T.β k, T.ExpBy (a * u) σ₂ F₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J,
      Good C.P.L.L z J → sval σ₂ r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J := by
  obtain ⟨σ', f', hc, hp, he⟩ := h
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, Good C.P.L.L z J →
      sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom a) σ) r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J :=
    fun Z r z J hJ => sval_scale _ σ r z hJ
  refine ⟨_, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hp, he⟩, hv⟩
  rw [hv Z r z J hJ, hc Z r z J J' hJ hJ', scal_mul, gs_mul r z ⊤ trivial]
  ring

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem exp_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  intro R _ _ _ hR D C k W _ _ _ T F _ _ _ _ hF Φ c hc h1 h2
  by_cases hB : ∃ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ ∧ ∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0
  · obtain ⟨F₀, σ, hσ, hw⟩ := hB
    obtain ⟨x, hx⟩ := GlobalTheory.T.relatingConstant_mem_traitFractionField R hR D C k W T F hF σ (Φ F₀) c (h2 F₀ σ hσ) hw
    have hx0 : x ≠ 0 := by rintro rfl; exact hc (by rw [← hx, map_zero])
    obtain ⟨⟨b, ⟨a, ha⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) x
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hb0 : b ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have key : ((algebraMap (FractionRing W) F).comp (algebraMap W _)) a * c =
        ((algebraMap (FractionRing W) F).comp (algebraMap W _)) b := by
      rw [← hx, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, mul_comm]
      congr 1
      exact IsLocalization.mk'_spec (FractionRing W) b ⟨a, ha⟩
    refine ⟨b, a, hb0, ha0, fun F₁ => ?_⟩
    obtain ⟨σ₁, hσ₁⟩ := h1 F₁
    obtain ⟨σ₂, hσ₂, hv⟩ := expBy_scale T 1 a hσ₁
    rw [_root_.mul_one] at hσ₂
    refine ⟨σ₂, hσ₂, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ₂ (Φ F₁) b ?_⟩
    intro Z p p' e1 e2 z J hJ
    have e2' : p ≫ T.G.hom = (p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫
        spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by rw [e2, Category.assoc]
    have ga := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z a
    have gb := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z b
    rw [hv Z p z J hJ, h2 F₁ σ₁ hσ₁ Z p p' e1 e2 z J hJ, ga, gb, ← _root_.mul_assoc, ← gs_mul _ z ⊤ trivial, fnF, ← map_mul, key]
  · push_neg at hB
    refine ⟨1, 1, one_ne_zero, one_ne_zero, fun F₀ => ?_⟩
    obtain ⟨σ, hσ⟩ := h1 F₀
    refine ⟨σ, hσ, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ (Φ F₀) 1 ?_⟩
    intro Z p p' e1 e2 z J hJ
    have h0 := hB F₀ σ hσ Z p p' e1 e2 z J hJ
    have e := h2 F₀ σ hσ Z p p' e1 e2 z J hJ
    rw [h0] at e
    rw [h0, scal_one, gs_one, _root_.one_mul]
    have hu : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c⁻¹) *
        gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) = 1 := by
      rw [← gs_mul _ z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ hc, map_one, gs_one]
    rw [← _root_.one_mul (sval (Φ F₀) _ z J), ← hu, _root_.mul_assoc, ← e, mul_zero]

end GlobalTheory.Mum.TraitDescent
