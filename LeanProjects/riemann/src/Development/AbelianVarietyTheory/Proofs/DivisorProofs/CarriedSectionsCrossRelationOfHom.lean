import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.Two

theorem whisker_comm₂ {C : Type*} [Category C] [CartesianMonoidalCategory C] (T : C) {X₁ X₂ Y₁ Y₂ : C}
    (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (h : a ≫ g₂ = g₁ ≫ b) :
    T ◁ a ≫ lift (fst _ _) (snd _ _ ≫ g₂) = lift (fst _ _) (snd _ _ ≫ g₁) ≫ T ◁ b := by
  ext <;> simp [h]

theorem crossH_at {R : Type} [CommRing R] [IsDomain R] {A₁ A₂ : PolAV (Sp (FractionRing R))} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {c : A₁.A ⟶ A₂.A} {j j' : ℕ} {t₁ t₂ : SecA A₂ F j} {t₁' t₂' : SecA A₁ F j'}
    (h : CrossH c t₁ t₂ t₁' t₂') {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A₁.A).left) (z : Z) {J₁ J₂}
    (hJ₁ : Good A₁.L z J₁) (hJ₂ : Good A₂.L z J₂) :
    sA t₁ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₂' r z J₁ =
      sA t₂ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₁' r z J₁ := by
  have e : ∀ t : SecA A₁ F j', sA t r z J₁ = (r.stalkMap z).hom (sA t (𝟙 _) (r z) (fun ψ => J₁ (r ≫ ψ))) :=
    fun t => by
      have := GlobalTheory.UU.IntExp.sval_comp (L := A₁.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₁.A).left)
        (ε := fun _ => ((j' : ℕ) : ℤ)) t (𝟙 _) r z J₁ hJ₁
      rw [Category.comp_id] at this
      exact this
  have e' : ∀ t : SecA A₂ F j, sA t (r ≫ (TFK (R := R) F ◁ c).left) z J₂ =
      (r.stalkMap z).hom (sA t (TFK (R := R) F ◁ c).left (r z) (fun ψ => J₂ (r ≫ ψ))) :=
    fun t => GlobalTheory.UU.IntExp.sval_comp (L := A₂.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₂.A).left)
        (ε := fun _ => ((j : ℕ) : ℤ)) t _ r z J₂ hJ₂
  rw [e, e, e', e', ← map_mul, ← map_mul, h (r z) _ _ (fun ψ => hJ₁ (r ≫ ψ)) (fun ψ => hJ₂ (r ≫ ψ))]

theorem carried_cross_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a c hc F _ _ w₁ w₂ _ _ j j' t₁ t₂ t₁' t₂' σ₁ σ₂ σ₁' σ₂'
    h₁ h₂ h₁' h₂' h y J₁ J₂ hJ₁ hJ₂
  have hm : (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left ≫ (U₂.genF F).left =
      (U₁.genF F).left ≫ (TFK (R := R) F ◁ c).left :=
    congrArg (fun q => q.left) (whisker_comm₂ (TFK (R := R) F) U₁.gen.hom U₂.gen.hom _ _ hc)
  obtain ⟨J'₁, hJ'₁⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₁.isLB y
  obtain ⟨J'₂, hJ'₂⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₂.isLB y
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val h₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₂ := GlobalTheory.BoxExpansion.isoRel_val h₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₃ := GlobalTheory.BoxExpansion.isoRel_val h₁' (𝟙 _) y hJ'₁ hJ₁
  have a₄ := GlobalTheory.BoxExpansion.isoRel_val h₂' (𝟙 _) y hJ'₁ hJ₁
  have a₅ := crossH_at h (U₁.genF F).left y hJ'₁ hJ'₂
  rw [Category.comp_id, hm] at a₁ a₂
  rw [Category.comp_id, Category.id_comp (U₁.genF F).left] at a₃ a₄
  rw [a₁, a₂, a₃, a₄]
  exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg (_ * ·) a₅).trans (_root_.mul_mul_mul_comm _ _ _ _))

end GlobalTheory.Mum.Two
