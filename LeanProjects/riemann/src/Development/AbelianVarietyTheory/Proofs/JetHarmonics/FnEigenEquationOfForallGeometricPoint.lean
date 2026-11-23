import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenSpread

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {l : ℕ}
    (a : Fin l → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem exists_defect_sum {O : Type} [CommRing O] {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H)
    (π : H ⟶ Spec (CommRingCat.of O)) (V : G.Opens) {l : ℕ} (c : Fin l → O) (t : Fin l → Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ m) z V (t i) -
          gs (g ≫ p) z ⊤ u * ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ s) z V (t i) := by
  choose f hf using fun i => EigenAll.exists_defect m s p V (t i) u
  refine ⟨∑ i, resTop _ (scal (p ≫ π) (c i)) * f i, fun Z g z hz => ?_⟩
  rw [gs_sum g z _ hz, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul g z _ hz, FieldBaseChange.gs_const _ g z _ hz, hf i Z g z hz, Category.assoc]
  ring

end GlobalTheory.EigenSpread

namespace GlobalTheory

theorem fn_eigen_equation_of_forall_geometric_point :
    ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  intro V O F _ _ _ _ _ hinj β G _ hG Z hfin hflat hred jZ hj U l c s k hyp
  let Y : Over (Spec (CommRingCat.of O)) :=
    Over.mk (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β)))
  have hY : Flat Y.hom := inferInstanceAs (Flat (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β))))
  let p : (Z ⊗ Y).left ⟶ Z.left := pullback.fst Z.hom Y.hom
  let PV : Over (Spec (CommRingCat.of V)) := Over.mk (p ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β))
  let r₀ : PV ⟶ G := Over.homMk (pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β))) (by
    change _ = pullback.fst Z.hom Y.hom ≫ Z.hom ≫ _
    rw [Category.assoc, pullback.condition, pullback.condition_assoc]
    rfl)
  let g₀ : PV ⟶ G := Over.homMk (p ≫ jZ) (by
    change _ = p ≫ Z.hom ≫ _
    rw [Category.assoc, hj])
  obtain ⟨f, hf⟩ := EigenSpread.exists_defect_sum (Y := (Z ⊗ Y).left) (r₀ * g₀).left r₀.left p Z.hom U c s k
  have h0 : f = 0 := by
    refine section_eq_zero_of_forall_geometric_point O F hinj Z Y hfin hflat hred hY _ f fun c₀ => ?_
    refine fn_ext fun x hx => ?_
    rw [EigenAll.gs_zero, gs_pull (𝟙 _) (c₀ ▷ Y).left x _ hx, Category.id_comp, hf _ _ x hx, sub_eq_zero]
    let ρ : Over.mk ((c₀ ▷ Y).left ≫ PV.hom) ⟶ PV := Over.homMk (c₀ ▷ Y).left rfl
    let e : (Pdiv.specO O F ⊗ Y).left ⟶ Spec (CommRingCat.of F) := pullback.fst (Pdiv.specO O F).hom Y.hom
    have e₁ : (c₀ ▷ Y).left ≫ p = e ≫ c₀.left := Over.whiskerRight_left_fst c₀
    have e₂ : (e ≫ c₀.left) ≫ Z.hom = e ≫ Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
      rw [Category.assoc, Over.w c₀]
      rfl
    have e₃ : (ρ ≫ r₀ * ρ ≫ g₀).left = (c₀ ▷ Y).left ≫ (r₀ * g₀).left := by
      rw [← MonObj.comp_mul]
      rfl
    have := hyp _ e c₀ (ρ ≫ r₀) (ρ ≫ g₀) (by rw [← e₁, Category.assoc]; rfl) x hx.2 (by rw [e₃]; exact hx.1)
    rw [e₃] at this
    rw [e₁, e₂]
    simp only [FieldBaseChange.constVal_specMap]
    exact this
  intro T q r g hg z hr hrg
  have hT : T.hom = q ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β) := by
    rw [← Over.w g, hg, Category.assoc, hj]
  let a : T.left ⟶ (Z ⊗ Y).left := pullback.lift q
    (pullback.lift r.left (q ≫ Z.hom) (by rw [Over.w r, hT, Category.assoc]))
    (pullback.lift_snd _ _ _).symm
  have e₁ : a ≫ p = q := pullback.lift_fst _ _ _
  let ρ : T ⟶ PV := Over.homMk a (by
    change a ≫ p ≫ _ = _
    rw [← Category.assoc, e₁, hT])
  have e₂ : a ≫ r₀.left = r.left := by
    change a ≫ pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β)) = _
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have e₃ : ρ ≫ r₀ = r := Over.OverMorphism.ext e₂
  have e₄ : ρ ≫ g₀ = g := Over.OverMorphism.ext (by
    change a ≫ p ≫ jZ = _
    rw [← Category.assoc, e₁, hg])
  have e₅ : a ≫ (r₀ * g₀).left = (r * g).left := by
    rw [← e₃, ← e₄, ← MonObj.comp_mul]
    rfl
  rw [← e₅] at hrg
  rw [← e₂] at hr
  have := hf _ a z ⟨hrg, hr⟩
  rw [h0, EigenAll.gs_zero, e₁, e₂, e₅] at this
  exact sub_eq_zero.1 this.symm

end GlobalTheory
