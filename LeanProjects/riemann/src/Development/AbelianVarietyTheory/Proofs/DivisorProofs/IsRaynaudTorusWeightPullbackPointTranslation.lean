import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTransWt

theorem valR_pbT_le {A : Type} [CommRing A] {X Z : Scheme.{0}} (w : Sp A ⟶ Z) (T : Z ⟶ X) {U : X.Opens}
    {U' : Z.Opens} (hU : U' ≤ T ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ U') (f : Γ(X, U)) :
    valR w U' (pbT T f U') = valR (w ≫ T) U f := by
  have h' : ⊤ ≤ (w ≫ T) ⁻¹ᵁ U := h.trans (w.preimage_mono hU)
  unfold valR
  rw [dif_pos h, dif_pos h', GlobalTheory.KS.pbT_of_le T hU]
  rw [← Scheme.Hom.appLE_comp_appLE w T U U' ⊤ hU h]
  rfl

theorem isWt_pbT_tr : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  intro R _ _ Q O _ _ _ oa Y x α U U' hU f hf S _ φ x₁ x₁' c a a' ha ha' hV hV' hq hc
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let z : Over.mk (spMap φ) ⟶ Y.H := toUnit _ ≫ x
  have hleft : ∀ w : Over.mk (spMap φ) ⟶ Y.H, (w * z).left = w.left ≫ GlobalTheory.HeatTrans.tr Y.H x := fun w => by
    have e : w ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)) = w * z := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (w ≫ toUnit Y.H) (toUnit _)]
    rw [← e]; rfl
  rw [valR_pbT_le a' _ hU hV', valR_pbT_le a _ hU hV]
  subst ha ha'
  rw [← hleft, ← hleft]
  refine hf S φ (x₁ * z) (x₁' * z) c _ _ rfl rfl ?_ ?_ ?_ ?_
  · rw [hleft]; exact hV.trans (x₁.left.preimage_mono hU)
  · rw [hleft]; exact hV'.trans (x₁'.left.preimage_mono hU)
  · rw [MonObj.mul_comp, MonObj.mul_comp, hq]
  · intro χ y J hJ
    have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ z)).2 χ y J hJ
    have h1' := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' z)).2 χ y J hJ
    simp only [Y.Φ_b, GlobalTheory.TorusModel.cv] at h1 h1'
    rw [hq] at h1'
    refine mul_right_cancel (h1'.trans ?_)
    rw [hc χ y J hJ, _root_.mul_assoc, ← h1, _root_.mul_assoc]

end GlobalTheory.HeatTransWt
