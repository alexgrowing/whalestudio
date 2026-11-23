import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn.LogDerDesc

theorem exists_app_mul_eq_dE : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (α : Q.X) (U : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ U ≤ h.W i → ∀ x : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U), IsUnit x → IsWt Y α _ x → ∃ A : Γ(Q.P.A.left, U), (Y.q.left.app U).hom A * x = dE h ν i _ x := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hdd hB i α U hU x hx hxw

  have h1 : IsWt Y α _ (dE h ν i _ x) := by
    unfold dE
    refine WtAlg.isWt_add ((hB i).2.2.2 α U hU x hxw) (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) ?_)
    exact WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hdd a α _ x hxw)

  have h2 : IsWt Y 0 _ (dE h ν i _ x * ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) := by
    intro S _ φ y y' c a a' ha ha' hV hV' hq hc
    have one : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U)),
        valR b _ x * valR b _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)) = 1 := by
      intro b hb
      rw [← WtAlg.valR_mul'' _ _ hb, IsUnit.mul_val_inv, WtAlg.valR_eq' _ _ hb, map_one, map_one]
    have e1 := h1 S φ y y' c a a' ha ha' hV hV' hq hc
    have ex := hxw S φ y y' c a a' ha ha' hV hV' hq hc
    have o := one a hV
    have o' := one a' hV'
    rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, e1, WtAlg.c_zero y y' c hc, Units.val_one, _root_.one_mul]
    rw [ex] at o'
    linear_combination (-((c α : S)) * valR a _ (dE h ν i _ x) * valR a' _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o
      + (valR a _ (dE h ν i _ x) * valR a _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o'

  obtain ⟨A, hA⟩ := AbConst.exists_app_eq Y h2
  refine ⟨A, ?_⟩
  rw [hA, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]

end GlobalTheory.HeatConn.LogDerDesc
