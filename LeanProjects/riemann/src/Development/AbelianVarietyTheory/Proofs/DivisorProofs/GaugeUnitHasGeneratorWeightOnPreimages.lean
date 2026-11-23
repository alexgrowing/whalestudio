import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
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

namespace GlobalTheory.Heat.Gauge

theorem isWt_zero_pbT_factor {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {Z : Scheme.{0}} (m₁ : Y.H.left ⟶ Z) (τ : Q.P.A.left ⟶ Z)
    (hm : m₁ = Y.q.left ≫ τ) {U : Z.Opens} (s : Γ(Z, U)) {V : Y.H.left.Opens} (hV : V ≤ m₁ ⁻¹ᵁ U) :
    IsWt Y 0 V (pbT m₁ s V) := by
  intro S _ φ z z' c a a' ha ha' h1 h2 hq hc
  have e : a' ≫ m₁ = a ≫ m₁ := by
    subst ha ha' hm
    have := congrArg CommaMorphism.left hq
    simp only [Over.comp_left] at this
    rw [← Category.assoc, this, Category.assoc]
  rw [GlobalTheory.HeatGlue.valR_pbT a' m₁ hV h2, GlobalTheory.HeatGlue.valR_pbT a m₁ hV h1, e, GlobalTheory.Heat.WtAlg.c_zero z z' c hc,
    Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.Gauge

open GlobalTheory.Heat.Gauge in

theorem GlobalTheory.Heat.Gauge.gU_isWt : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D) (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∀ (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ GlobalTheory.Heat.Gauge.W Y.q.left h₁ p → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (GlobalTheory.Heat.Gauge.gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D x h₁ e β hwe p V hV
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  have hW := W_le_wchart Y.q.left h₁ p
  have hm := W_le_m₁ Y.q.left h₁ p
  have key : rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V) =
      pbT ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) (Q.P.L.g (p.2 1) (h₁.j p.1)).val (Y.q.left ⁻¹ᵁ V) *
        rsT (e.s p.2).val (Y.q.left ⁻¹ᵁ V) := by
    rw [gU, Units.val_mul, GlobalTheory.KS.AdjDlog.val_res_pullU]
    erw [GlobalTheory.KS.AdjDlog.val_res hW]
    rw [GlobalTheory.KS.rsT_mul,
      GlobalTheory.KS.rsT_rsT hW hV, GlobalTheory.KS.rsT_pbT _ hm hV]
    exact mul_comm _ _
  rw [key]
  exact GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
    (isWt_zero_pbT_factor Y _ τ hτ _ (hV.trans hm))
    (hwe p.2 V (hV.trans hW))
