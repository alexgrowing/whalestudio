import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.CrdDown

theorem val_of_rel {K : Type} [CommRing K] {X Y : Scheme.{0}} (x : Sp K ⟶ X) (ρ : X ⟶ Y) (p : Sp K ⟶ Y)
    (hp : x ≫ ρ = p) (U : X.Opens) (V : Y.Opens) (W : (Sp K).Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : U ≤ ρ ⁻¹ᵁ V)
    (hW : ⊤ ≤ W) (hWV : W ≤ p ⁻¹ᵁ V) (u : Γ(Sp K, W)ˣ) :
    ∃ c : Kˣ, ∀ (f : Γ(Y, V)) (w : Γ(Sp K, ⊤)),
      ((Sp K).presheaf.map (homOfLE hWV).op).hom ((p.app V).hom f) =
        ((Sp K).presheaf.map (homOfLE le_top).op).hom w * u.val →
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom w = (c : K) * valR x U ((ρ.appLE V U hV).hom f) := by
  subst hp
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  refine ⟨(Units.map φ.toMonoidHom u)⁻¹, fun f w h => ?_⟩
  have e : ((Sp K).presheaf.map (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ ⊤)).op).hom w = w :=
    congrArg (fun φ => CommRingCat.Hom.hom φ w) ((Sp K).presheaf.map_id _)
  rw [e] at h
  have h1 : (x.appLE U ⊤ hU).hom ((ρ.appLE V U hV).hom f) = w * u.val :=
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.appLE_comp_appLE x ρ V U ⊤ hV hU)).trans h
  rw [CrdCalc.valR_eq x U hU, Units.eq_inv_mul_iff_mul_eq]
  refine Eq.trans ?_ (congrArg φ h1).symm
  rw [map_mul, _root_.mul_comm]
  rfl

theorem crd_down_of_isValueAt : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  intro K _ _ P N J t ρ e x τ w h
  have hx : (x.left : Sp K ⟶ P.A.left) (IsLocalRing.closedPoint K) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hi' := (CrdCalc.top_le_iff (x.left : Sp K ⟶ P.A.left) _).2 hi
  haveI : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  have hp : (x.left : Sp K ⟶ P.A.left) ≫ ρ = (Out.ptSecT P.A x).left := by
    rw [← cancel_mono (snd (Out.baseOver (Sp K)) P.A).left]
    refine (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) e).trans ((Category.comp_id _).trans ?_))
    exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Out.baseOver (Sp K))) x)).symm
  have hU : ⊤ ≤ (x.left : Sp K ⟶ P.A.left) ⁻¹ᵁ LB.wchart P.L (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  have hW : ⊤ ≤ LB.wchart P.L (fun _ : Fin 1 => x.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  obtain ⟨c, hc⟩ := val_of_rel (x.left : Sp K ⟶ P.A.left) ρ _ hp _ _ _ hU
    (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (fun _ => i)).le hW
    (Out.val_le P.A P.L x (fun _ => i)) (τ.s (fun _ => i))
  exact ⟨fun _ => i, c, hU, fun a => hc _ _ (h a (fun _ => i))⟩

end GlobalTheory.ZH.CrdDown
end
