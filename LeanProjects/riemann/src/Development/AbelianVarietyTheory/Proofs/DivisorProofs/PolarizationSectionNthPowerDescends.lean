import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} (P : PolAV S)

def toProd : P.A.left ⟶ (baseOver S ⊗ P.A).left := (λ_ P.A).inv.left

theorem toProd_snd : toProd P ≫ (snd (baseOver S) P.A).left = 𝟙 _ := by
  have h := congrArg (fun f => f.left) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Over.id_left, leftUnitor_hom] at h
  exact h

variable {P}
theorem chart_le {n : ℕ} (j : PUnit → P.L.ι) :
    (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ()) := by
  intro y hy
  have hy' : y ∈ P.L.U (j ()) := Set.mem_iInter.1 hy ()
  refine Set.mem_iInter.2 fun _ => ?_
  show (toProd P ≫ (snd (baseOver S) P.A).left).base y ∈ P.L.U (j ())
  rw [toProd_snd]; exact hy'
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
theorem coe_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    ((res h (pullU f U x) : Γ(Y, W)ˣ) : Γ(Y, W)) = (f.appLE U W h).hom x := by
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem appLE_res_pullU_pow {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h1 : V ≤ g ⁻¹ᵁ U) (h2 : W ≤ f ⁻¹ᵁ V) (h3 : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) (n : ℕ) :
    (f.appLE V W h2).hom ((res h1 (pullU g U x)).val ^ n) =
      (res h3 (pullU (f ≫ g) U x)).val ^ n := by
  rw [map_pow, coe_res_pullU, coe_res_pullU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem res_pullU_of_eq {X Y : Scheme.{0}} {f g : Y ⟶ X} (hfg : f = g) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : res h (pullU f U x) = res (hfg ▸ h) (pullU g U x) := by
  subst hfg; rfl

variable {S : Scheme.{0}} {P : PolAV S}
theorem g_eq {n : ℕ} (i j : PUnit → P.L.ι)
    (e : (lbPow P.L n).U i ⊓ (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ ((LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => i ()) ⊓
      (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ()))) :
    ((toProd P).appLE _ _ e).hom ((LPow P.A P.L (n : ℤ) (baseOver S)).g (fun _ => i ()) (fun _ => j ())).val =
      ((lbPow P.L n).g i j).val := by
  simp only [LPow, LB.LinComb, Units.coe_prod, Fin.prod_univ_one, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [lbPow, LB.LinComb, Units.coe_prod, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  refine (appLE_res_pullU_pow (toProd P) (snd (baseOver S) P.A).left (P.L.U (i ()) ⊓ P.L.U (j ()))
    ((P.L.wchart (fun _ : Fin 1 => (snd (baseOver S) P.A).left) fun _ => i ()) ⊓
      P.L.wchart (fun _ : Fin 1 => (snd (baseOver S) P.A).left) fun _ => j ())
    (P.L.wchart (fun _ : PUnit => 𝟙 P.A.left) i ⊓ P.L.wchart (fun _ : PUnit => 𝟙 P.A.left) j) _ e ?_ (P.L.g (i ()) (j ())) n).trans ?_
  · rw [toProd_snd]
    intro z hz
    exact ⟨Set.mem_iInter.1 hz.1 (), Set.mem_iInter.1 hz.2 ()⟩
  · rw [res_pullU_of_eq (toProd_snd P)]
    rfl
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} {P : PolAV S}

def descSec (n : ℕ) (t : LB.Sec (LPow P.A P.L (n : ℤ) (baseOver S))) : (lbPow P.L n).Sec where
  f j := ((toProd P).appLE _ _ (chart_le j)).hom (t.f (fun _ => j ()))
  compat i j := by
    have e : (lbPow P.L n).U i ⊓ (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ ((LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => i ()) ⊓
        (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ())) :=
      fun z hz => ⟨chart_le i hz.1, chart_le j hz.2⟩
    have ht := congrArg ((toProd P).appLE _ _ e).hom (t.compat (fun _ => i ()) (fun _ => j ()))
    rw [map_mul] at ht
    erw [g_eq i j e] at ht
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply] at ht
    rw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE] at ht
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    exact ht
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} {P : PolAV S}

end GlobalTheory.TrSecDesc
