import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalAdditionFactorGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqSumMulOfIsDomain
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_addG : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  intro V _ _ _ _ D A G _ _ U θ
  have := U.semi.smooth
  have := U.semi.separated
  have := U.semi.quasiCompact
  obtain ⟨v, hv⟩ := exists_addSec _ G U.P (𝟙_ _) θ (toUnit _)
  obtain ⟨v', hv'⟩ := exists_sec U.P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left ≫ 𝟙 G.left) (fun _ => (snd G G).left ≫ 𝟙 G.left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))
    (fun U _ h => by simp only [Category.comp_id]) v
  obtain ⟨r, hr, n, a, b, hab⟩ := GlobalTheory.exists_smul_eq_sum_mul_of_isDomain V G.left U.P.L.L U.P.L.isLB G G (Fin 1) (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) v'
  have mv : ∀ s : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ))),
      ∃ σ : U.SecGT (𝟙_ _) 2, ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
        sval σ (lift (toUnit T) x).left z J = sval s x.left z J := fun s => by
    obtain ⟨σ, hσ⟩ := exists_sec U.P.L.isLB (K' := Fin 1) (φ' := fun _ => (snd (𝟙_ _) G).left)
      (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun U _ h => by simp only [Category.comp_id])
      (H1.SectionArithmetic.pullSec s (snd (𝟙_ _) G).left)
    refine ⟨σ, fun T x z J hJ => (hσ _ _ z J hJ).trans ?_⟩
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, ← Over.comp_left, lift_snd]
  choose mv hmv using mv
  refine ⟨r, n, fun i => mv (a i), fun i => mv (b i), hr, fun T x y z J hJ => ?_⟩
  have e := hab T.left (lift x y).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd, hv' _ _ z J hJ, hv T x y z J hJ,
    toUnit_unique (lift x y ≫ toUnit _) (toUnit T)] at e
  have g : gs (lift x y).left z ⊤ (scal (G ⊗ G).hom r) = gs (𝟙 _) z ⊤ (scal T.hom r) := by
    have p : ∀ {Z Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of V)) (w : Z),
        gs f w ⊤ (scal q r) = gs (f ≫ q) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) :=
      fun f q w => gs_pull f q w ⊤ trivial _
    rw [p, p, Over.w, Category.id_comp]
  simp only [hmv _ T _ z J hJ]
  rw [e, g, _root_.mul_assoc]

end GlobalTheory.UU
end
