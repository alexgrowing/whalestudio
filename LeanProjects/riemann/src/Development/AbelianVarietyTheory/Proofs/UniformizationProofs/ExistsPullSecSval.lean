import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pullSec_sval {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans
    (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)

theorem whisker_famφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by
  have hu : ρ ▷ D.P.A ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  fin_cases i
  · show (ρ ▷ D.P.A ≫ snd T D.P.A).left = (snd T' D.P.A).left
    rw [whiskerRight_snd]
  · show (ρ ▷ D.P.A ≫ padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (snd T' D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, whiskerRight_snd, ← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ D.c α).left = (toUnit (T' ⊗ D.P.A) ≫ D.c α).left
    rw [← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit (T' ⊗ D.P.A) ≫ η[D.P.A]).left
    rw [← Category.assoc, hu]

theorem expT_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → ∃ (σ' : U.SecGT T' k) (f' : ∀ α, SecBT D T' k α), U.ExpT T' k σ' f' ∧ PullT ρ f f' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T') (s : Raw D F k), PullB D F φ k f' s ↔ PullB D F (φ ≫ ρ) k f s := by
  intro R _ _ I D A G _ _ U T T' ρ k σ f H
  obtain ⟨σ', hσ⟩ := exists_pullSec_sval σ (ρ ▷ G).left (fun _ => (snd T' G).left) (fun _ => by
    show (ρ ▷ G ≫ snd T G).left = _
    rw [whiskerRight_snd])
  choose f' hf using fun α => exists_pullSec_sval (f α) (ρ ▷ D.P.A).left (famφT D T' α) (whisker_famφT D ρ α)
  have s1 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (snd T B).left = (snd T' B).left := fun B => by
    show (ρ ▷ B ≫ snd T B).left = _
    rw [whiskerRight_snd]
  have s2 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun B => by
    show (ρ ▷ B ≫ fst T B).left = (fst T' B ≫ ρ).left
    rw [whiskerRight_fst]
  refine ⟨σ', f', fun e => ?_, fun α Z r z J hJ => hf α Z r z J hJ, fun F _ _ φ s => ?_⟩
  · obtain ⟨s, hs⟩ := H e
    refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hJ => ?_⟩
    have := hs Z x (rG ≫ (ρ ▷ G).left) (rB ≫ (ρ ▷ D.P.A).left) (by rw [Category.assoc, s1, h1])
      (by rw [Category.assoc, s1, h2])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h3, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => (hf α Z rB z J hJ).trans (this.1 α hα), ?_⟩
    rw [hσ Z rG z JG hG, this.2]
    exact Finset.sum_congr rfl fun α _ => by rw [hf α Z rB z J hJ]
  · have e : (φ ▷ D.P.A).left ≫ (ρ ▷ D.P.A).left = ((φ ≫ ρ) ▷ D.P.A).left := by
      rw [comp_whiskerRight]; rfl
    have key : ∀ α (z : (DegPre.BF D F).left) J, Good D.P.L z J →
        sval (f' α) (φ ▷ D.P.A).left z J = sval (f α) ((φ ≫ ρ) ▷ D.P.A).left z J := fun α z J hJ =>
      (hf α _ (φ ▷ D.P.A).left z J hJ).trans (congrArg (fun q => sval (f α) q z J) e)
    exact ⟨fun h α z J hJ => (h α z J hJ).trans (key α z J hJ), fun h α z J hJ => (h α z J hJ).trans (key α z J hJ).symm⟩

end GlobalTheory.UU
