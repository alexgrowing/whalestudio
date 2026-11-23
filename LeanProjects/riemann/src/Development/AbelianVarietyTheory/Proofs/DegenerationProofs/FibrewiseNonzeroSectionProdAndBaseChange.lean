import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.FibreNonzero

def pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => ((1 : ℕ) : ℤ))) :=
  LBGerm.secOfGerm (fun j => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : Fin 1 => h) j 0)).op).hom
      ((h.app (L.U (j 0))).hom (θ.f (j 0)))) fun y i j hi hj => by
    have hi' : (𝟙 Y ≫ h) y ∈ L.U (i 0) := Set.mem_iInter.1 hi 0
    have hj' : (𝟙 Y ≫ h) y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    refine ((gs_res _ y _ hi _).trans (gs_pull (𝟙 Y) h y _ hi' _)).trans ((gs_compat θ _ y hi' hj').trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) ((gs_res _ y _ hj _).trans (gs_pull (𝟙 Y) h y _ hj' _)).symm))
    refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => h) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 Y) y i j hi hj).symm
    simp

theorem mem_nonzeroLocus_pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) (y : Y) (i : L.ι)
    (hy : h y ∈ X.basicOpen (θ.f i)) : y ∈ nonzeroLocus (pullOne θ h) := by
  have hi' : (𝟙 Y ≫ h) y ∈ L.U i := X.basicOpen_le _ hy
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => i) := Set.mem_iInter.2 fun _ => hi'
  refine (mem_nonzeroLocus_iff_isUnit (pullOne θ h) (k := fun _ => i) hi).2 ?_
  have e := (gs_res (𝟙 Y) y (LB.wchart_le L (fun _ : Fin 1 => h) (fun _ => i) 0) hi _).trans
    (gs_pull (𝟙 Y) h y _ hi' (θ.f i))
  exact e ▸ (LBGerm.isUnit_gs_iff _ y _ hi' _).2 hy

theorem isIso_snd_left {S : Scheme.{0}} (G : Over S) : IsIso (snd (𝟙_ (Over S)) G).left := by
  have : IsIso (snd (𝟙_ (Over S)) G) := by
    rw [← leftUnitor_hom]; infer_instance
  exact inferInstanceAs (IsIso ((Over.forget S).map (snd (𝟙_ (Over S)) G)))

end GlobalTheory.FibreNonzero

open GlobalTheory.FibreNonzero in

theorem GlobalTheory.fibNZ_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  intro R V _ _ _ _ I I' φ D D' A G _ _ A' G' _ _ U U' F C
  have := isIso_snd_left G
  have := isIso_snd_left G'
  refine ⟨fun ⟨θ, hθ⟩ => ⟨pullOne θ _, fun y => ?_⟩, fun k σ σ' h hσ y' => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hθ y
    obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
    refine ⟨z, ?_, mem_nonzeroLocus_pullOne θ _ z i hi⟩
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply, hg]
  · obtain ⟨z, hz, hzσ⟩ := hσ (spMap φ y')
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply] at hz
    obtain ⟨g', hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback C.pb.1 _ y' hz
    obtain ⟨z', rfl⟩ := (snd (𝟙_ _) G').left.surjective g'
    refine ⟨z', by rw [← Over.w (snd (𝟙_ _) G'), Scheme.Hom.comp_apply, hg₂], ?_⟩
    let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
    have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
    have hrz : r z' = z := by
      apply (snd (𝟙_ _) G).left.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hr, Category.id_comp, Scheme.Hom.comp_apply, hg₁]
    obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
    obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
    have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 (hrz ▸ hzσ)
    rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
    exact (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)

end
