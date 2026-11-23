import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordR

open ReciprocityTheory.ChartRestriction.G.Chart (sp fB sp_hom_fB)

section Iso

variable {W : Type} [CommRing W] {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (sp (R₀ := W) (DualNumber R')).hom =
    (epsPtR (spMap (algebraMap W R'))).hom := by
  rw [Category.id_comp]
  exact (sp_hom_fB (R := W) (R' := R') (P := DualNumber R')).symm

theorem epsInv_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (epsPtR (spMap (algebraMap W R'))).hom =
    (sp (R₀ := W) (DualNumber R')).hom := by
  rw [Category.id_comp]
  exact sp_hom_fB (R := W) (R' := R') (P := DualNumber R')

def epsHom : epsPtR (spMap (algebraMap W R')) ⟶ sp (R₀ := W) (DualNumber R') :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsHom_w

def epsInv : sp (R₀ := W) (DualNumber R') ⟶ epsPtR (spMap (algebraMap W R')) :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsInv_w

end Iso

section Main
open GlobalTheory.SqZero
variable {W : Type} [CommRing W] {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR W ⟶ G)} {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_epsInv : epsHom (W := W) (R' := R') ≫ epsInv = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem epsInv_epsHom : epsInv (W := W) (R' := R') ≫ epsHom = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem fst_left : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (fstS W R')).left =
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := rfl

theorem isTanOver_epsInv (w : epsPtR (spMap (algebraMap W R')) ⟶ G)
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left) : IsTanOver (epsInv ≫ w) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, fst_left]
  exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
    (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) w.left)).trans hw

variable (v) in

def coordPt (c : Fin n → R') : epsPtR (spMap (algebraMap W R')) ⟶ G :=
  epsHom ≫ tanExp v c

theorem coordPt_injective [Smooth G.hom] (hv : IsLieBasis v) :
    Function.Injective (coordPt (R' := R') v) := by
  intro c c' h
  have h' := congrArg (epsInv ≫ ·) h
  simp only [coordPt] at h'
  rw [← Category.assoc, ← Category.assoc, epsInv_epsHom, Category.id_comp, Category.id_comp] at h'
  exact (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).1 c c' h'

theorem coordPt_range [Smooth G.hom] (hv : IsLieBasis v) (w : epsPtR (spMap (algebraMap W R')) ⟶ G) :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left ↔ w ∈ Set.range (coordPt v) := by
  constructor
  · intro hw
    obtain ⟨s, hs⟩ := (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).2 _
      (isTanOver_epsInv w hw)
    exact ⟨s, by rw [coordPt, ← hs, ← Category.assoc, epsHom_epsInv, Category.id_comp]⟩
  · rintro ⟨s, rfl⟩
    have := congrArg (fun f => Over.Hom.left f) (isTanOver_tanExp (S := R') hv.1 s)
    rw [Over.comp_left, fst_left] at this
    rw [coordPt, Over.comp_left]
    exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v s).left)).trans this

theorem coordPt_add (hv : IsLieBasis v) (c c' : Fin n → R') :
    coordPt v (c + c') = coordPt v c * coordPt v c' := by
  rw [coordPt, coordPt, coordPt, LieTwo.tanExp_add hv.1, MonObj.comp_mul]

theorem dualScale_eq (s : R') : (dualScale W s).toRingHom = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR])
    (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mul_comm])

theorem coordPt_smul (s : R') (c : Fin n → R') :
    (coordPt v (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (coordPt v c).left := by
  have h1 : s • c = fun i => c i * s := funext fun i => by simp [mul_comm]
  rw [coordPt, coordPt, Over.comp_left, Over.comp_left, h1, ← scl_tanExp, scl, Over.comp_left,
    ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, dualScale_eq]
  exact (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) _).trans
    (congrArg (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v c).left)).symm

variable (v) in

def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) W := by
  classical
  exact if h : ∀ i, IsTangent (v i ≫ u) then
    Matrix.transpose (Matrix.of fun i => (hv.2 _ (h i)).exists.choose) else 0

theorem isTangent_comp (hv : ∀ i, IsTangent (v i)) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    IsTangent (v i ≫ u) := by
  unfold IsTangent at *
  rw [Over.comp_left, ← Category.assoc, hv i, ← Over.comp_left, IsMonHom.one_hom]

theorem comp_eq_tanExp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    v i ≫ u = tanExp v (fun j => lieMat v hv u j i) := by
  have h := isTangent_comp hv.1 u
  have hc := (hv.2 _ (h i)).exists.choose_spec
  rw [isLieComb_iff_lieExp] at hc
  rw [hc]
  simp only [lieMat, dif_pos h, Matrix.transpose_apply, Matrix.of_apply]

theorem coordPt_comp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (c : Fin n → R') :
    coordPt v c ≫ u = coordPt v (((lieMat v hv u).map (algebraMap W R')).mulVec c) := by
  have h1 : tanExp v c ≫ u = tanExp (fun i => v i ≫ u) c := by
    simp only [tanExp, lieExp]
    exact (map_prod (IsMonHom.monoidHom u (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := W) (DualNumber R'))) _ _).trans
      (Finset.prod_congr rfl fun i _ => by
        show (_ ≫ v i) ≫ u = _
        exact Category.assoc _ _ _)
  have hM : ∀ i, res (Algebra.ofId W R') (v i ≫ u) =
      tanExp v (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i)) i) := by
    intro i
    rw [comp_eq_tanExp hv u i, res_tanExp]
    rfl
  have key : Matrix.vecMul c (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i))) =
      ((lieMat v hv u).map (algebraMap W R')).mulVec c := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [coordPt, coordPt, Category.assoc, h1, LieTwo.tanExp_eq_vecMul hv.1 hM, key]

end Main

theorem exists_coords_baseChange : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  intro W _ _ G _ _ hsm
  haveI := hsm
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G hsm
  refine ⟨n, lieMat v hv, fun R' _ β => ?_⟩
  letI := β.toAlgebra
  exact ⟨coordPt v, coordPt_injective hv, coordPt_range hv, coordPt_add hv, coordPt_smul,
    fun u hu c => by haveI := hu; exact coordPt_comp hv u c⟩

end GlobalTheory.LieCoordR
