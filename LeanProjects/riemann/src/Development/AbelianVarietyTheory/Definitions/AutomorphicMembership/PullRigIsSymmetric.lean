import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RestrictLineBundleSymmetryUnitsEquivIsoApply
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

section Generators

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

def combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) : LB.Gen (LB.LinComb (LB.LinComb L F δ) φ ε) where
  s := fun jj => ∏ i, res (GeneratorPullback.box_le L F φ jj i) ((t i).s (fun k _ => jj k i)) ^ δ i

theorem gm_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F δ) φ jj) ((combGen L F δ φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem trF_comb (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (jj jj' : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj)
    (h' : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj') :
    trF (L := LB.LinComb L F δ) φ ε r z jj jj' =
      ∏ i, trF (L := L.pull (F i)) φ ε r z (fun k _ => jj k i) (fun k _ => jj' k i) ^ δ i := by
  unfold trF
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (congrArg (· ^ ε k) (gm_linComb L F δ (r ≫ φ k) z (jj k) (jj' k) (Set.mem_iInter.1 h k)
    (Set.mem_iInter.1 h' k))).trans ?_
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← zpow_mul, mul_comm, zpow_mul]
  refine congrArg (fun q => (q ^ ε k) ^ δ i) ?_
  exact (gm_pull_g L (F i) (r ≫ φ k) z (fun _ => jj k i) (fun _ => jj' k i)
    (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj i h) k) (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj' i h') k)).symm

theorem isGen_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (combGen L F δ φ ε t).IsGen := by
  refine isGen_of_gm _ fun y jj jj' h h' => ?_
  rw [gm_combGen L F δ φ ε t (𝟙 Y) y jj h, gm_combGen L F δ φ ε t (𝟙 Y) y jj' h', trF_comb L F δ φ ε (𝟙 Y) y jj jj' h h',
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ δ i) (gen_trans (ht i) (𝟙 Y) y (GeneratorPullback.box_le L F φ jj i h) (GeneratorPullback.box_le L F φ jj' i h'))

variable {L}

theorem good_factor {F : J → (X' ⟶ X)} {δ : J → ℤ} {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) (i : J) : Good (L.pull (F i)) z (fun χ _ => I χ i) :=
  fun χ => mem_pull.2 (Set.mem_iInter.1 (hI χ) i)

theorem val_combGen {F : J → (X' ⟶ X)} {δ : J → ℤ} {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) :
    val (combGen L F δ φ ε t) r z I = ∏ i, val (t i) r z (fun χ _ => I χ i) ^ δ i :=
  gm_combGen L F δ φ ε t r z _ (hI.mem φ r)

end Generators

theorem isCub_prod {B U J : Type} [CommGroup B] [CommGroup U] [Fintype J] (θ : J → B → B → B → U)
    (h : ∀ i, IsCub (θ i)) (δ : J → ℤ) : IsCub fun x y z => ∏ i, θ i x y z ^ δ i where
  face x y := Finset.prod_eq_one fun i _ => by rw [(h i).face, one_zpow]
  s01 x y z := Finset.prod_congr rfl fun i _ => by rw [(h i).s01]
  s12 x y z := Finset.prod_congr rfl fun i _ => by rw [(h i).s12]
  coc x x' x'' y := by
    simp only [← Finset.prod_mul_distrib, ← mul_zpow]
    exact Finset.prod_congr rfl fun i _ => by rw [(h i).coc]

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  {J : Type} [Fintype J]

def pullRig (L : RigLB G) (f : A ⟶ G) [IsMonHom f] : RigLB A :=
  (CubeMap.ofHom f).rigLB L (LB.isLB_linComb L.isLB _ _)
    (LBxP.isGen_pullAlong L.L f.left (𝟙 _) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec A)
      (fun _ => (CubeMap.ofHom f).e_comm) L.rig L.rigGen)

def pullCub {L : RigLB G} (c : CubicalStr G L) (f : A ⟶ G) [IsMonHom f] : CubicalStr A (pullRig L f) :=
  CubePf.cubical (CubeMap.ofHom f) L c _ _

theorem pullRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) (f : A ⟶ G) [IsMonHom f] :
    (pullRig L f).IsSymmetric := by
  obtain ⟨_, _, -, h⟩ := proved_CubePullSt S S G A (CubeMap.ofHom f) L c
  exact h hs

variable (u : J → (A ⟶ G)) [∀ i, IsMonHom (u i)] (δ : J → ℤ)

def combRig (L : RigLB G) : RigLB A where
  L := LB.LinComb L.L (fun i => (u i).left) δ
  rig := combGen L.L (fun i => (u i).left) δ (fun _ : PUnit => eSec A) (fun _ => 1) fun i => (pullRig L (u i)).rig
  isLB := LB.isLB_linComb L.isLB _ _
  rigGen := isGen_combGen _ _ _ _ _ _ fun i => (pullRig L (u i)).rigGen

def combCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (combRig u δ L) :=
  CubTransport.cubicalOfVal (L := combRig u δ L)
    (combGen L.L (fun i => (u i).left) δ (thφ A (x3 A)) thε fun i => (pullCub c (u i)).t)
    (isGen_combGen _ _ _ _ _ _ fun i => (pullCub c (u i)).isGen) fun T z I hI => by
      have h := isCub_prod _ (fun i => isCub_cubV (pullCub c (u i)) (T := T) (good_factor hI i)) δ
      convert h using 4 with x y w
      exact val_combGen (fun i => (pullCub c (u i)).t) _ hI

theorem isSymmetric_iff (L : RigLB G) : L.IsSymmetric ↔ ∃ sy, BoxCompare.IsCanonSym L.L sy := by
  refine ⟨fun ⟨_, w, h⟩ => ?_, fun ⟨sy, h⟩ => ⟨GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv, _, (BoxCompare.isNormSymm_iff L sy).2 h⟩⟩
  obtain ⟨sy, rfl⟩ := (BoxCompare.symEquiv L.L _).surjective w
  exact ⟨sy, (BoxCompare.isNormSymm_iff L sy).1 h⟩

theorem combRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) :
    (combRig u δ L).IsSymmetric := by
  choose sy hsy using fun i => (isSymmetric_iff _).1 (pullRig_isSymmetric c hs (u i))
  refine (isSymmetric_iff _).2 ⟨combGen L.L (fun i => (u i).left) δ _ _ sy,
    isGen_combGen _ _ _ _ _ _ fun i => (hsy i).1, corr_of_val (combRig u δ L).isLB fun y I hI => ?_⟩
  refine (val_pull hI _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  refine (val_combGen sy _ hI).trans (Finset.prod_eq_one fun i _ => ?_)
  have e := (val_pull (good_factor hI i) (sy i) (eSec A) (𝟙 _)).symm.trans
    ((val_corr (good_factor hI i) (hsy i).2 (𝟙 _)).trans (val_one _))
  exact (congrArg (· ^ δ i) e).trans (one_zpow _)

end GlobalTheory.HomComb
