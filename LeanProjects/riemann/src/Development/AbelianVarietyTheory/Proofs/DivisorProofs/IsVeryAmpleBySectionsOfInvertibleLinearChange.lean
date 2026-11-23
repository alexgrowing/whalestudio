import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinChange

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

def lin (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    Fin (n + 1) → H.Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j

theorem cst_eq (f : X ⟶ Sp R) (W : X.Opens) (r : R) :
    GlobalTheory.AbLaw.cst f W r = (baseRingHom f W).hom r := by
  rw [← baseRingHom_res f (le_top : W ≤ ⊤), baseRingHom_top]
  rfl

theorem resG_cst (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    resG X h (GlobalTheory.AbLaw.cst f U r) = GlobalTheory.AbLaw.cst f V r :=
  GlobalTheory.AbLaw.rs_cst f h r

theorem sum_f {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) : (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem lin_f (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec)
    (i : Fin (n + 1)) (k : H.ι) :
    (lin f a s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (s j).f k := by
  rw [lin, sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, resG_cst]

theorem lin_lin (f : X ⟶ Sp R) (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    lin f b (lin f a s) = lin f (b * a) s := by
  funext i
  simp only [lin, Finset.smul_sum, smul_smul, ← map_mul, Matrix.mul_apply, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem lin_one (f : X ⟶ Sp R) (s : Fin (n + 1) → H.Sec) : lin f 1 s = s := by
  funext i
  simp [lin, Matrix.one_apply, apply_ite]

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem iSup_nonzeroLocus_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    {a : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (ha : IsUnit a.det) :
    ⨆ i, nonzeroLocus (lin f a s i) = ⊤ := by
  have hb : lin f a⁻¹ (lin f a s) = s := by rw [lin_lin, Matrix.nonsing_inv_mul a ha, lin_one]
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((lin f a s j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)
  rw [← hb, lin_f, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem appLE_cst {Y : Scheme.{0}} (p : Y ⟶ Sp R) (g : X ⟶ Y) {U : Y.Opens} {W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (r : R) :
    (g.appLE U W h).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (g ≫ p) W r := by
  rw [cst_eq, cst_eq, ← GlobalTheory.ProjSpace.baseRingHom_appLE p g U W h]
  rfl

theorem toProj_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ht : ⨆ i, nonzeroLocus (lin f a s i) = ⊤)
    (hc : ⨆ i, nonzeroLocus (lin (PSpace.str R n) a (coord R n) i) = ⊤) :
    toProj f (lin f a s) ht =
      toProj f s hs ≫ toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n)) hc := by
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := PSpace.str R n) hc (toProj f s hs)
    (t := lin f a s) ht ?_
  · rwa [toProj_str] at e
  intro z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (s i) ⊓ H.U l ≤ toProj f s hs ⁻¹ᵁ chart R n i :=
    inf_le_left.trans (toProj_preimage_chart f s hs i).ge
  refine ⟨nonzeroLocus (s i) ⊓ H.U l, ⟨hi, hl⟩, i, hW, l, inf_le_right, resG X inf_le_right ((s i).f l),
    fun j => ?_⟩
  rw [lin_f, lin_f (H := O1 R n) (PSpace.str R n) a (coord R n) j i, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, resG_cst, coord_f]
  erw [appLE_cst (PSpace.str R n) (toProj f s hs) hW (a j m)]
  rw [toProj_str]
  change _ = _ * (_ * pullRatio (toProj f s hs) _ i hW m)
  generalize (GlobalTheory.AbLaw.cst f (nonzeroLocus (s i) ⊓ H.U l)) (a j m) = c
  rw [pullRatio_toProj_on, secRatio_on (s i) (s m) l inf_le_left inf_le_right]
  ring

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj coord iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem toProj_congr (f : X ⟶ Sp R) {s t : Fin (n + 1) → H.Sec} (h : s = t) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) : toProj f s hs = toProj f t ht := by
  subst h
  rfl

def linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : PSpace R n ⟶ PSpace R n :=
  toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n))
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha)

theorem linAut_comp (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hba : IsUnit (b * a).det) : linAut a ha ≫ linAut b hb = linAut (b * a) hba :=
  (toProj_lin (PSpace.str R n) _ b
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha) hb) _).symm.trans (toProj_congr _ (lin_lin _ a b _) _ _)

theorem linAut_one (h : IsUnit (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).det) : linAut 1 h = 𝟙 (PSpace R n) :=
  (toProj_congr _ (lin_one _ _) _ _).trans (toProj_coord R n)

instance isIso_linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : IsIso (linAut a ha) := by
  have hb : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det a ha
  refine ⟨⟨linAut a⁻¹ hb, ?_, ?_⟩⟩
  · rw [linAut_comp a a⁻¹ ha hb (by rw [Matrix.nonsing_inv_mul a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.nonsing_inv_mul a ha]
    exact linAut_one _
  · rw [linAut_comp a⁻¹ a hb ha (by rw [Matrix.mul_nonsing_inv a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.mul_nonsing_inv a ha]
    exact linAut_one _

end GlobalTheory.LinChange

theorem GlobalTheory.veryAmpleBy_linChange : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ)
    (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB →
    GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  intro R _ X f H n s a ha _ hv
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f (GlobalTheory.LinChange.lin f a s)).2
    ⟨GlobalTheory.LinChange.iSup_nonzeroLocus_lin f hs ha, ?_⟩
  rw [GlobalTheory.LinChange.toProj_lin f hs a _ (GlobalTheory.LinChange.iSup_nonzeroLocus_lin _
    (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord R n) ha)]
  exact (inferInstance : IsClosedImmersion (GlobalTheory.ProjSpace.toProj f s hs ≫ GlobalTheory.LinChange.linAut a ha))
