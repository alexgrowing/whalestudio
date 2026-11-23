import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt

noncomputable section

namespace GlobalTheory.SplitBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

section One

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}
  {s : ∀ T : Over (Sp R), (T ⟶ D.P.A) → GtPt D T} (hs : IsSplit D n s)
include hs

theorem cv_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) : cv (s T 1) χ y J = 1 := by
  have e := ((TorusModel.isAdd_iff _ _ _).1 (hs.2.1 T 1 1)).2 χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [_root_.mul_one, hs.1, one_pow, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm)

theorem val_univ {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((s T b).s χ) r z J = val ((s D.P.A (𝟙 _)).s χ) (r ≫ b.left) z J := by
  have e := hs.2.2 D.P.A T b (𝟙 _)
  rw [Category.comp_id] at e
  exact (val_corr hJ (e.2 χ) r).trans (val_pull hJ _ _ _)

theorem val_univ_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) :
    val ((s D.P.A (𝟙 _)).s χ) (1 : T ⟶ D.P.A).left y J = 1 := by
  have e := val_univ hs (1 : T ⟶ D.P.A) χ (𝟙 _) hJ
  rw [Category.id_comp] at e
  exact e.symm.trans (cv_one hs T χ hJ)

theorem gtTanR_split {v : epsR R ⟶ D.P.A} (hv : IsTangent v) : GtTanR (s (epsR R) v) := by
  let o : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))
  have ho : o ≫ v = 1 := Over.OverMorphism.ext (hv.trans (Category.id_comp _).symm)
  have e := hs.2.2 _ _ o v
  rw [ho] at e
  refine ⟨s _ 1, ⟨(hs.1 _ _).trans (one_pow n), fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, e⟩
  exact (cv_one hs _ χ hJ).trans (val_one _).symm

end One

section Two

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D₀ : DegPre R}
  {D₁ : DegPre R'} (p : IsPullDeg f D₀ D₁) {n : ℕ} {s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → GtPt D₀ T}
  {s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → GtPt D₁ T}

theorem univ_corr (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) (χ : D₁.X) :
    (∀ k, DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k ≫ prj p =
      prj p ≫ DegPre.gtφT D₀ D₀.P.A (s₀ D₀.P.A (𝟙 _)).b (p.xe χ) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) J J', Good D₀.P.L z J → Good D₁.P.L z J' →
      val ((s₀ D₀.P.A (𝟙 _)).s (p.xe χ)) (r ≫ prj p) z J =
        (∏ k, ConstFam.wVal p.w z J J' (r ≫ DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k) ^ DegPre.gtε k) *
          val ((s₁ D₁.P.A (𝟙 _)).s χ) r z J' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := D₀.P.A) (T' := D₁.P.A) (prj p) gp.1.w (s₀ D₀.P.A (𝟙 _))
  let ρ : Over.mk (D₁.P.A.hom ≫ spMap f) ⟶ D₀.P.A := Over.homMk (prj p) gp.1.w
  have hρ : pushHom gp D₁.P.A (𝟙 _) = ρ := Over.OverMorphism.ext (Category.id_comp _)
  have r₁ : pushHom gp D₁.P.A g.b = ρ ≫ (s₀ D₀.P.A (𝟙 _)).b := Over.OverMorphism.ext ((hg 0).1 2)
  have hb : g.b = (s₁ D₁.P.A (𝟙 _)).b := ConstGrp.push_injective gp _ (by
    rw [r₁, h₀.1, h₁.1, map_pow, hρ, MonObj.comp_pow, Category.comp_id])
  have he : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ D₁.P.A.hom = 𝟙 _ := Over.w _
  have key := gen_unique' D₁.P.isLB (u := g.s χ) (u' := (s₁ D₁.P.A (𝟙 _)).s χ) (fun U _ k => by rw [hb]) D₁.P.A.hom _ he
    (hG _ _ D₁.P.isAb).2 (g.isGen χ) ((s₁ D₁.P.A (𝟙 _)).isGen χ) (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D₀.P.isLB y
      have v := (hg χ).2 _ (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left y J J' hJ hJ'
      have o : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ prj p =
          (1 : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ D₀.P.A).left :=
        congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have q := FormalPoint.prod_gtφT (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A) g.b χ (ConstFam.wVal p.w y J J')
      rw [hb, h₁.1, MonObj.comp_pow, Category.comp_id, one_pow, _root_.mul_one, inv_mul_cancel, _root_.one_mul,
        mul_inv_cancel, ← h₁.1, ← hb] at q
      rw [o, q, _root_.one_mul] at v
      exact v.symm.trans ((val_univ_one h₀ (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f)) _ hJ).trans
        (val_univ_one h₁ _ χ hJ').symm))
  refine ⟨fun k => hb ▸ (hg χ).1 k, fun Z r z J J' hJ hJ' => ?_⟩
  rw [← key Z r z J' hJ', ← hb]
  exact (hg χ).2 Z r z J J' hJ hJ'

theorem letBC_split (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) {v : epsR R ⟶ D₀.P.A}
    {v₁ : epsR R' ⟶ D₁.P.A} (hv : v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left) :
    LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) := by
  have a₀ : ∀ x k, DegPre.gtφT D₀ _ (s₀ (epsR R) v).b x k = v.left ≫ DegPre.gtφT D₀ _ (s₀ D₀.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₀.2.2 _ _ v (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₀ (epsR R) v).b v.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have a₁ : ∀ x k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b x k = v₁.left ≫ DegPre.gtφT D₁ _ (s₁ D₁.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₁.2.2 _ _ v₁ (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₁ (epsR R') v₁).b v₁.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have hψ : ∀ χ k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b χ k ≫ prj p =
      spMap (dualMap f) ≫ DegPre.gtφT D₀ _ (s₀ (epsR R) v).b (p.xe χ) k := fun χ k => by
    rw [a₀, a₁, Category.assoc, (univ_corr p hG h₀ h₁ χ).1, ← Category.assoc, hv, Category.assoc]
  refine (ArcQBC.letBC_iff p _ _).2 ⟨hψ 0 2, fun χ => ⟨hψ χ, ArcQBC.pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hψ χ)
    ((s₁ _ v₁).isGen χ) ((s₀ _ v).isGen _) fun y J J' hJ hJ' => ?_⟩⟩
  have e := (univ_corr p hG h₀ h₁ χ).2 _ v₁.left y J J' hJ hJ'
  rw [hv] at e
  refine (val_univ h₀ v _ _ hJ).trans ?_
  rw [val_univ h₁ v₁ χ _ hJ']
  simp only [Category.id_comp, a₁]
  exact e

end Two

theorem split_baseChange : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ) (s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T) (s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → Out.GtPt D₁ T), Function.Injective f → IsSplit D₀ n s₀ → IsSplit D₁ n s₁ → ∀ (v : epsR R ⟶ D₀.P.A) (v₁ : epsR R' ⟶ D₁.P.A), v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left → (IsTangent v → GtTanR (s₀ (epsR R) v)) ∧ LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) :=
  fun hK _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ h₀ h₁ _ _ hv =>
    ⟨fun ht => gtTanR_split h₀ ht, letBC_split p hK.laws.globalFns h₀ h₁ hv⟩

end GlobalTheory.SplitBC
