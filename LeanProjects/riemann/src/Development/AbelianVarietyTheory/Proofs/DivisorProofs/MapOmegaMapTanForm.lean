import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLatLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPoint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.DualPull GlobalTheory.TanSec
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul)

namespace GlobalTheory.ChainPts.DualAct

theorem dualMap_coord {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {r : ℕ} {e : Fin r → Γ(F, U)} (he : VB.IsFrame e)
    (u : F ⟶ F) (c : Fin r → Γ(X, U)) (hu : ∀ i, u.app U (e i) = c i • e i) (i : Fin r) :
    (VB.dualMap u).app U (he.coord i) = c i • he.coord i := by
  refine dual_ext fun W hW s => ?_
  rw [dualApp_dualMap, dualApp_smul, LinearMap.smul_apply, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
  have k : u.app W s = ∑ j, ((he.basis hW).repr s j * resG X hW (c j)) • he.basis hW j := by
    conv_lhs => rw [← (he.basis hW).sum_repr s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, app_resM, hu, resM_smul, smul_smul]
  rw [k, (he.basis hW).repr_sum_self, smul_eq_mul, mul_comm]

theorem dualMap_secOf {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (hM : IsIso (theta j M))
    (ψ : (Scheme.Modules.pullback j).obj M ⟶ structureModule Y) (u : M ⟶ M) {U : X.Opens} (hU : U ≤ j ''ᵁ ⊤)
    (hU' : ⊤ ≤ j ⁻¹ᵁ U) (c : Γ(X, U))
    (H : ∀ (T : Y.Opens) (s : Γ((Scheme.Modules.pullback j).obj M, T)),
      ψ.app T (((Scheme.Modules.pullback j).map u).app T s) =
        resG Y (le_top : T ≤ ⊤) (j.appLE U ⊤ hU' c) • ψ.app T s) :
    (VB.dualMap u).app U (resM _ hU (secOf j M ψ)) = c • resM _ hU (secOf j M ψ) := by
  refine dual_ext fun W hW s => ?_
  have hi : Function.Injective (j.appLE W (j ⁻¹ᵁ W) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    haveI := j.isIso_app W (by
      refine (hW.trans hU).trans ?_
      rw [Scheme.Hom.image_top_eq_opensRange])
    exact (ConcreteCategory.bijective_of_isIso (j.app W)).1
  refine hi ?_
  rw [dualApp_dualMap, dualApp_smul, LinearMap.smul_apply, dualApp_res, smul_eq_mul, map_mul,
    Glue.appLE_dualApp_secOf j M hM, Glue.appLE_dualApp_secOf j M hM, ← pullback_map_app_pullbackSections, H,
    appLE_resG, resG_appLE]
  rfl

theorem fromSpec_appLE {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : Sp (DualNumber R) ⟶ t.G.left}

theorem map_omegaMap_tanForm (φ : t.G ⟶ t.G) [IsMonHom φ] (hv : IsTanAtG t x v) (hv' : IsTanAtG t x (v ≫ φ.left)) :
    (Scheme.Modules.pullback x).map (omegaMap φ) ≫ tanForm t hv = tanForm t hv' := by
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (epsIso R).hom) ?_)
  refine pullback_hom_ext (sec_hom (MonObj.one (X := t.G))) fun W b => ?_
  have e₁ : unitSec t.G ≫ φ.left = unitSec t.G := congrArg (·.left) (IsMonHom.one_hom φ)
  have k₁ := (le_preimage_of_comp e₁).2 (le_refl (unitSec t.G ⁻¹ᵁ W))
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) k₁ le_rfl
  have e₂ := (QCoh.pullback_map_app_pullbackSections x (omegaMap φ) le_rfl (dUnit t.G le_rfl b)).trans
    (congrArg (pullbackSections x _ le_rfl) (omegaMap_dUnit φ le_rfl k₁ le_rfl b))
  refine (congrArg ((baseMap (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv)).app _) e₂).trans ?_
  have k₃ : v ⁻¹ᵁ φ.left ⁻¹ᵁ W ≤ (v ≫ φ.left) ⁻¹ᵁ W := le_rfl
  have e₃ := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) k₁ le_rfl
    k₂ le_rfl (φ.left.appLE W _ le_rfl b)
  have e₄ := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero R)) hv'.1 (epsZero_comp_of_isTanAtG t hv') le_rfl
    le_rfl k₂ k₃ b
  have e₅ := appLE_appLE (f := v) (g := φ.left) rfl le_rfl le_rfl k₃ b
  exact e₃.trans ((congrArg (d (sec_hom (epsZero R)) k₂) e₅).trans e₄.symm)

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem tanForm_eig (a : 𝓞 E) (c : R) (hv : IsTanAtG t x v)
    (h : v ≫ (t.act.act a).left = spMap (epsMul c) ≫ v) (T : (Sp R).Opens)
    (s : Γ((Scheme.Modules.pullback x).obj (omega t.G), T)) :
    haveI := t.act.hom a
    (tanForm t hv).app T (((Scheme.Modules.pullback x).map (omegaMap (t.act.act a))).app T s) =
      resG (Sp R) (le_top : T ≤ ⊤) (cst R c) • (tanForm t hv).app T s := by
  haveI := t.act.hom a
  have hv' : IsTanAtG t x (v ≫ (t.act.act a).left) := isTan_tv (actR t.act a (tanOf hv))
  have e : tanOf hv' = c • tanOf hv := tan_ext h
  have k := (Frame.form_spec (t := t) (isGrpPullback_pullback t.G x)).2.1 c (tanOf hv)
  rw [← e] at k
  have k' := congrArg (fun l => dualApp l (le_top : T ≤ ⊤) s) k
  simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul] at k'
  exact (congr(($(map_omegaMap_tanForm t (t.act.act a) hv hv')).app T s)).trans k'

theorem dualMap_secOf_tanMor {Z : Scheme.{0}} (j : Sp R ⟶ Z) [IsOpenImmersion j] (π : Z ⟶ X)
    (hM : IsIso (theta j ((Scheme.Modules.pullback π).obj (omega t.G)))) (hv : IsTanAtG t (j ≫ π) v) (a : 𝓞 E)
    [IsMonHom (t.act.act a)] {c : R} (h : v ≫ (t.act.act a).left = spMap (epsMul c) ≫ v) {U : Z.Opens} (hU : U ≤ j ''ᵁ ⊤)
    (hU' : ⊤ ≤ j ⁻¹ᵁ U) {c' : Γ(Z, U)} (hc : j.appLE U ⊤ hU' c' = cst R c) :
    (VB.dualMap ((Scheme.Modules.pullback π).map (omegaMap (t.act.act a)))).app U
        (resM _ hU (secOf j _ ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v))) =
      c' • resM _ hU (secOf j _ ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) v)) := by
  refine dualMap_secOf j _ hM _ _ hU hU' c' fun T s => ?_
  have k := tanForm_eig t a c hv h T (((Scheme.Modules.pullbackComp j π).hom.app _).app T s)
  have n := (Scheme.Modules.pullbackComp j π).hom.naturality (omegaMap (t.act.act a))
  have n' := congr(($n).app T s)
  rw [hc, Frame.tanMor_eq hv]
  exact (congrArg ((tanForm t hv).app T) n').trans k

end Tan

section Mdl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : LocM.Mdl Y i₀)

def omAct : 𝓞 E →+* End (om Z) :=
  haveI := (Y Z.i).t.semi
  pullAct (omegaAct (Y Z.i).t.act) Z.π

def lieXAct {X : Scheme.{0}} (h : X ⟶ Z.X) : 𝓞 E →+* End (lieX Z h) := pullAct (dualAct (omAct Z)) h

theorem dualMap_sec (a : Fin Z.m) (q : Letter Dw) (c : 𝓞 E) :
    (VB.dualMap (VB.act (omAct Z) c)).app _ (TanSec.sec Z a (Z.fr a q.1 q.2)) =
      Z.alg a (embK Z.i.c q.1 c) • TanSec.sec Z a (Z.fr a q.1 q.2) := by
  have hU' : ⊤ ≤ Z.chart a ⁻¹ᵁ (Z.U a).1 := (Z.U a).2.fromSpec_preimage_self.ge
  haveI := (Y Z.i).t.act.hom c
  exact dualMap_secOf_tanMor (Y Z.i).t (Z.chart a) Z.π (Glue.isIso_theta_om Z _) ((Z.frame a).1 q.1 q.2).1 c
    (((Z.frame a).1 q.1 q.2).2 c) (chart_image_top Z a).ge hU'
    congr($(fromSpec_appLE (Z.U a).2 hU') (Z.alg a (embK Z.i.c q.1 c)))

theorem lieXAct_secX {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (a : Fin Z.m) (i : Fin r) (c : 𝓞 E) :
    (VB.act (lieXAct Z h) c).app _ (secX Z h x a i) =
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 c)) • secX Z h x a i := by
  refine (pullback_map_app_pullbackSections h _ _ _).trans ?_
  refine (congrArg _ (dualMap_sec Z a (x i) c)).trans ?_
  rw [pullbackSections_smul, Scheme.Hom.appLE_eq_app]
  rfl

end Mdl

theorem actSt : SysB.ActSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ _ _ B h r x hx hfr
  have hvbX : IsVB (lieX Z h) r := (GlobalTheory.T.tangent_sheaf_local_model_bundle E H Dw Xo p W Y i₀ Z r x hx).dual.pullback h
  let ρ : 𝓞 E →+* End (dual (lieX Z h)) := (dualAct (lieXAct Z h)).comp H.bar.toRingHom
  refine ⟨ρ.toMonoidHom, fun a b => ρ.map_add a b, hvbX.dual, ⟨fun a => (hfr a).dual, ?_, ?_⟩, fun a i c => ?_⟩
  · intro k _ w a a' φ φ' h1 h2 j
    simp only [GlobalTheory.T.dual_frame_transition_coefficients]
    exact GlobalTheory.T.tangent_frame_at_field_point E H Dw Xo p W Y i₀ Z _ h r x hx hfr k w a a' φ φ' h1 h2 j
  · intro y w hw a φ hφ V e he hV cf v hv
    obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_dual_frame_coefficients _ (lieX Z h) r r hvbX V e he
    simp only [hc]
    exact GlobalTheory.T.tangent_frame_at_integral_point E H Dw Xo p W Y i₀ Z _ h r x hx hfr y w hw a φ hφ V e' he' hV cf v hv
  · exact dualMap_coord (hfr a) (VB.act (lieXAct Z h) (H.bar c)) _ (fun i => lieXAct_secX Z h x a i (H.bar c)) i

end GlobalTheory.ChainPts.DualAct

end
