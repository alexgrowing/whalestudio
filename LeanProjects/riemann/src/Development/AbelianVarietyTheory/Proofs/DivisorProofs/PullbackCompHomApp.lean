import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open GlobalTheory.GroupBplus (AffOp)
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChainPts.SysB.Form

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.DualPull GlobalTheory.TanSec
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul)

theorem exists_secEquiv {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (R : Type) [CommRing R] [Algebra Γ(X, U) R]
    {j : Sp R ⟶ X} (hj : j = spMap (algebraMap Γ(X, U) R) ≫ hU.fromSpec) (e : ⊤ ≤ j ⁻¹ᵁ U) (M : X.Modules)
    [M.IsQuasicoherent] :
    ∃ Ψ : R ⊗[Γ(X, U)] Γ(M, U) →+ Γ((Scheme.Modules.pullback j).obj M, ⊤), Function.Bijective Ψ ∧
      (∀ (a : R) z, Ψ (a • z) = cst R a • Ψ z) ∧ ∀ s, Ψ (1 ⊗ₜ s) = pullbackSections j M e s := by
  letI := appLEAlgebra j e
  letI := appLEModule j ((Scheme.Modules.pullback j).obj M) e
  haveI := appLE_isScalarTower j ((Scheme.Modules.pullback j).obj M) e
  have hb := isBaseChange_pullbackSections j M (isAffineOpen_top _) hU e
  have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
  have ha (a : Γ(X, U)) : cst R (algebraMap Γ(X, U) R a) = j.appLE U ⊤ e a := by
    subst hj
    have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    refine Eq.trans ?_ (appLE_appLE rfl e₁ (le_preimage_top _ _) e a)
    have e₂ : hU.fromSpec.appLE U ⊤ e₁ a = (Scheme.ΓSpecIso Γ(X, U)).inv a := by
      rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      simp
    rw [e₂]
    exact ((appLE_top _ _).trans congr($(Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap Γ(X, U) R))) a).symm).symm
  let c : R ≃ₗ[Γ(X, U)] Γ(Sp R, ⊤) := LinearEquiv.ofBijective
    { toFun := cst R
      map_add' := map_add _
      map_smul' := fun a b => by
        rw [Algebra.smul_def, map_mul, ha]; rfl } hc
  let Ψ := (c.rTensor Γ(M, U)).toAddEquiv.trans hb.equiv.toAddEquiv
  have hΨ (a : R) (s : Γ(M, U)) : Ψ (a ⊗ₜ s) = cst R a • pullbackSections j M e s := hb.equiv_tmul _ _
  refine ⟨Ψ.toAddMonoidHom, Ψ.bijective, fun a z => ?_, fun s => (hΨ 1 s).trans (by rw [map_one, one_smul])⟩
  change Ψ _ = _ • Ψ _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  | tmul b s => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]

theorem pullbackComp_hom_app {S Y X : Scheme.{0}} (b : S ⟶ Y) (a : Y ⟶ X) (M : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : S.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h₃ : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app M).app T (pullbackSections b _ h₂ (pullbackSections a M h₁ s)) =
      pullbackSections (b ≫ a) M h₃ s := by
  have e₃ := ((Scheme.Modules.pullbackComp b a).app M).inv_hom_id
  rw [← Vert.DivPull.pullbackComp_inv_app b a M h₁ h₂ h₃ s]
  exact congr(($e₃).app _ (pullbackSections (b ≫ a) _ h₃ s))

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X₀ : Scheme.{0}} (t : SAB H X₀) {X : Scheme.{0}} (g : X ⟶ X₀) {R : Type} [CommRing R] (j : Sp R ⟶ X)

theorem val_eq_sum {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t (j ≫ g) v) {U : X.Opens} (e : ⊤ ≤ j ⁻¹ᵁ U)
    (μ : Γ((Scheme.Modules.pullback g).obj (omega t.G), U)) {k : Type} [Field k] (κ : R →+* k)
    (hv' : IsTanAtG t (spMap κ ≫ j ≫ g) (spMap (Formalism.L2.Pj.dualMap κ) ≫ v)) {V : X₀.Opens}
    (hV : ⊤ ≤ (spMap κ ≫ j ≫ g) ⁻¹ᵁ V) {n : ℕ} (m : Fin n → Γ(omega t.G, V)) {T : X.Opens} (hT : T ≤ U)
    (hTV : T ≤ g ⁻¹ᵁ V) (hw : ⊤ ≤ (spMap κ ≫ j) ⁻¹ᵁ T) (c : Fin n → Γ(X, T))
    (hc : resM _ hT μ = ∑ b, c b • pullbackSections g _ hTV (m b)) :
    κ ((Scheme.ΓSpecIso (.of R)).hom ((tanForm t hv).app ⊤
      (((Scheme.Modules.pullbackComp j g).hom.app _).app ⊤ (pullbackSections j _ e μ)))) =
      ∑ b, (Scheme.ΓSpecIso (.of k)).hom ((spMap κ ≫ j).appLE T ⊤ hw (c b)) * tanEv t hv' hV (m b) := by
  have h₀ : ⊤ ≤ spMap κ ⁻¹ᵁ j ⁻¹ᵁ T := hw
  have h₁ : j ⁻¹ᵁ T ≤ (j ≫ g) ⁻¹ᵁ V := j.preimage_mono hTV
  have k₁ (z : Γ(Sp R, ⊤)) : κ ((Scheme.ΓSpecIso (.of R)).hom z) =
      (Scheme.ΓSpecIso (.of k)).hom ((spMap κ).appLE _ ⊤ h₀ (resG _ le_top z)) := by
    rw [appLE_resG, appLE_top]
    exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ)) z).symm
  have k₂ : resM _ (le_top : j ⁻¹ᵁ T ≤ ⊤) (pullbackSections j _ e μ) =
      ∑ b, j.appLE T _ le_rfl (c b) • pullbackSections j _ le_rfl (pullbackSections g _ hTV (m b)) := by
    refine (res_pullbackSections j _ _ _ _).trans ((pullbackSections_res j _ le_rfl hT μ).symm.trans ?_)
    letI := appLEModule j ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback g).obj (omega t.G)))
      (le_refl (j ⁻¹ᵁ T))
    refine (congrArg _ hc).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_))
    exact pullbackSections_smul j _ _ _ _
  let ψ : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback g).obj (omega t.G)) ⟶ structureModule (Sp R) :=
    (Scheme.Modules.pullbackComp j g).hom.app (omega t.G) ≫ tanForm t hv
  let f (b : Fin n) : Γ(Sp R, j ⁻¹ᵁ T) := (tanForm t hv).app _ (pullbackSections (j ≫ g) _ h₁ (m b))
  have k₃ : resG (Sp R) (le_top : j ⁻¹ᵁ T ≤ ⊤) (ψ.app ⊤ (pullbackSections j _ e μ) : Γ(Sp R, ⊤)) =
      ∑ b, j.appLE T _ le_rfl (c b) * f b := by
    refine (app_resM ψ le_top _).symm.trans ?_
    rw [k₂, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Scheme.Modules.Hom.app_smul]
    exact congrArg (fun z => j.appLE T _ le_rfl (c b) * (show Γ(Sp R, j ⁻¹ᵁ T) from (tanForm t hv).app _ z))
      (pullbackComp_hom_app j g _ hTV le_rfl h₁ (m b))
  refine (k₁ _).trans ((congrArg (fun z => (Scheme.ΓSpecIso (.of k)).hom ((spMap κ).appLE _ ⊤ h₀ z)) k₃).trans ?_)
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul, appLE_appLE rfl _ _ hw, tanEv, Glue.tanForm_bc t κ h₁ h₀ hv hv' hV]

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj in

theorem tanEv_of_isCombAtG {k : Type} [CommRing k] {y : Sp k ⟶ X₀} {V : X₀.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V) {n : ℕ}
    {m : Fin n → Γ(omega t.G, V)} (hm : VB.IsFrame m) {r : ℕ} {u : Fin r → (Sp (DualNumber k) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t y (u i)) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t y v) {c : Fin r → k}
    (h : IsCombAtG t y u c v) (b : Fin n) : tanEv t hv hV (m b) = ∑ i, c i * tanEv t (hu i) hV (m b) := by
  obtain ⟨Φ, hΦ⟩ := TanPair.exists_tanM_equiv _ _ _ t k _ V hV n m hm
  have e := (LieMet.isComb_iff (fun i => LieMet.tanOf (hu i)) c (LieMet.tanOf hv)).1 h
  refine (hΦ (LieMet.tanOf hv) b).symm.trans ?_
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, hΦ]
  rfl

end Tan

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X₀ : Scheme.{0}} (t₀ : SAB H X₀) {X : Scheme.{0}} (g : X ⟶ X₀)

theorem exists_lam {U : X.Opens} (hU : IsAffineOpen U) (R : Type) [CommRing R] [Algebra Γ(X, U) R]
    {j : Sp R ⟶ X} (hj : j = spMap (algebraMap Γ(X, U) R) ≫ hU.fromSpec) (e : ⊤ ≤ j ⁻¹ᵁ U) {F : X.Modules}
    (β : (Scheme.Modules.pullback g).obj (omega t₀.G) ⟶ F) [IsIso β] {G : Over (Sp R)} [GrpObj G]
    {φ : G.left ⟶ t₀.G.left} (hG : IsGrpPullback G t₀.G (j ≫ g) φ) :
    ∃ lam : R ⊗[Γ(X, U)] Γ(F, U) →ₗ[R] Pdiv.omega G, Function.Bijective lam ∧
      ∀ (μ : Γ((Scheme.Modules.pullback g).obj (omega t₀.G), U)) (v : Pdiv.LieG G),
        (lam (1 ⊗ₜ β.app U μ)).1 v = (Scheme.ΓSpecIso (.of R)).hom ((tanForm t₀ (TanPair.isTanAtG_lieG hG v)).app ⊤
          (((Scheme.Modules.pullbackComp j g).hom.app _).app ⊤ (pullbackSections j _ e μ))) := by
  have := t₀.semi
  have := t₀.semi.smooth
  have : QuasiSeparated G.hom := MorphismProperty.of_isPullback hG.1 inferInstance
  have : Smooth G.hom := MorphismProperty.of_isPullback hG.1 inferInstance
  have := OmegaGlobal.isQuasicoherent_of_frames (exists_isFrame_omega t₀.G)
  have : F.IsQuasicoherent := isQuasicoherent_of_iso (asIso β)
  obtain ⟨Ψ, h₁, h₂, h₃⟩ := exists_secEquiv hU R hj e F
  let δ : (Scheme.Modules.pullback j).obj F ⟶ omega G :=
    (Scheme.Modules.pullback j).map (inv β) ≫ (Scheme.Modules.pullbackComp j g).hom.app _ ≫ omegaBase hG
  have hδ : Function.Bijective (δ.app ⊤) := ConcreteCategory.bijective_of_isIso (δ.app ⊤)
  have hω := OmegaGlobal.toOmega_bijective R G ⟨tangent_injective R G, TangentSurj.tangent_surjective R G⟩
  refine ⟨{ toFun := fun z => toOmega G (δ.app ⊤ (Ψ z))
            map_add' := fun y z => by rw [map_add, map_add, map_add]
            map_smul' := fun a z => by rw [h₂, Scheme.Modules.Hom.app_smul, toOmega_smul]; rfl },
    hω.comp (hδ.comp h₁), fun μ v => ?_⟩
  have e₀ := IsIso.hom_inv_id β
  have e₁ : (inv β).app U (β.app U μ) = μ := congr(($e₀).app U μ)
  have e₂ := pullback_map_app_pullbackSections j (inv β) e (β.app U μ)
  rw [e₁] at e₂
  rw [TanPair.tanForm_eq hG v _ rfl, ← e₂, ← h₃]
  rfl

end Forms

theorem formSt : GlobalTheory.ChainPts.SysB.FormSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X _ h r x _ hfr U t φt hφt
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  have := OmegaGlobal.isQuasicoherent_of_frames (exists_isFrame_omega (Y Z.i).t.G)
  have := Glue.isIso_theta_om Z h
  have : IsIso (cartierDualToBidual ((Scheme.Modules.pullback h).obj (om Z))) := OmegaGlobal.isIso_toBidual_of_local_frames
    (Frame.frames_pullback h (Frame.frames_pullback Z.π (exists_isFrame_omega (Y Z.i).t.G)))
  have hU : ⊤ ≤ U.toX ⁻¹ᵁ U.1 := fun q _ => by
    change U.toX q ∈ (U.1 : Set X)
    rw [← U.2.1.range_fromSpec]
    exact ⟨spMap (algebraMap Γ(X, U.1) U.Bp) q, rfl⟩
  let γ : (Scheme.Modules.pullback (h ≫ Z.π)).obj (omega (Y Z.i).t.G) ≅ (Scheme.Modules.pullback h).obj (om Z) :=
    ((Scheme.Modules.pullbackComp h Z.π).app _).symm
  let β : (Scheme.Modules.pullback (h ≫ Z.π)).obj (omega (Y Z.i).t.G) ⟶ dual (lieX Z h) :=
    γ.hom ≫ cartierDualToBidual _ ≫ (dualIso (asIso (theta h (om Z)))).hom
  have : IsIso β := (γ ≪≫ asIso (cartierDualToBidual _) ≪≫ dualIso (asIso (theta h (om Z)))).isIso_hom
  obtain ⟨lam, hb, hlam⟩ := exists_lam (Y Z.i).t (h ≫ Z.π) U.2.1 U.Bp (j := U.toX) rfl hU β hφt
  refine ⟨lam, hb, fun σ v k _ κ a φ hφ cf hv => ?_⟩
  obtain ⟨μ, rfl⟩ := (ConcreteCategory.bijective_of_isIso (β.app U.1)).2 σ
  let w : Sp k ⟶ X := spMap κ ≫ U.toX
  have hφ' : spMap φ ≫ Z.chart a = w ≫ h := hφ.trans (Category.assoc _ _ _).symm
  have hy : (w ≫ h) ≫ Z.π = spMap κ ≫ U.toX ≫ h ≫ Z.π := by simp only [w, Category.assoc]
  have hpt {S : Scheme.{0}} (g : Sp k ⟶ S) {U : S.Opens} (hU : g default ∈ U) : ⊤ ≤ g ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim q default]; exact hU
  have hch : (w ≫ h) default ∈ (Z.U a).1 := by
    rw [← hφ']
    exact (chart_image_top Z a).le ⟨spMap φ default, trivial, rfl⟩
  have hwU : w default ∈ U.1 := hU (Opens.mem_top (spMap κ default))
  have htan (i : Fin r) :
      IsTanAtG (Y Z.i).t (spMap κ ≫ U.toX ≫ h ≫ Z.π) ((Z.fr a).bc φ (x i).1 (x i).2) :=
    LieMet.isTan_map φ (by rw [← Category.assoc, hφ', hy]) ((Z.frame a).1 _ _).1
  have hv₀ := TanPair.isTanAtG_lieG hφt v
  have hv' := LieMet.isTan_map κ rfl hv₀
  obtain ⟨V, n, m, hx, hm⟩ := exists_isFrame_omega (Y Z.i).t.G ((spMap κ ≫ U.toX ≫ h ≫ Z.π) default)
  have hV := hpt _ hx
  have hcomb := tanEv_of_isCombAtG (Y Z.i).t hV hm htan hv' hv
  let T₀ : Z.X.Opens := (Z.U a).1 ⊓ Z.π ⁻¹ᵁ V
  have hgT : ⊤ ≤ (w ≫ h) ⁻¹ᵁ T₀ := hpt _ ⟨hch, hx⟩
  let T : X.Opens := U.1 ⊓ h ⁻¹ᵁ T₀
  have hwT : ⊤ ≤ w ⁻¹ᵁ T := hpt _ ⟨hwU, hch, hx⟩
  have hT : T ≤ U.1 ⊓ h ⁻¹ᵁ (Z.U a).1 := inf_le_inf_left _ (h.preimage_mono inf_le_left)
  have hTV : T ≤ (h ≫ Z.π) ⁻¹ᵁ V := inf_le_right.trans (h.preimage_mono inf_le_right)
  obtain ⟨c, hc⟩ : ∃ c : Fin n → Γ(X, T),
      resM _ inf_le_left μ = ∑ b, c b • pullbackSections (h ≫ Z.π) _ hTV (m b) := by
    refine ⟨fun b => ((hm.pullback (h ≫ Z.π)).basis hTV).repr (resM _ inf_le_left μ) b,
      (((hm.pullback (h ≫ Z.π)).basis hTV).sum_repr _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)⟩
    rw [IsFrame.basis_apply]
    exact congrArg _ (res_pullbackSections _ _ _ _ _)
  have hcrd (i : Fin r) : valF w _ (OmegaHT.crd (hfr a).dual (β.app U.1 μ) i) =
      ∑ b, (Scheme.ΓSpecIso (.of k)).hom (w.appLE T ⊤ hwT (c b)) * tanEv _ (htan i) hV (m b) := by
    have hTa : T ≤ h ⁻¹ᵁ (Z.U a).1 := hT.trans inf_le_right
    let s := (theta h (om Z)).app T (pullbackSections h _ hTa (TanSec.sec Z a (Z.fr a (x i).1 (x i).2)))
    have e₁ : resG X hT (OmegaHT.crd (hfr a).dual (β.app U.1 μ) i) =
        dualApp s le_rfl (γ.hom.app T (resM _ inf_le_left μ)) := by
      rw [OmegaHT.crd, (hfr a).dual_basis_repr, ← dualApp_resM, resM_resM, dualApp_res, app_resM]
      have e : resM _ hTa (secX Z h x a i) = pullbackSections h _ hTa (TanSec.sec Z a (Z.fr a (x i).1 (x i).2)) :=
        res_pullbackSections h _ _ _ _
      rw [e]
      rfl
    rw [valF, dif_pos (hwT.trans (w.preimage_mono hT))]
    refine (congrArg (Scheme.ΓSpecIso (.of k)).hom (appLE_resG w hT hwT _)).symm.trans ?_
    rw [e₁, hc, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e₂ : γ.hom.app T (pullbackSections (h ≫ Z.π) _ hTV (m b)) =
        pullbackSections h (om Z) inf_le_right (pullbackSections Z.π _ (inf_le_right : T₀ ≤ _) (m b)) :=
      Vert.DivPull.pullbackComp_inv_app h Z.π _ _ _ _ _
    rw [Scheme.Modules.Hom.app_smul, map_smul, smul_eq_mul, map_mul, map_mul, e₂]
    refine congrArg (_ * ·) (Eq.trans (congrArg (Scheme.ΓSpecIso (.of k)).hom ?_)
      (Glue.appLE_dualApp_sec Z a ((Z.frame a).1 _ _).1 φ hφ' hy (htan i) hV (m b) inf_le_left inf_le_right hgT))
    exact (congrArg (w.appLE _ ⊤ hwT) (dualApp_theta h _ inf_le_left hTa le_rfl inf_le_right _)).trans
      (appLE_appLE rfl _ _ _ _)
  rw [hlam, val_eq_sum (Y Z.i).t (h ≫ Z.π) U.toX hv₀ hU μ κ hv' hV m inf_le_left hTV hwT c hc]
  simp only [hcomb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcrd i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

end GlobalTheory.ChainPts.SysB.Form
