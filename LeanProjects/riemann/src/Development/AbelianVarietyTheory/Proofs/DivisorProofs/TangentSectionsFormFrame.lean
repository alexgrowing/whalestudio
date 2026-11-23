import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.TanPair GlobalTheory.DualPull
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanSec.Frame

theorem isIso_theta {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ VB.IsFrame e) : IsIso (theta g F) := by
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have : (VB.dual F).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := h x
    ⟨U, n, _, hx, he.dual⟩
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y))
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_
  have H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y)))
      ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i :=
    dual_pull_ext g le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta g _ hW, VB.IsFrame.dualApp_coord, VB.IsFrame.dualApp_coord]
      exact ((he (g y)).pullback_basis_repr g hW e' s i).symm
  have : QCoh.appLinear (theta g F) W =
      (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap :=
    (((he (g y)).dual.pullback g).basis hW).ext fun i => by
      rw [VB.IsFrame.basis_apply, LinearEquiv.coe_coe, VB.IsFrame.equiv_resM_frame, ← H]
      exact Twist.app_resM (theta g F) hW _
  rw [← QCoh.coe_appLinear, this]
  exact LinearEquiv.bijective _

theorem frames_pullback {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ VB.IsFrame e) (y : C) :
    ∃ (U : C.Opens) (n : ℕ) (e : Fin n → Γ((Scheme.Modules.pullback g).obj F, U)), y ∈ U ∧ VB.IsFrame e :=
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have ⟨U, n, _, hx, he⟩ := h (g y)
  ⟨g ⁻¹ᵁ U, n, _, hx, he.pullback g⟩

theorem isFrame_secOf {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (h : IsIso (theta j M))
    {κ : Type} [Fintype κ] (φ : κ → ((Scheme.Modules.pullback j).obj M ⟶ structureModule Y))
    (hφ : VB.IsFrame (F := dual ((Scheme.Modules.pullback j).obj M)) (U := ⊤)
      fun i => (homGlobalEquiv _ _).symm (φ i)) : VB.IsFrame fun i => secOf j M (φ i) := by
  have key := (isFrame_restrict_iff j _).1
    ((hφ.map_iso (inv (theta j M))).map_iso ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app (dual M)))
  have e (i : κ) : secOf j M (φ i) = _ := dif_pos h
  rw [funext e]
  exact key

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X}

theorem exists_unique_coords {Dw : Datum H} {l : Level H} {c : Coeff l} {f : c.F →+* R} {u : Vecs Dw t R}
    (hu : LocM.IsFrame t f x u) (m : TanM x t.G) :
    ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → R, m = ∑ k, a k • tanOf (hu.1 k.1 k.2).1 := by
  classical
  let _ : Algebra c.F R := f.toAlgebra
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨g, hg, hgs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := R) t.act
  have hE : ∀ τ (v : TanM x t.G), PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
      (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ (tv v).left := fun τ v =>
    forall_congr' fun a => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => tan_ext h⟩
  have hS : ∀ τ (a : Fin (Dw.mult τ) → R), PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • tanOf (hu.1 τ i).1) := fun τ a s => by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (hE τ (tanOf (hu.1 τ i).1)).2 (hu.1 τ i).2 s, smul_comm]
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End R (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hco : ∀ τ, ∃! a : Fin (Dw.mult τ) → R, proj ρ (embK c) α τ m = ∑ i, a i • tanOf (hu.1 τ i).1 := fun τ =>
    (existsUnique_congr fun a => isComb_iff (fun i => tanOf (hu.1 τ i).1) a _).1 (hu.2 τ _ (isTan_tv _)
      ((hE τ _).1 (eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj g hg hgs τ m))))
  choose a ha hun using hco
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · beta_reduce
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · beta_reduce at hb
    rw [Fintype.sum_sigma] at hb
    funext ⟨τ, i⟩
    have hn := proj_sum_eig ρ (embK c) α hinj _ (fun τ => hS τ fun i => b ⟨τ, i⟩) τ
    rw [← hb] at hn
    exact congrFun (hun τ (fun i => b ⟨τ, i⟩) hn) i

def form (v : TanM x t.G) : Γ(dual ((Scheme.Modules.pullback x).obj (omega t.G)), ⊤) :=
  (homGlobalEquiv _ _).symm (tanForm t (isTan_tv v))

section Pull

variable {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left} (h' : IsGrpPullback G' t.G x φ)

theorem form_eq (p : LieG G') (v : TanM x t.G) (hp : p.1.left ≫ φ = (tv v).left) :
    form v = (VB.dualMap (omegaBase h')).app ⊤ (tangent p) := by
  rw [form, tanForm_eq h' p _ hp]
  rfl

include h'

theorem form_spec : (∀ v w : TanM x t.G, form (v + w) = form v + form w) ∧
    (∀ (a : R) (v : TanM x t.G), form (a • v) = cst R a • form v) ∧ Function.Bijective (form (t := t) (x := x)) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  have hb : Function.Bijective ((VB.dualMap (omegaBase h')).app ⊤) :=
    ConcreteCategory.bijective_of_isIso ((dualIso (asIso (omegaBase h'))).hom.app ⊤)
  refine ⟨fun v w => ?_, fun a v => ?_, fun v w hvw => ?_, fun s => ?_⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
      (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
    rw [form_eq h' p _ hp, form_eq h' q _ hq, form_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, map_add]
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    have ha : (dualScale a).toRingHom = epsScaleR a := by
      ext y <;> simp [dualScale, epsScaleR]
    have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
      rw [Over.comp_left, Category.assoc, hp]
      exact congrArg (fun r => spMap r ≫ (tv v).left) ha
    rw [form_eq h' p _ hp, form_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale,
      Scheme.Modules.Hom.app_smul]
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    rw [form_eq h' p _ hp, form_eq h' q _ hq] at hvw
    obtain rfl : p = q := tangent_injective R G' (hb.1 hvw)
    exact tan_ext (hp.symm.trans hq)
  · obtain ⟨s, rfl⟩ := hb.2 s
    obtain ⟨p, rfl⟩ := TangentSurj.tangent_surjective R G' s
    exact ⟨tanOf (isTanAtG_lieG h' p), form_eq h' p _ rfl⟩

end Pull

theorem isFrame_form {κ : Type} [Fintype κ] (u : κ → TanM x t.G)
    (hu : ∀ m : TanM x t.G, ∃! a : κ → R, m = ∑ k, a k • u k) : VB.IsFrame fun i => form (u i) := by
  have := t.semi
  have := t.semi.smooth
  have : (dual ((Scheme.Modules.pullback x).obj (omega t.G))).IsQuasicoherent :=
    OmegaGlobal.isQuasicoherent_of_frames fun y =>
      have ⟨U, n, _, hx, he⟩ := frames_pullback x (exists_isFrame_omega t.G) y
      ⟨U, n, _, hx, he.dual⟩
  obtain ⟨h₁, h₂, h₃⟩ := form_spec (t := t) (isGrpPullback_pullback t.G x)
  let Φ : TanM x t.G →+ _ := AddMonoidHom.mk' form h₁
  have hΦ (a : κ → R) : form (∑ k, a k • u k) = ∑ k, cst R (a k) • form (u k) :=
    (map_sum Φ _ _).trans (Finset.sum_congr rfl fun k _ => h₂ _ _)
  have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
  have li : LinearIndependent Γ(Sp R, ⊤) fun i => form (u i) := by
    refine Fintype.linearIndependent_iff.2 fun a ha i => ?_
    choose b hb using fun k => hc.2 (a k)
    obtain rfl : a = fun k => cst R (b k) := funext fun k => (hb k).symm
    have h0 : ∑ k, b k • u k = 0 := h₃.1 ((hΦ b).trans (ha.trans (map_zero Φ).symm))
    have := (hu 0).unique h0.symm (by simp : (0 : TanM x t.G) = ∑ k, (0 : κ → R) k • u k)
    simp [this]
  have sp : ⊤ ≤ Submodule.span Γ(Sp R, ⊤) (Set.range fun i => form (u i)) := fun s _ => by
    obtain ⟨m, rfl⟩ := h₃.2 s
    obtain ⟨a, rfl, -⟩ := hu m
    rw [hΦ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have := Summand.isFrame_of_affine_basis (isAffineOpen_top (Sp R)) (Module.Basis.mk li sp)
  rwa [Module.Basis.coe_mk] at this

theorem tanMor_eq {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) : tanMor t.G x v = tanForm t hv :=
  dif_pos ⟨hv.1, epsZero_comp_of_isTanAtG t hv⟩

theorem isFrame_secOf_tanMor {Z : Scheme.{0}} (j : Sp R ⟶ Z) [IsOpenImmersion j] (π : Z ⟶ X) {Dw : Datum H}
    {l : Level H} {c : Coeff l} {f : c.F →+* R} {u : Vecs Dw t R} (hu : LocM.IsFrame t f (j ≫ π) u) {r : ℕ}
    (y : Fin r → Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hy : Function.Bijective y) :
    VB.IsFrame fun i => secOf j ((Scheme.Modules.pullback π).obj (omega t.G))
      ((Scheme.Modules.pullbackComp j π).hom.app _ ≫ tanMor t.G (j ≫ π) (u (y i).1 (y i).2)) := by
  have := t.semi
  have := t.semi.smooth
  have h₁ := (isFrame_form _ (exists_unique_coords hu)).comp_equiv (Equiv.ofBijective y hy)
  have h₂ := h₁.map_iso (dualIso ((Scheme.Modules.pullbackComp j π).app (omega t.G))).hom
  refine isFrame_secOf j _ (isIso_theta _ (frames_pullback π (exists_isFrame_omega t.G))) _ ?_
  refine (congrArg VB.IsFrame (funext fun i => ?_)).mpr h₂
  rw [tanMor_eq (hu.1 (y i).1 (y i).2).1]
  rfl

end GlobalTheory.TanSec.Frame

namespace GlobalTheory.TanSec.Frame

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

theorem isFrame_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W)
    (i₀ : Idx H p) (Z : GlobalTheory.LocM.Mdl Y i₀) (r : ℕ) (x : Fin r → GlobalTheory.ShFam.Pad.Letter Dw), Function.Bijective x →
    ∀ a : Fin Z.m, GlobalTheory.VB.IsFrame (fun i => GlobalTheory.TanSec.sec Z a (Z.fr a (x i).1 (x i).2)) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z r x hx a
  exact (isFrame_secOf_tanMor (Z.chart a) Z.π (Z.frame a) x hx).res (chart_image_top Z a).ge

end GlobalTheory.TanSec.Frame
