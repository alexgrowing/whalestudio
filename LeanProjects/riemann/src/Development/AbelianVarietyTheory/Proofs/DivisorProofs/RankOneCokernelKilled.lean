import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomOfSecSecPowAppChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationMapMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LinePow

section Scheme

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB (IsVB IsFrame Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)

variable {X Y : Scheme.{0}}

theorem isUnit_of_isFrame {E : X.Modules} {U : X.Opens} {e e' : Fin 1 → Γ(E, U)} (he : IsFrame e)
    (he' : IsFrame e') {a : Γ(X, U)} (h : e' 0 = a • e 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := exists_eq_smul he' le_rfl (e 0)
  rw [resM_self, h, smul_smul] at hb
  refine IsUnit.of_mul_eq_one_right b (eq_of_smul_eq he le_rfl ?_)
  rw [resM_self, one_smul, ← hb]

theorem isFrame_of_isUnit {E : X.Modules} {U : X.Opens} {e e' : Fin 1 → Γ(E, U)} (he : IsFrame e)
    {a : Γ(X, U)} (ha : IsUnit a) (h : ∀ i, e' i = a • e i) : IsFrame e' :=
  GlobalTheory.VB.isFrame_of_basis (fun V hV => (he.basis hV).isUnitSMul (w := fun _ => resG X hV a)
    fun _ => ha.map _) fun V hV i => by
      rw [Module.Basis.isUnitSMul_apply, IsFrame.basis_apply, h, resM_smul]

theorem exists_frames {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) (x : X) :
    ∃ (U : X.Opens) (e : Fin 1 → Γ(E, U)) (e' : Fin 1 → Γ(E', U)) (_ : IsFrame e) (_ : IsFrame e')
      (a : Γ(X, U)), x ∈ U ∧ ψ.app U (e' 0) = a • e 0 := by
  obtain ⟨U, e, hx, he⟩ := hE x
  obtain ⟨V, e', -, hx', hle, he'⟩ := hE'.exists_affine hx
  obtain ⟨a, ha⟩ := exists_eq_smul he hle (ψ.app V (e' 0))
  exact ⟨V, _, e', he.res hle, he', a, hx', ha⟩

theorem powHom_app_frm_self {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) (n : ℕ)
    {U : X.Opens} {e : Fin 1 → Γ(E, U)} {e' : Fin 1 → Γ(E', U)} (he : IsFrame e) (he' : IsFrame e')
    {a : Γ(X, U)} (ha : ψ.app U (e' 0) = a • e 0) (i j : Fin 1) :
    (powHom hE hE' ψ n).app U (frm hE' n ⟨U, e', he'⟩ i) = a ^ n • frm hE n ⟨U, e, he⟩ j := by
  have := powHom_app_frm hE hE' ψ n ⟨U, e, he⟩ ⟨U, e', he'⟩ (V := U) le_rfl le_rfl (a := a)
    (by rw [resM_self, resM_self]; exact ha) i j
  rwa [resM_self, resM_self] at this

theorem isIso_powHom_zero {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) :
    IsIso (powHom hE hE' ψ 0) :=
  GlobalTheory.VB.isIso_of_frames _ fun x =>
    have ⟨U, _, _, he, he', _, hx, ha⟩ := exists_frames hE hE' ψ x
    ⟨U, _, hx, isFrame_frm hE' 0 ⟨U, _, he'⟩, isFrame_of_isUnit (isFrame_frm hE 0 ⟨U, _, he⟩)
      (by rw [pow_zero]; exact isUnit_one) fun i => powHom_app_frm_self hE hE' ψ 0 he he' ha i i⟩

theorem pullback_map_app_of_eq_smul (f : Y ⟶ X) {F G : X.Modules} (φ : F ⟶ G) {U : X.Opens}
    {s : Γ(F, U)} {t : Γ(G, U)} {a : Γ(X, U)} (h : φ.app U s = a • t) {T : Y.Opens}
    (hT : T ≤ f ⁻¹ᵁ U) : ((Scheme.Modules.pullback f).map φ).app T (pullbackSections f F hT s) =
      f.appLE U T hT a • pullbackSections f G hT t := by
  rw [QCoh.pullback_map_app_pullbackSections, h, QCoh.pullbackSections_smul]

theorem isIso_pullback_powHom (f : Y ⟶ X) {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1)
    (ψ : E' ⟶ E) [IsIso ((Scheme.Modules.pullback f).map ψ)] (n : ℕ) :
    IsIso ((Scheme.Modules.pullback f).map (powHom hE hE' ψ n)) := by
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  have := (isVB_powMod hE n).isQuasicoherent
  have := (isVB_powMod hE' n).isQuasicoherent
  refine GlobalTheory.VB.isIso_of_frames (ι := Fin 1) _ fun y => ?_
  obtain ⟨U, e, e', he, he', a, hx, ha⟩ := exists_frames hE hE' ψ (f y)
  have hu : IsUnit (f.appLE U _ le_rfl a) := isUnit_of_isFrame (he.pullback f)
    ((he'.pullback f).map_iso ((Scheme.Modules.pullback f).map ψ))
    (pullback_map_app_of_eq_smul f ψ ha le_rfl)
  refine ⟨f ⁻¹ᵁ U, _, hx, (isFrame_frm hE' n ⟨U, _, he'⟩).pullback f,
    isFrame_of_isUnit ((isFrame_frm hE n ⟨U, _, he⟩).pullback f) (a := f.appLE U _ le_rfl (a ^ n))
      (by rw [map_pow]; exact hu.pow n) fun i => ?_⟩
  exact pullback_map_app_of_eq_smul f _ (powHom_app_frm_self hE hE' ψ n he he' ha i i) le_rfl

theorem smulHom_cokernel_powHom {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E)
    [Mono ψ] {g : Γ(X, ⊤)} (hg : smulHom (cokernel ψ) g = 0) (n : ℕ) :
    smulHom (cokernel (powHom hE hE' ψ n)) (g ^ n) = 0 := by
  have h0 : smulHom E g ≫ cokernel.π ψ = 0 := by rw [smulHom_comp, hg, comp_zero]
  have hβ := Abelian.monoLift_comp ψ _ h0
  generalize Abelian.monoLift ψ _ h0 = β at hβ
  have key : powHom hE' hE β n ≫ powHom hE hE' ψ n = smulHom _ (g ^ n) := by
    refine hom_ext_of_frames (ι := Fin 1) fun x => ?_
    obtain ⟨U, e, e', he, he', a, hx, ha⟩ := exists_frames hE hE' ψ x
    obtain ⟨b, hb⟩ := exists_eq_smul he' le_rfl (β.app U (e 0))
    rw [resM_self] at hb
    have h1 := congrArg (fun φ => φ.app U (e 0)) hβ
    simp only [← QCoh.app_app, hb, Scheme.Modules.Hom.app_smul, ha, smul_smul, smulHom_app_apply] at h1
    have h2 : b * a = resG X le_top g := eq_of_smul_eq he le_rfl (by rw [resM_self]; exact h1)
    refine ⟨U, _, hx, isFrame_frm hE n ⟨U, _, he⟩, fun i => ?_⟩
    rw [← QCoh.app_app, powHom_app_frm_self hE' hE β n he' he hb i i, Scheme.Modules.Hom.app_smul,
      powHom_app_frm_self hE hE' ψ n he he' ha i i, smul_smul, ← mul_pow, h2, ← map_pow]
    rfl
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [comp_zero, ← smulHom_comp, ← key, Category.assoc, cokernel.condition, comp_zero]

theorem isFrame_pullbackSections (f : Y ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens}
    {e : Fin 1 → Γ(F, U)} (he : IsFrame e) {T : Y.Opens} (hT : T ≤ f ⁻¹ᵁ U) :
    IsFrame fun i => pullbackSections f F hT (e i) := by
  have := (he.pullback f).res hT
  rwa [funext fun i => QCoh.res_pullbackSections f F le_rfl hT (e i)] at this

theorem resM_pullbackSections (f : Y ⟶ X) {F : X.Modules} {U U' : X.Opens} {s : Γ(F, U)} {s' : Γ(F, U')}
    {a : Γ(X, U ⊓ U')} (h : resM F inf_le_right s' = a • resM F inf_le_left s) {T T' : Y.Opens}
    (hT : T ≤ f ⁻¹ᵁ U) (hT' : T' ≤ f ⁻¹ᵁ U') (hl : T ⊓ T' ≤ f ⁻¹ᵁ (U ⊓ U')) :
    resM _ inf_le_right (pullbackSections f F hT' s') =
      f.appLE _ _ hl a • resM _ inf_le_left (pullbackSections f F hT s) := by
  have := congrArg (pullbackSections f F hl) h
  rw [QCoh.pullbackSections_smul] at this
  refine (QCoh.res_pullbackSections _ _ _ _ _).trans (((QCoh.pullbackSections_res _ _ _ _ _).symm.trans
    this).trans (congrArg _ ?_))
  exact (QCoh.pullbackSections_res _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm

variable {f g : Y ⟶ X} {n : ℕ} (hU : ∀ U : X.Opens, f ⁻¹ᵁ U ≤ g ⁻¹ᵁ U)
  (hfg : ∀ (U : X.Opens) (T : Y.Opens) (h : T ≤ f ⁻¹ᵁ U) (a : Γ(X, U)),
    g.appLE U T (h.trans (hU U)) a = f.appLE U T h a ^ n)

include hfg in

theorem exists_iso_pullback_powMod {E : X.Modules} (hE : IsVB E 1) :
    ∃ θ : (Scheme.Modules.pullback f).obj (powMod E n) ≅ (Scheme.Modules.pullback g).obj E,
      ∀ (c : Chart E 1) (i : Fin 1), θ.hom.app (f ⁻¹ᵁ c.U) (pullbackSections f _ le_rfl (frm hE n c i)) =
        pullbackSections g E (hU c.U) (c.e i) := by
  have := hE.isQuasicoherent
  have := (isVB_powMod hE n).isQuasicoherent
  refine exists_iso_of_frames (U := fun c : Chart E 1 => f ⁻¹ᵁ c.U) (top_le_iff.1 fun y _ => ?_)
    (fun c => (isFrame_frm hE n c).pullback f) (fun c => isFrame_pullbackSections g c.isFrame (hU c.U))
    fun c c' => ?_
  · obtain ⟨U, e, hx, he⟩ := hE (f y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, e, he⟩, hx⟩
  · obtain ⟨a, ha⟩ := exists_eq_smul c.isFrame (inf_le_left : c.U ⊓ c'.U ≤ c.U)
      (resM E inf_le_right (c'.e 0))
    have hl : f ⁻¹ᵁ c.U ⊓ f ⁻¹ᵁ c'.U ≤ f ⁻¹ᵁ (c.U ⊓ c'.U) := fun _ hy => hy
    refine ⟨f.appLE _ _ hl (a ^ n), resM_pullbackSections f (resM_frm hE n c c' _ _ ha 0 0) _ _ hl, ?_⟩
    rw [map_pow, ← hfg]
    exact resM_pullbackSections g ha _ _ _

include hfg in

theorem nonempty_iso_pullback_cokernel {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1)
    (ψ : E' ⟶ E) : Nonempty ((Scheme.Modules.pullback f).obj (cokernel (powHom hE hE' ψ n)) ≅
      (Scheme.Modules.pullback g).obj (cokernel ψ)) := by
  have := (isVB_powMod hE' n).isQuasicoherent
  obtain ⟨θ, hθ⟩ := exists_iso_pullback_powMod hU hfg hE
  obtain ⟨θ', hθ'⟩ := exists_iso_pullback_powMod hU hfg hE'
  have sq : (Scheme.Modules.pullback f).map (powHom hE hE' ψ n) ≫ θ.hom =
      θ'.hom ≫ (Scheme.Modules.pullback g).map ψ := by
    refine hom_ext_of_frames (ι := Fin 1) fun y => ?_
    obtain ⟨U, e, e', he, he', a, hx, ha⟩ := exists_frames hE hE' ψ (f y)
    refine ⟨f ⁻¹ᵁ U, _, hx, (isFrame_frm hE' n ⟨U, _, he'⟩).pullback f, fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h1 := pullback_map_app_of_eq_smul f _ (powHom_app_frm_self hE hE' ψ n he he' ha 0 0) le_rfl
    have h2 := pullback_map_app_of_eq_smul g ψ ha (hU U)
    refine (QCoh.app_app _ _ _ _).symm.trans (Eq.trans ?_ (QCoh.app_app _ _ _ _))
    refine (congrArg _ h1).trans (Eq.trans ?_ ((congrArg _ (hθ' ⟨U, _, he'⟩ 0)).trans h2).symm)
    rw [Scheme.Modules.Hom.app_smul, map_pow, ← hfg]
    exact congrArg _ (hθ ⟨U, _, he⟩ 0)
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) _ ≪≫ cokernel.mapIso _ _ θ' θ sq ≪≫
    (PreservesCokernel.iso (Scheme.Modules.pullback g) _).symm⟩

theorem det_smul {E : X.Modules} {U V : X.Opens} {e : Fin 1 → Γ(E, U)} (he : IsFrame e) (h : V ≤ U)
    (s : Fin 1 → Γ(E, V)) : s 0 = (he.basis h).det s • resM E h (e 0) := by
  rw [Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply, ← he.basis_apply]
  simpa using ((he.basis h).sum_repr (s 0)).symm

theorem exists_det_powHom {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) (n : ℕ)
    (c : Chart E 1) (c' : Chart E' 1) (d : Chart (powMod E n) 1) (d' : Chart (powMod E' n) 1)
    {V : X.Opens} (h : V ≤ c.U) (h' : V ≤ c'.U) (k : V ≤ d.U) (k' : V ≤ d'.U) : ∃ u : Γ(X, V)ˣ,
      ((d.isFrame.basis k).det fun i => (powHom hE hE' ψ n).app V (resM _ k' (d'.e i))) =
        u * ((c.isFrame.basis h).det fun i => ψ.app V (resM E' h' (c'.e i))) ^ n := by
  obtain ⟨u, hu⟩ := exists_eq_smul d.isFrame k (resM _ h (frm hE n c 0))
  obtain ⟨u', hu'⟩ := exists_eq_smul (isFrame_frm hE' n c') h' (resM _ k' (d'.e 0))
  obtain ⟨u, rfl⟩ := isUnit_of_isFrame (d.isFrame.res k) ((isFrame_frm hE n c).res h) hu
  obtain ⟨u', rfl⟩ := isUnit_of_isFrame ((isFrame_frm hE' n c').res h') (d'.isFrame.res k') hu'
  refine ⟨u' * u, eq_of_smul_eq d.isFrame k ?_⟩
  rw [← det_smul, hu', Scheme.Modules.Hom.app_smul,
    powHom_app_frm hE hE' ψ n c c' h h' (det_smul c.isFrame h fun i => ψ.app V (resM E' h' (c'.e i))) 0 0,
    hu, smul_smul, smul_smul, Units.val_mul, mul_right_comm]

end Scheme

section Model

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB (IsVB IsFrame Chart det)
open GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.CechPic
open GlobalTheory.Vert.Model (GenIso FlagPair)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O}
  {E E' : B.X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E)

theorem cls_div_powHom [IsIso (B.genRes.map ψ)] (n : ℕ) :
    haveI := isIso_pullback_powHom B.gen.ι hE hE' ψ n
    ((GenIso.ofHom (powHom hE hE' ψ n)).div (isVB_powMod hE n) (isVB_powMod hE' n)).cls =
      n • ((GenIso.ofHom ψ).div hE hE').cls := by
  induction n with
  | zero =>
    have := isIso_powHom_zero hE hE' ψ
    rw [zero_smul]
    exact GenIso.cls_div_of_isIso _ _ (ψ := powHom hE hE' ψ 0) rfl
  | succ n ih =>
    rw [succ_nsmul, ← ih]
    refine VertDiv.IsSum.cls_eq fun i j k => ?_
    obtain ⟨d, d'⟩ := i
    obtain ⟨c, c'⟩ := j
    obtain ⟨e, e'⟩ := k
    have h₁ : d.U ⊓ d'.U ⊓ (c.U ⊓ c'.U) ⊓ (e.U ⊓ e'.U) ≤ d.U ⊓ d'.U := inf_le_left.trans inf_le_left
    have h₂ : d.U ⊓ d'.U ⊓ (c.U ⊓ c'.U) ⊓ (e.U ⊓ e'.U) ≤ c.U ⊓ c'.U := inf_le_left.trans inf_le_right
    have h₃ : d.U ⊓ d'.U ⊓ (c.U ⊓ c'.U) ⊓ (e.U ⊓ e'.U) ≤ e.U ⊓ e'.U := inf_le_right
    obtain ⟨u, hu⟩ := exists_det_powHom hE hE' ψ n c c' d d' (h₂.trans inf_le_left)
      (h₂.trans inf_le_right) (h₁.trans inf_le_left) (h₁.trans inf_le_right)
    obtain ⟨v, hv⟩ := exists_det_powHom hE hE' ψ (n + 1) c c' e e' (h₂.trans inf_le_left)
      (h₂.trans inf_le_right) (h₃.trans inf_le_left) (h₃.trans inf_le_right)
    refine ⟨v * u⁻¹, (GenIso.eqn_div_of_hom _ _ (ψ := powHom hE hE' ψ (n + 1)) rfl e e' le_rfl h₃).trans
      (Eq.trans ?_ (congrArg _ (congrArg₂ (· * ·)
        (GenIso.eqn_div_of_hom _ _ (ψ := powHom hE hE' ψ n) rfl d d' le_rfl h₁)
        (GenIso.eqn_div_of_hom _ _ (ψ := ψ) rfl c c' le_rfl h₂))).symm)⟩
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg _ (map_mul _ _ _)))
    refine congrArg _ ?_
    rw [hu, hv, pow_succ]
    exact (show ∀ {R : Type} [CommRing R] (s t : Rˣ) (a b : R), s.val * (a * b) = (s * t⁻¹).val * (t * a * b)
      from fun s t a b => by
        rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left]) _ _ _ _

theorem cls_div_ofRankOne (φ : B.GenIso E E') :
    ((FlagPair.ofRankOne φ hE hE').div 0).cls = (φ.div hE hE').cls := by
  refine GenIso.cls_div_eq_of_iso O B _ _ _ _ 1 _ _ hE hE' _ φ (Flag.grOfRankOne hE)
    (Flag.grOfRankOne hE') ?_
  have h := (FlagPair.ofRankOne φ hE hE').π_grIso_hom 0
  have hπ' {L : B.X.Modules} (hL : IsVB L 1) :
      (Flag.ofRankOne hL).π 0 = (Flag.grOfRankOne hL).inv := cokernelZeroIsoTarget_inv.symm
  have h' : B.genRes.map (Flag.grOfRankOne hE).inv ≫ ((FlagPair.ofRankOne φ hE hE').grIso 0).hom =
      φ.hom ≫ B.genRes.map (Flag.grOfRankOne hE').inv := by
    rw [← hπ', ← hπ']
    exact h
  exact (B.genRes.mapIso (Flag.grOfRankOne hE')).eq_comp_inv.1
    (((B.genRes.mapIso (Flag.grOfRankOne hE)).inv_comp_eq.1 h').trans (Category.assoc _ _ _).symm)

theorem c1_isLB_root_powMod_eq_nsmul {X : Scheme.{0}} {L : X.Modules} (hL : IsVB L 1) (n : ℕ) :
    c1 _ ((Flag.ofRankOne (isVB_powMod hL n)).isLB_root 0) =
      (n : ℚ) • c1 _ ((Flag.ofRankOne hL).isLB_root 0) := by
  have h {M : X.Modules} (hM : IsVB M 1) : c1 _ ((Flag.ofRankOne hM).isLB_root 0) = c1 _ hM.isLB_det :=
    firstChernCongr _ _ (((Flag.ofRankOne hM).isVB_gr 0).lbIso_det_of_iso (Flag.grOfRankOne hM))
  rw [h, h]
  refine (firstChernCongr (GlobalTheory.AbLaw.isLB_pw hL.isLB_det n) _
    (GlobalTheory.VB.lbIso_det_toMod (GlobalTheory.AbLaw.isLB_pw hL.isLB_det n))).symm.trans ?_
  rw [← firstChernPic_class, ← firstChernPic_class,
    GlobalTheory.AmpleStabFinite.cls_pw, natCast_zsmul, map_nsmul, Nat.cast_smul_eq_nsmul]

open GlobalTheory.MixedLocalChains.FrobQuot in

theorem isFrob_cokernel_powHom (p : ℕ) [Fact p.Prime] [IsIso (B.genRes.map ψ)] {g : Γ(B.X, ⊤)}
    (hg : IsRootOfP p g p) (hk : Kills g (cokernel ψ)) :
    IsFrob p (cokernel ψ) (cokernel (powHom hE hE' ψ p)) := by
  have hp := natCast_eq_zero_fibI p B
  refine ⟨hp, ?_⟩
  have : Mono ψ := Pres.mono_ψ O B ⟨1, E, E', hE, hE', ψ, inferInstance⟩
  have := (isVB_powMod hE p).isQuasicoherent
  have := (isVB_powMod hE' p).isQuasicoherent
  have hC := smulHom_cokernel_powHom hE hE' ψ hk p
  have hCp : smulHom (cokernel (powHom hE hE' ψ p)) (p : Γ(B.X, ⊤)) = 0 := by
    obtain ⟨u, hu⟩ := hg
    rw [← u.inv_mul_cancel_left (p : Γ(B.X, ⊤)), ← hu, smulHom_mul, hC, zero_comp]
  have hI := isIso_unit_fibI p B (cokernel (powHom hE hE' ψ p)) hCp
  obtain ⟨e⟩ := nonempty_iso_pullback_cokernel (f := (fibI p B).subschemeι) (n := p)
    (g := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι) (fun _ => le_rfl)
    (fun U T h a => by
      rw [← Scheme.Hom.appLE_comp_appLE (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp)
        (fibI p B).subschemeι U T T h le_rfl, CommRingCat.comp_apply]
      exact (GlobalTheory.SS.FrobField.absFrob_appLE _ p 1 Fact.out hp T le_rfl _).trans (by rw [pow_one]))
    hE hE' ψ
  exact ⟨@asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction (fibI p B).subschemeι).unit.app
      (cokernel (powHom hE hE' ψ p))) hI ≪≫ (Scheme.Modules.pushforward (fibI p B).subschemeι).mapIso e⟩

end Model

end GlobalTheory.LinePow

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

open GlobalTheory.LinePow in

theorem GlobalTheory.LinePow.exists_frob_presentation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (hE : GlobalTheory.VB.IsVB E 1) (hE' : GlobalTheory.VB.IsVB E' 1) (ψ : E' ⟶ E) [IsIso (B.genRes.map ψ)] (g : Γ(B.X, ⊤)), IsRootOfP p g p → Kills g (cokernel ψ) → ∃ (F F' : B.X.Modules) (hF : GlobalTheory.VB.IsVB F 1) (hF' : GlobalTheory.VB.IsVB F' 1) (χ : F' ⟶ F) (_ : IsIso (B.genRes.map χ)), IsFrob p (cokernel ψ) (cokernel χ) ∧ (B.toITh p).c1 (((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom χ) hF hF').toFPair p).x 0) = (p : ℚ) • (B.toITh p).c1 (((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom ψ) hE hE').toFPair p).x 0) ∧ (B.toITh p).c1 (((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom χ) hF hF').toFPair p).x' 0) = (p : ℚ) • (B.toITh p).c1 (((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom ψ) hE hE').toFPair p).x' 0) ∧ ((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom χ) hF hF').toFPair p).Dv 0 = (p : ℚ) • ((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom ψ) hE hE').toFPair p).Dv 0 := by
  intro O _ _ _ p _ _ _ B _ E E' hE hE' ψ _ g hg hk
  refine ⟨powMod E p, powMod E' p, isVB_powMod hE p, isVB_powMod hE' p, powHom hE hE' ψ p,
    isIso_pullback_powHom B.gen.ι hE hE' ψ p, isFrob_cokernel_powHom hE hE' ψ p hg hk,
    c1_isLB_root_powMod_eq_nsmul hE p, c1_isLB_root_powMod_eq_nsmul hE' p, ?_⟩
  change GlobalTheory.Vert.Model.toQ _ = (p : ℚ) • GlobalTheory.Vert.Model.toQ _
  rw [cls_div_ofRankOne, cls_div_ofRankOne, cls_div_powHom, map_nsmul, Nat.cast_smul_eq_nsmul]
