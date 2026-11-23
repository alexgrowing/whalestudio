import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingDualSymplectic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeAffineBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeSubbundleCorrespondentExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationDeRhamFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationDeRhamSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationHodgeSubSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEpiVectorBundleSameRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeSubbundleExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplOfIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamRingActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeInclusionEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPairingEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianExtensionOverNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianAbelianNearGenericPointStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CechPic
open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.PrincipalPolPairing
open GlobalTheory.QCoh (appLinear)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum

variable {O : Type} [CommRing O] {T : Scheme.{0}} {A : Over T} [GrpObj A] {g : ℕ} {H : T.Modules}
  {e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)}

section Transport

variable {X : Scheme.{0}} {W L L' W' W₁ L₁ L₁' W₁' D : X.Modules}

theorem shortExact_congr (ι : W₁ ≅ W) (κ : L ≅ L₁) {a : W ⟶ D} {b : D ⟶ L} {w : a ≫ b = 0}
    (s : (ShortComplex.mk a b w).ShortExact) (w' : (ι.hom ≫ a) ≫ b ≫ κ.hom = 0) :
    (ShortComplex.mk (ι.hom ≫ a) (b ≫ κ.hom) w').ShortExact :=
  ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk a b w)
    (ShortComplex.isoMk ι.symm (Iso.refl _) κ (by simp) (by simp)) s

theorem isEquivariant_comp {α : O →+* End W} {β : O →+* End D} {γ : O →+* End L} {a : W ⟶ D} {b : D ⟶ L}
    (h : IsEquivariant α β a) (h' : IsEquivariant β γ b) : IsEquivariant α γ (a ≫ b) := fun x ↦ by
  rw [← Category.assoc, h x, Category.assoc, h' x, Category.assoc]

def transport {α : O →+* End W} {β : O →+* End L} {α' : O →+* End L'} {β' : O →+* End W'} {α₁ : O →+* End W₁}
    {β₁ : O →+* End L₁} {α₁' : O →+* End L₁'} {β₁' : O →+* End W₁'} {r : ℕ} (d : TwoSeq.Datum α β α' β' r)
    (ι : W₁ ≅ W) (κ : L₁ ≅ L) (ι' : L₁' ≅ L') (κ' : W₁' ≅ W') (h₁ : IsEquivariant α₁ α ι.hom)
    (h₂ : IsEquivariant β₁ β κ.hom) (h₃ : IsEquivariant α₁' α' ι'.hom) (h₄ : IsEquivariant β₁' β' κ'.hom) :
    TwoSeq.Datum α₁ β₁ α₁' β₁' r where
  D := d.D
  ρ := d.ρ
  a := ι.hom ≫ d.a
  b := d.b ≫ κ.inv
  u := ι'.hom ≫ d.u
  v := d.v ≫ κ'.inv
  w₁ := by rw [Category.assoc, reassoc_of% d.w₁, zero_comp, comp_zero]
  w₂ := by rw [Category.assoc, reassoc_of% d.w₂, zero_comp, comp_zero]
  isVB := d.isVB
  exact₁ := shortExact_congr ι κ.symm d.exact₁ _
  exact₂ := shortExact_congr ι' κ'.symm d.exact₂ _
  equiv_a := isEquivariant_comp h₁ d.equiv_a
  equiv_b := isEquivariant_comp d.equiv_b (isEquivariant_inv h₂)
  equiv_u := isEquivariant_comp h₃ d.equiv_u
  equiv_v := isEquivariant_comp d.equiv_v (isEquivariant_inv h₄)

end Transport

section Pairing

variable {P : LB (A ⊗ A).left}

theorem isPerfect_of_symm (hd : IsDual A A P) (hs : LBIso (swap P) P) : IsPerfect A A P := by
  have hP := hd.isLB
  have hs' : (swap P).IsLB := pull_isLB hP _
  have sym {Y : Over T} (x y : Y ⟶ A) : evc hP x y = evc hP y x := by
    rw [← evc_swap hP hs', evc, (cls_eq_iff hs' hP).2 hs, evc]
  refine ⟨hP, (triv_ev_iff hP _ _).2 (hd.additive.evc_one hP _), hd.zero, fun Y x hx ↦ hd.eq_one x ?_,
    fun _ ↦ hd.eq_one⟩
  have k := congrArg (CechPic.pull (lift (snd A Y) (fst A Y)).left) ((triv_ev_iff hP _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at k
  rw [triv_ev_iff hP, sym, k]

omit [GrpObj A] in

theorem sqMap_comp {S₁ S₂ : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {b : S₂ ⟶ S₁} {π : A₂.left ⟶ A₁.left}
    (w : π ≫ A₁.hom = A₂.hom ≫ b) {f₁ : A₁.left ⟶ A.left} {f₂ : A₂.left ⟶ A.left} (eπ : π ≫ f₁ = f₂)
    {m : (A₁ ⊗ A₁).left ⟶ (A ⊗ A).left} {m' : (A₂ ⊗ A₂).left ⟶ (A ⊗ A).left}
    (m₁ : m ≫ (fst A A).left = (fst A₁ A₁).left ≫ f₁) (m₂ : m ≫ (snd A A).left = (snd A₁ A₁).left ≫ f₁)
    (m₁' : m' ≫ (fst A A).left = (fst A₂ A₂).left ≫ f₂) (m₂' : m' ≫ (snd A A).left = (snd A₂ A₂).left ≫ f₂) :
    m' = sqMap w ≫ m := by
  have e₁ : sqMap w ≫ (fst A₁ A₁).left = (fst A₂ A₂).left ≫ π := pullback.lift_fst _ _ _
  have e₂ : sqMap w ≫ (snd A₁ A₁).left = (snd A₂ A₂).left ≫ π := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · change m' ≫ (fst A A).left = (sqMap w ≫ m) ≫ (fst A A).left
    rw [Category.assoc, m₁, m₁', ← Category.assoc, e₁, Category.assoc, eπ]
  · change m' ≫ (snd A A).left = (sqMap w ≫ m) ≫ (snd A A).left
    rw [Category.assoc, m₂, m₂', ← Category.assoc, e₂, Category.assoc, eπ]

set_option maxHeartbeats 800000 in

theorem exists_isPolPairing (hD : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hP : IsPerfect A A P) (he : IsDRIso A H e) : ∃ β : H ⟶ dual H, IsPolPairing e P β := by
  have hπ (V : T.Opens) (hV : IsAffineOpen V) :
      IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) := isGrpPullback_pullback A _
  have hAV := fun (V : T.Opens) (hV : IsAffineOpen V) ↦ DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hgV := fun (V : T.Opens) (hV : IsAffineOpen V) ↦ DeRhamSheaf.VB.smooth_onAff A hg hV
  choose m m₁ m₂ using fun (V : T.Opens) (hV : IsAffineOpen V) ↦ exists_prod_pullback (hπ V hV) (hπ V hV)
  have hL (V : T.Opens) (hV : IsAffineOpen V) := pull_isLB hP.isLB (m V hV)
  have hPV (V : T.Opens) (hV : IsAffineOpen V) : IsPerfect (onAff A hV) (onAff A hV) (P.pull (m V hV)) :=
    hP.baseChange (hπ V hV) (hπ V hV) (m₁ V hV) (m₂ V hV) (hL V hV) ((cls_eq_iff (hL V hV) (hL V hV)).1 rfl)
  choose φ hφ using fun (V : T.Opens) (hV : IsAffineOpen V) ↦ exists_isCorrForm
    (cupSquare_of_free hD.1 (AbelianSchemeGerms.isAbelianScheme_tensor _ _ (hAV V hV) (hAV V hV))
      (smooth_prod (hgV V hV) (hgV V hV))) (hL V hV) (hPV V hV).zero_left (hPV V hV).zero_right
  have pφ (V : T.Opens) (hV : IsAffineOpen V) : (φ V hV).IsPerfPair :=
    ((hφ V hV).perfect hD (hAV V hV) (hgV V hV) (hAV V hV) (hgV V hV) (hPV V hV)).1
  choose b pb k using fun (V : T.Opens) (hV : IsAffineOpen V) ↦ by
    obtain ⟨_, _, -⟩ := Free.prim hD.1 (hAV V hV) (hgV V hV)
    exact exists_inverse (φ V hV) (pφ V hV)
  have hb : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
      (b V' hV').compl₁₂ (e V' hV').toLinearMap (e V' hV').toLinearMap (Twist.resM H h s) (Twist.resM H h t) =
        resG T h ((b V hV).compl₁₂ (e V hV).toLinearMap (e V hV).toLinearMap s t) := by
    intro V V' hV hV' h s t
    letI := resAlg h
    obtain ⟨π, hπ', eπ⟩ := DeRhamSheaf.VB.exists_transition A hV hV' h
    obtain ⟨_, _, -⟩ := Free.prim hD.1 (hAV V hV) (hgV V hV)
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [he V V' hV hV' h π hπ' eπ, he V V' hV hV' h π hπ' eπ]
    refine inverse_bc (hD.2.2.1 _ _ g (hAV V hV) (hgV V hV) _ _ π hπ').1 (pφ V' hV') (corr_bc hD.1
      (hAV V' hV') (hgV V' hV') hπ' (hL V hV) (hL V' hV') ?_ (hφ V hV) (hφ V' hV')) (k V hV) (k V' hV') _ _
    exact (congrArg (fun z ↦ CechPic.pull z (cls P hP.isLB))
      (sqMap_comp hπ'.1.w eπ (m₁ V hV) (m₂ V hV) (m₁ V' hV') (m₂ V' hV'))).trans (CechPic.pull_comp _ _ _)
  refine ⟨AffinePairingGlue.toDual _ hb, fun V hV ↦ ⟨m V hV, φ V hV, m₁ V hV, m₂ V hV, hφ V hV, pφ V hV, ?_⟩⟩
  intro s x y hx
  have ex : x = b V hV (e V hV s) := LinearMap.ext fun w ↦ by
    obtain ⟨w, rfl⟩ := (e V hV).surjective w
    rw [hx, AffinePairingGlue.dualApp_toDual_affine _ hb hV]
    rfl
  rw [ex, k]

def formOn (β : H ⟶ dual H) (V : T.Opens) : Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V) :=
  Lagr.evU H V ∘ₗ appLinear β V

theorem formOn_apply (β : H ⟶ dual H) (V : T.Opens) (s t : Γ(H, V)) :
    formOn β V s t = dualApp (β.app V s) le_rfl t := rfl

variable {β : H ⟶ dual H}

theorem IsPolPairing.perfect (hD : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hβ : IsPolPairing e P β) {V : T.Opens} (hV : IsAffineOpen V) : (formOn β V).IsPerfPair := by
  obtain ⟨m, φ, -, -, -, pφ, k⟩ := hβ V hV
  obtain ⟨_, _, -⟩ := Free.prim hD.1 (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV)
    (DeRhamSheaf.VB.smooth_onAff A hg hV)
  obtain ⟨b, pb, kb⟩ := exists_inverse φ pφ
  have ex (s : Γ(H, V)) : formOn β V s ∘ₗ (e V hV).symm.toLinearMap = b (e V hV s) :=
    pφ.bijective_left.1 (LinearMap.ext fun y ↦ (k s _ y fun t ↦ by simp [formOn_apply]).trans (kb _ _).symm)
  refine LinearMap.IsPerfPair.congr b (e V hV) (e V hV) _ (LinearMap.ext₂ fun s t ↦ ?_)
  simpa using LinearMap.congr_fun (ex ((e V hV).symm s)) t

theorem IsPolPairing.isIso (hD : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hβ : IsPolPairing e P β) (hH : IsVB H (2 * g)) : IsIso β := by
  have hb : ∀ (V V' : T.Opens) (_ : IsAffineOpen V) (_ : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
      formOn β V' (Twist.resM H h s) (Twist.resM H h t) = resG T h (formOn β V s t) := fun V V' _ _ h s t ↦ by
    rw [formOn_apply, formOn_apply, Twist.app_resM, dualApp_res, dualApp_resM]
  have e₁ : β = AffinePairingGlue.toDual (fun V _ ↦ formOn β V) hb := hom_dual_ext_affine fun V hV s t ↦
    (AffinePairingGlue.dualApp_toDual_affine _ hb hV s t).symm
  rw [e₁]
  exact AffinePairingGlue.isIso_toDual _ hb hH fun V hV ↦ hβ.perfect hD hA hg hV

theorem IsPolPairing.isotropic (hD : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hd : IsDual A A P) (hβ : IsPolPairing e P β) {V : T.Opens} (hV : IsAffineOpen V)
    (S : Submodule Γ(T, V) (primDR (onAff A hV))) (hS : ∃ S', IsCompl S S')
    (hrk : ∀ Q : PrimeSpectrum Γ(T, V), Module.rankAtStalk S Q = g)
    (hiso : ∀ (Q : LB (onAff A hV ⊗ onAff A hV).left), IsDual (onAff A hV) (onAff A hV) Q →
      ∀ φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V),
        IsCorrForm (dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) Q φ →
        ∀ x y : HdR (onAff A hV), (∀ c ∈ S, x c = 0) → (∀ c ∈ S, y c = 0) → φ x y = 0)
    {s t : Γ(H, V)} (hs : e V hV s ∈ S) (ht : e V hV t ∈ S) : dualApp (β.app V s) le_rfl t = 0 := by
  have hp := hβ.perfect hD hA hg hV
  obtain ⟨m, φ, m₁, m₂, hφ, -, k⟩ := hβ V hV
  obtain ⟨h₁, h₂, h₃⟩ := Free.prim hD.1 (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV)
    (DeRhamSheaf.VB.smooth_onAff A hg hV)
  have hπ : IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) := isGrpPullback_pullback A _
  have hL := pull_isLB hd.isLB m
  exact AnnIso.pairing_vanishes_of_annihilator_isotropic _ _ _ (e V hV) g h₁ h₂ h₃ (formOn β V).flip inferInstance φ
    (fun x y u v hx hy ↦ (k u x y hx).trans (hy u)) S hS hrk
    (hiso _ (hd.baseChange hπ hπ m₁ m₂ hL ((cls_eq_iff hL hL).1 rfl)) φ hφ) t s ht hs

end Pairing

section Hodge

theorem exists_isHodgeIncl (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (he : IsDRIso A H e) : ∃ a : omega A ⟶ H, IsHodgeIncl e a := by
  choose c hcF hc using HodgeSubExists.main hP T A g hA hg
  have uniq := HodgeSub.corr_unique hP T A g hA hg
  let j : ∀ V : T.Opens, ∀ hV : IsAffineOpen V, Γ(IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V) →ₗ[Γ(T, V)] primDR (onAff A hV) :=
    fun V hV ↦
      { toFun := c V hV
        map_add' := fun s s' ↦ uniq V hV _ _ _ (hc V hV (s + s'))
          (HodgeSub.corr_add_smul A V hV s s' _ _ 1 (hc V hV s) (hc V hV s')).1
        map_smul' := fun r s ↦ uniq V hV _ _ _ (hc V hV (r • s))
          (HodgeSub.corr_add_smul A V hV s s _ _ r (hc V hV s) (hc V hV s)).2 }
  obtain ⟨a, ha⟩ := hom_of_affine_compatible T _ H (fun V hV ↦ (e V hV).symm.toLinearMap ∘ₗ j V hV) (by
    intro V V' hV hV' h s
    letI := resAlg h
    obtain ⟨φ, hφ, hfst⟩ := HodgeSub.exists_proj A V V' hV hV' h
    apply (e V' hV').injective
    change e V' hV' ((e V' hV').symm (c V' hV' _)) = _
    rw [LinearEquiv.apply_symm_apply, he V V' hV hV' h φ hφ hfst]
    change _ = (bcMor hφ).pull (e V hV ((e V hV).symm (c V hV s)))
    rw [LinearEquiv.apply_symm_apply]
    exact uniq V' hV' _ _ _ (hc V' hV' _)
      (HodgeSub.Nat.corr_res hP T A g hA hg V V' hV hV' h φ hφ hfst s _ (hc V hV s)))
  refine ⟨a, fun V hV s ↦ ?_⟩
  have k : e V hV (a.app V s) = c V hV s :=
    (congrArg (e V hV) (LinearMap.congr_fun (ha V hV) s)).trans ((e V hV).apply_symm_apply _)
  exact k.symm ▸ ⟨hcF V hV s, hc V hV s⟩

theorem exists_isCompl_range {R M N L : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup L] [Module R L] (ε : M ≃ₗ[R] N) (f : L →ₗ[R] M) (W : Submodule R N)
    (h : ∀ s, s ∈ LinearMap.range f ↔ ε s ∈ W) (hW : ∃ W', IsCompl W W') :
    ∃ N', IsCompl (LinearMap.range f) N' := by
  obtain ⟨W', hW'⟩ := hW
  have hr : LinearMap.range f = W.comap ε.toLinearMap := Submodule.ext h
  refine ⟨W'.comap ε.toLinearMap, ?_⟩
  rw [hr]
  have := (OrderIso.isCompl_iff (f := (Submodule.orderIsoMapComap ε.symm))).1 hW'
  simpa [Submodule.map_equiv_eq_comap_symm] using this

theorem IsHodgeIncl.split (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {a : omega A ⟶ H} (ha : IsHodgeIncl e a) (V : T.Opens) (hV : IsAffineOpen V) :
    Function.Injective (appLinear a V) ∧ ∃ N, IsCompl (LinearMap.range (appLinear a V)) N := by
  refine ⟨fun s s' h ↦ ?_, exists_isCompl_range (e V hV) _ (PrimitiveSubmodule (onAff A hV)) (fun s ↦ ⟨?_, fun hs ↦ ?_⟩)
    (hP.p5.2.1 Γ(T, V) (onAff A hV) g (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV)
      (DeRhamSheaf.VB.smooth_onAff A hg hV)).2.1⟩
  · have h' : a.app V s = a.app V s' := h
    exact GlobalTheory.T.hodge_correspondence_unique_left hP T A g hA hg V hV s s' _ (ha V hV s).2 (h' ▸ (ha V hV s').2)
  · rintro ⟨t, rfl⟩
    exact (ha V hV t).1
  · obtain ⟨t, ht⟩ := HodgeSubSurj.main hP T A g hA hg V hV _ hs
    exact ⟨t, (e V hV).injective (HodgeSub.corr_unique hP T A g hA hg V hV t _ _ (ha V hV t).2 ht)⟩

theorem hodge_shortExact (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hd : IsDual A A P) (hH : IsVB H (2 * g)) {a : omega A ⟶ H} (ha : IsHodgeIncl e a)
    {β : H ⟶ dual H} (hβ : IsPolPairing e P β) :
    ∃ w : a ≫ β ≫ dualMap a = 0, (ShortComplex.mk a (β ≫ dualMap a) w).ShortExact := by
  have w : a ≫ β ≫ dualMap a = 0 := hom_dual_ext_affine fun V hV s t ↦ by
    have hAV := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
    have hgV := DeRhamSheaf.VB.smooth_onAff A hg hV
    obtain ⟨-, hc, -, -, hrk⟩ := hP.p5.2.1 Γ(T, V) (onAff A hV) g hAV hgV
    exact hβ.isotropic hP.p5 hA hg hd hV _ hc hrk (fun Q hQ φ hφ x y hx hy ↦
      PrincipalPolPairing.isotropic hP.p5 hAV hgV hQ.isLB hφ x ((Submodule.mem_dualAnnihilator _).2 hx) y
        ((Submodule.mem_dualAnnihilator _).2 hy)) (ha V hV s).1 (ha V hV t).1
  have := hA.proper
  have := hg
  exact ⟨w, lagrangian_shortExact T g _ H (isVB_omega A g) hH a β (hβ.isIso hP.p5 hA hg hH) (ha.split hP hA hg) w⟩

end Hodge

section Conj

variable (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0)

theorem exists_conj (hC : ConjugateFiltration) (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : LB (A ⊗ A).left} (hd : IsDual A A P) (he : IsDRIso A H e)
    {a : omega A ⟶ H} (ha : IsHodgeIncl e a) {β : H ⟶ dual H} (hβ : IsPolPairing e P β)
    {L : T.Modules} (hL : IsVB L g) {b : H ⟶ L} {w : a ≫ b = 0} (hs : (ShortComplex.mk a b w).ShortExact)
    {Ψ : (frobPull p h0).obj H ⟶ H} (hΨ : IsLinFrob e p h0 Ψ) :
    ∃ u : (frobPull p h0).obj L ⟶ H, (frobPull p h0).map b ≫ u = Ψ ∧
      ∃ w' : u ≫ β ≫ dualMap u = 0, (ShortComplex.mk u (β ≫ dualMap u) w').ShortExact := by
  letI : Algebra (ZMod p) Γ(T, ⊤) := ((Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom Γ(T, ⊤))
    (fun x hx ↦ by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      simp [h0])).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom).toAlgebra
  have hH := DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hP.p5 T A g hA hg H ⟨e, he⟩
  have hAV := fun (V : T.Opens) (hV : IsAffineOpen V) ↦ DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hgV := fun (V : T.Opens) (hV : IsAffineOpen V) ↦ DeRhamSheaf.VB.smooth_onAff A hg hV
  have hCV := fun (V : T.Opens) (hV : IsAffineOpen V) ↦
    hC p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV) g (hAV V hV) (hgV V hV)
      (ConjSeq.cast_left p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV))
      (ConjSeq.frobMor p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV)
        (ConjSeq.cast_left p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV)))
  obtain ⟨C, hCs⟩ := ConjSeq.ConjSub.exists_conjSub hP p A g hA hg H e he
  have hzC : Ψ ≫ cokernel.π C.incl = 0 := ConjSeq.frobLin_comp_cokernel_π_eq_zero p A g hA hg H e he C hCs Ψ hΨ
  haveI := C.mono_incl
  let Ψc : (frobPull p h0).obj H ⟶ C.toMod := Abelian.monoLift C.incl Ψ hzC
  have hΨc : Ψc ≫ C.incl = Ψ := Abelian.monoLift_comp _ _ _
  have hepi : Epi Ψc := ConjIso.epi_frobPull_conj p A g hA hg H e he C hCs Ψc (by rw [hΨc]; exact hΨ)
  have hz : (frobPull p h0).map a ≫ Ψ = 0 := frobPull_hom_ext_affine p h0 fun V hV s ↦ by
    refine (congrArg (Ψ.app V) (QCoh.pullback_map_app_pullbackSections (frob T p h0) _ _ _)).trans ?_
    apply (e V hV).injective
    exact (hΨ V hV _).trans (((hCV V hV).1 _ (ha V hV s).1).trans (map_zero (e V hV)).symm)
  have hz' : (frobPull p h0).map a ≫ Ψc = 0 := by
    rw [← cancel_mono C.incl, Category.assoc, hΨc, hz, zero_comp]
  have hco : IsColimit (CokernelCofork.ofπ ((frobPull p h0).map b)
      (show (frobPull p h0).map a ≫ (frobPull p h0).map b = 0 by rw [← Functor.map_comp, w, Functor.map_zero])) :=
    isColimitCoforkMapOfIsColimit' (frobPull p h0) w hs.gIsCokernel
  obtain ⟨π, hπ⟩ := CokernelCofork.IsColimit.desc' hco Ψc hz'
  have hπ' : (frobPull p h0).map b ≫ π = Ψc := hπ
  have : Epi π := epi_of_epi_fac hπ'
  have : IsIso π := isIso_of_epi_of_isVB π g (hL.frobPull p h0) (ConjSeq.isVB_conj hC hP p A g hA hg H e he C hCs)
  have hmem (V : T.Opens) (s : Γ(H, V)) : s ∈ LinearMap.range (appLinear (π ≫ C.incl) V) ↔ s ∈ C.sec V := by
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨t, rfl⟩
      exact C.incl_app_mem _
    · obtain ⟨t, rfl⟩ := C.mem_sec_iff.1 h
      exact ⟨(inv π).app V t, congr(($(IsIso.inv_hom_id_assoc π C.incl)).app V t)⟩
  have w' : (π ≫ C.incl) ≫ β ≫ dualMap (π ≫ C.incl) = 0 := hom_dual_ext_affine fun V hV s t ↦ by
    obtain ⟨-, hc, hrk, hd'⟩ := hCV V hV
    exact hβ.isotropic hP.p5 hA hg hd hV _ hc hrk (fun Q hQ φ hφ x y hx hy ↦
      hd' (onAff A hV) (hAV V hV) (hgV V hV) _ _ Q hQ φ hφ x y (fun c ↦ hx _ (Submodule.subset_span ⟨c, rfl⟩))
        fun c ↦ hy _ (Submodule.subset_span ⟨c, rfl⟩)) ((hCs V hV _).1 (C.incl_app_mem _))
      ((hCs V hV _).1 (C.incl_app_mem _))
  refine ⟨π ≫ C.incl, by rw [← Category.assoc, hπ', hΨc], w', lagrangian_shortExact T g _ H (hL.frobPull p h0) hH _ β
    (hβ.isIso hP.p5 hA hg hH) (fun V hV ↦ ⟨QCoh.injective_app_of_mono _ V,
      exists_isCompl_range (e V hV) _ _ (fun s ↦ (hmem V s).trans (hCs V hV s)) (hCV V hV).2.1⟩) w'⟩

end Conj

section Datum

variable {c : O →+* O} {i : OAct O A} {P : LB (A ⊗ A).left}

theorem IsSelfDual.act_conj_conj (h : IsSelfDual c i P) (x : O) : i.act (c (c x)) = i.act x := by
  obtain ⟨hd, hs, hr⟩ := h
  have hP := hd.isLB
  have hs' : (swap P).IsLB := pull_isLB hP _
  have sym {Y : Over T} (x y : Y ⟶ A) : evc hP x y = evc hP y x := by
    rw [← evc_swap hP hs', evc, (cls_eq_iff hs' hP).2 hs, evc]
  have ros (z : O) {Y : Over T} (x y : Y ⟶ A) : evc hP (x ≫ i.act z) y = evc hP x (y ≫ i.act (c z)) := by
    have k := congrArg (CechPic.pull (lift x y).left) ((cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hr z))
    rw [cls_ev hP, cls_ev hP, pull_evc, pull_evc] at k
    simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using k
  refine BirigidLift.dual_ext hd ?_
  rw [← ros, sym, ← ros, sym]

variable (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0)

theorem exists_datum [QuasiSeparated A.hom] (hC : ConjugateFiltration) (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (h : IsSelfDual c i P) :
    ∃ d : TwoSeq.Datum (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob T p h0))
      (pullAct (omegaAct i) (frob T p h0)) (2 * g), IsDRDatum p h0 i P d.ρ d.a d.b d.u d.v := by
  letI : Algebra (ZMod p) Γ(T, ⊤) := ((Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom Γ(T, ⊤))
    (fun x hx ↦ by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      simp [h0])).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom).toAlgebra
  obtain ⟨H, hH₀⟩ := exists_isDeRhamSheaf hP.p5 T A g hA hg
  have hH := DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hP.p5 T A g hA hg H hH₀
  obtain ⟨e, he⟩ := (isDeRhamSheaf_iff A H).1 hH₀
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_de_rham_ring_action O T A hA i H e he
  obtain ⟨a, ha⟩ := exists_isHodgeIncl hP hA hg he
  obtain ⟨β, hβ⟩ := exists_isPolPairing hP.p5 hA hg (isPerfect_of_symm h.1 h.2.1) he
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, IsLinFrob e p h0 Ψ := LinFrob.exists_linFrob hP p A g hA hg H e he
  obtain ⟨w₁, s₁⟩ := hodge_shortExact hP hA hg h.1 hH ha hβ
  have := hg
  have hω := isVB_omega A g
  obtain ⟨u, hu, w₂, s₂⟩ := exists_conj p h0 hC hP hA hg h.1 he ha hβ hω.dual s₁ hΨ
  have := hω.isIso_toBidual_of_local_frames
  have := DualPull.isIso_theta (frob T p h0) hω.dual
  let θ := (frobPull p h0).map (cartierDualToBidual (omega A)) ≫ DualPull.theta (frob T p h0) (Lie A)
  have ea : IsEquivariant (omegaAct i) ρ a := GlobalTheory.T.hodge_inclusion_equivariant hP O T A g hA hg i H e ρ a hρ ha
  have eβ := GlobalTheory.T.polarization_pairing_equivariant hP O c T A g hA hg i P h H e ρ β hρ hβ
  have eΨ := GlobalTheory.T.frobenius_equivariant_de_rham O T A i H e p h0 ρ Ψ hρ hΨ
  have eb : IsEquivariant ρ ((lieAct i).comp c) (β ≫ dualMap a) := fun x ↦ by
    rw [← Category.assoc, eβ, Category.assoc, Category.assoc, ← dualMap_comp, ← ea (c x), dualMap_comp]
    rfl
  have := s₁.epi_g
  have eu : IsEquivariant (pullAct ((lieAct i).comp c) (frob T p h0)) ρ u := fun x ↦ by
    rw [← cancel_epi ((frobPull p h0).map (β ≫ dualMap a)), ← Category.assoc, ← eb.pullback (frob T p h0) x,
      Category.assoc, ← Category.assoc _ u, hu, eΨ x]
  have eθ (x : O) : act (pullAct (omegaAct i) (frob T p h0)) x ≫ θ =
      θ ≫ dualMap (act (pullAct ((lieAct i).comp c) (frob T p h0)) (c x)) := by
    have k : act ((lieAct i).comp c) (c x) = dualMap (act (omegaAct i) x) :=
      congrArg dualMap (@omegaMap_congr _ _ _ _ _ _ _ (i.hom _) (i.hom _) (h.act_conj_conj x))
    rw [act_pullAct, act_pullAct, k, ← Category.assoc, ← Functor.map_comp, toBidual_naturality_dualSheafTranspose, Functor.map_comp,
      Category.assoc, Category.assoc, DualPull.theta_naturality]
  have ev : IsEquivariant ρ (pullAct (omegaAct i) (frob T p h0)) ((β ≫ dualMap u) ≫ inv θ) := fun x ↦ by
    rw [← cancel_mono θ, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc, eθ,
      Category.assoc, IsIso.inv_hom_id_assoc, ← Category.assoc, eβ, Category.assoc, Category.assoc, ← dualMap_comp,
      ← eu (c x), dualMap_comp]
  have w₂' : u ≫ (β ≫ dualMap u) ≫ inv θ = 0 := by rw [← Category.assoc, w₂, zero_comp]
  have s₂' : (ShortComplex.mk u ((β ≫ dualMap u) ≫ inv θ) w₂').ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk u (β ≫ dualMap u) w₂)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso θ).symm (by simp) (by simp)) s₂
  exact ⟨⟨H, ρ, a, _, u, _, w₁, w₂', hH, s₁, s₂', ea, eb, eu, ev⟩, e, β, Ψ, he, hρ, ha, hβ, hΨ, rfl, hu,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (IsIso.inv_hom_id θ)).trans (Category.comp_id _))⟩

end Datum

section On

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) {f : T ⟶ C} {φ : A.left ⟶ G.left}

theorem exists_datumOn (hC : ConjugateFiltration) (hP : CovTop.Hypotheses2) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {j : OAct O A} (h : CurveRootGeometry.IsActPull j i f φ) {P : LB (A ⊗ A).left}
    (hs : IsSelfDual c j P) (hω : IsVB (omega G) g) :
    ∃ d : TwoSeq.DieuDatumOn q k c i g f, IsDRDatumOn q k c i j h.1 P hω d := by
  have := hA.proper
  obtain ⟨d, hd⟩ := exists_datum q (cast_eq_zero q k f) hC hP hA hg hs
  have e₁ : IsEquivariant (pullAct (omegaAct i) f) (omegaAct j) (omegaRes h.1).hom := isEquivariant_omegaBase h.1 h.2
  have e₂ : IsEquivariant (pullAct ((lieAct i).comp c) f) ((lieAct j).comp c) (lieRes h.1 hω).hom :=
    fun x ↦ isEquivariant_lieBase h.1 h.2 (c x)
  have e₀ {M : C.Modules} (α : O →+* End M) : IsEquivariant (pullAct (pullAct α (frob C q (natCast_eq_zero C q k))) f)
      (pullAct (pullAct α f) (frob T q (cast_eq_zero q k f)))
      ((frobPullPullbackIso q (natCast_eq_zero C q k) f (cast_eq_zero q k f)).app M).hom :=
    fun x ↦ (frobPullPullbackIso q (natCast_eq_zero C q k) f (cast_eq_zero q k f)).hom.naturality (act α x)
  refine ⟨transport d (omegaRes h.1) (lieRes h.1 hω)
    (frobLieRes h.1 q (natCast_eq_zero C q k) (cast_eq_zero q k f) hω)
    (frobOmegaRes h.1 q (natCast_eq_zero C q k) (cast_eq_zero q k f)) e₁ e₂
    (isEquivariant_comp (e₀ _) (e₂.pullback _)) (isEquivariant_comp (e₀ _) (e₁.pullback _)), ?_⟩
  unfold IsDRDatumOn
  simpa only [transport, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd

end On

theorem exists_datumOn_open (hD : DualAbelianScheme) (hC : ConjugateFiltration) (hP : CovTop.Hypotheses2) (c : O →+* O)
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
    (hc : IsSmoothProjCurve k C) {G : Over C} [GrpObj G] [hG : IsSemiAbelian G] (i : OAct O G)
    (Q : Out.PolAV (Sp C.functionField)) (j₀ : OAct O Q.A) (φ₀ : Q.A.left ⟶ G.left)
    (h₀ : CurveRootGeometry.IsActPull j₀ i (CurveRootGeometry.genPt C) φ₀) (hr : CurveRootGeometry.IsRosati c Q j₀) {U : C.Opens} (hU : genericPoint C ∈ U)
    {A : Over U.toScheme} [GrpObj A] (hA : IsAbelianScheme A) {j : OAct O A} {φ : A.left ⟶ G.left}
    (h : CurveRootGeometry.IsActPull j i U.ι φ) :
    ∃ (P : LB (A ⊗ A).left) (g : ℕ) (hg : IsVB (omega G) g) (d : TwoSeq.DieuDatumOn q k c i g U.ι),
      IsSelfDual c j P ∧ IsDRDatumOn q k c i j h.1 P hg d ∧
      ∀ (ψ : Q.A.left ⟶ A.left) (m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left), ψ ≫ φ = φ₀ →
        m ≫ (fst A A).left = (fst Q.A Q.A).left ≫ ψ → m ≫ (snd A A).left = (snd Q.A Q.A).left ≫ ψ →
        LBIso (P.pull m) (abelian₂ Q.A Q.L) := by
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group C G).1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom x
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1.1 hg
  have := hc.isNoetherian
  have := hc.smooth
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (U : Set C))
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : AlgebraicGeometry.IsNoetherian U.toScheme := {}
  have hN : Geo.Tor.IsNormalScheme U.toScheme := AbelianLocusNormalisation.isNormalScheme_of_open U.ι
    (@GlobalTheory.IsNormalScheme.pred _ (isNormalScheme_of_smooth (strHom k C)))
  let η : Sp C.functionField ⟶ U.toScheme := U.fromSpecStalkOfMem _ hU
  have hη : η ≫ U.ι = CurveRootGeometry.genPt C := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have : IsPreimmersion (η ≫ U.ι) := hη ▸ inferInstanceAs (IsPreimmersion (C.fromSpecStalk _))
  have : IsPreimmersion η := .of_comp η U.ι
  have : IsDominant η := by
    have k := (IsGenericPointHom.quasiCompact_and_dominant_of_comp (k := η) (i := U.ι)
      (hη ▸ IsGenericPointHom.fromSpecStalk C)).2
    infer_instance
  have hw : φ₀ ≫ G.hom = (Q.A.hom ≫ η) ≫ U.ι := by rw [h₀.1.1.w, Category.assoc, hη]
  let ψ₀ : Q.A.left ⟶ A.left := h.1.1.lift φ₀ _ hw
  have hψ₀ : ψ₀ ≫ φ = φ₀ := h.1.1.lift_fst _ _ _
  have : Mono φ := MorphismProperty.of_isPullback (P := .monomorphisms _) h.1.1.flip
    (inferInstanceAs (Mono U.ι))
  have hp : CurveRootGeometry.IsActPull j₀ j η ψ₀ := by
    refine ⟨h.1.cancel (h₀.1.congr hη.symm hψ₀.symm) (h.1.1.lift_snd _ _ _), fun x ↦ ?_⟩
    rw [← cancel_mono φ, Category.assoc, Category.assoc, hψ₀, h.2, ← Category.assoc, hψ₀, h₀.2]
  obtain ⟨P, hs, hgen⟩ := GlobalTheory.T.abelian_extension_over_normal_base hD hP.p22 O c U hN _ η (IsGenericPointHom.of_isPreimmersion η) A j hA Q j₀ ψ₀ hp hr
  have hω := isVB_omega G g
  obtain ⟨d, hd⟩ := exists_datumOn q k c i hC hP hA hgA h hs hω
  refine ⟨P, g, hω, d, hs, hd, fun ψ m e₁ ↦ ?_⟩
  obtain rfl : ψ = ψ₀ := by rw [← cancel_mono φ, e₁, hψ₀]
  exact hgen m

theorem main : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
    IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G), CurveRootGeometry.AbGen c i →
    ∃ (U : C.Opens) (A : Over U.toScheme) (_ : GrpObj A) (j : OAct O A) (φ : A.left ⟶ G.left)
      (h : IsGrpPullback A G U.ι φ) (P : LB (A ⊗ A).left) (g : ℕ) (hg : IsVB (omega G) g)
      (d₀ : TwoSeq.DieuDatumOn q k c i g U.ι), genericPoint C ∈ U ∧ IsAbelianScheme A ∧ CurveRootGeometry.IsActPull j i U.ι φ ∧
      IsSelfDual c j P ∧ IsDRDatumOn q k c i j h P hg d₀ := by
  intro hX hP O _ c q _ k _ _ _ C _ _ hc G _ hG i ⟨Q, j₀, φ₀, h₀, hr⟩
  have := hc.isNoetherian
  obtain ⟨U, hU, hA⟩ := GlobalTheory.T.semiabelian_abelian_near_generic_point C _ (CurveRootGeometry.genPt C) (IsGenericPointHom.fromSpecStalk C) G hG Q.A φ₀ h₀.1 Q.isAb
  have := hG.comm
  have h : CurveRootGeometry.IsActPull (OAct.pullback U.ι G i) i U.ι (pullback.fst G.hom U.ι) :=
    ⟨isGrpPullback_pullback G U.ι, fun x ↦ pullback.lift_fst _ _ _⟩
  obtain ⟨P, g, hg, d, hs, hd, -⟩ := exists_datumOn_open hX.dual hX.conj hP c q k hc i Q j₀ φ₀ h₀ hr hU hA h
  exact ⟨U, _, _, _, _, h.1, P, g, hg, d, hU, hA, h, hs, hd⟩

end GlobalTheory.AbDatum
