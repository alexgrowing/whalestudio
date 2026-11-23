import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
open GlobalTheory.Conormal GlobalTheory.Cris GlobalTheory.TanFibre
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open GlobalTheory.LocM (spMap_dualMap_comp spMap_dualMap_epsFn)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeSub.Nat

section Form

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y}

theorem form_baseChange (he : e ≫ π = 𝟙 X) [QuasiSeparated π] (φ : k →+* k') {x : Sp k ⟶ X}
    {v : (specO k (DualNumber k)).left ⟶ Y}
    (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {x' : Sp k' ⟶ X} {v' : (specO k' (DualNumber k')).left ⟶ Y}
    (w' : v' ≫ π = (specO k' (DualNumber k')).hom ≫ x') (we' : sec (epsZero k') ≫ v' = x' ≫ e)
    (ex : spMap φ ≫ x = x') (ev : spMap (Formalism.L2.Pj.dualMap φ) ≫ v = v')
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x' ⁻¹ᵁ V) (s : Γ(conormal e, V)) :
    ((form w' we').app ⊤ (pullbackSections _ _ h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form w we).app ⊤ (pullbackSections x _ h s) : Γ(Sp k, ⊤)) := by
  subst ex ev
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((form w' we').app ⊤ (pullbackSections _ _ h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form w we).app ⊤ (pullbackSections x _ h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart he (V := V) (x := x (spMap φ y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective he (resM _ hle s)
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    have hTW : T ≤ x ⁻¹ᵁ e ⁻¹ᵁ W := hTU.trans (x.preimage_mono c.le)
    have hTW' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ e ⁻¹ᵁ W := (spMap φ).preimage_mono hTW
    obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k T hT).2 (v.appLE W _ (preimage_le we hTW) f)
    have e₁ := form_d he w we c.le f hTU (preimage_le we hTW) a b E.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := form_d he w' we' c.le f hTU' (preimage_le we' hTW') ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le we hTW) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) E.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf, QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (form w' we') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (form w we) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

variable {A : Over X} [GrpObj A] {x : Sp k ⟶ X} {G : Over (Sp k)} [GrpObj G] {ψ : G.left ⟶ A.left}

theorem form_eq_fibre (hp : IsGrpPullback G A x ψ) {y : specO k (DualNumber k) ⟶ G} (hy : epsZero k ≫ y = η)
    (w : (y.left ≫ ψ) ≫ A.hom = (specO k (DualNumber k)).hom ≫ x)
    (we : sec (epsZero k) ≫ y.left ≫ ψ = x ≫ unitSec A) :
    form w we = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[A]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq we (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp (rfl : y.left ≫ ψ = _)).2 (le_refl ((y.left ≫ ψ) ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[A]) (sec_hom (epsZero k)) w we le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE rfl _ _ _ a))

theorem epsZero_comp_of_isTangent {y : epsR k ⟶ G} (hy : IsTangent y) : epsZero k ≫ y = η :=
  Over.OverMorphism.ext hy

def ev (σ : Γ(omega G, ⊤)) : (conormal (unitSec G) ⟶ conormal (sec (epsZero k))) →+ k :=
  AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
    (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
      (map_add _ _ _)

def tv (σ : Γ(omega G, ⊤)) (v : epsR k ⟶ G) (hv : IsTangent v) : k :=
  ev σ (cotMap (T' := specO k (DualNumber k)) v (epsZero_comp_of_isTangent hv))

theorem tv_scale (σ : Γ(omega G, ⊤)) (r : k) {y : epsR k ⟶ G} (hy : IsTangent y)
    (hz : IsTangent (GrpTangent.epsScale r ≫ y)) : tv σ _ hz = r * tv σ y hy := by
  have e := cotMap_comp (T' := specO k (DualNumber k)) (epsZero_comp_of_isTangent hy) (epsZero_dualScale r)
    (χ := GrpTangent.epsScale r ≫ y) rfl (epsZero_comp_of_isTangent hz)
  rw [cotMap_dualScale] at e
  refine (congrArg (ev σ) e).symm.trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app_smul (cst k r)
    ((cotMap (T' := specO k (DualNumber k)) y (epsZero_comp_of_isTangent hy)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem tv_mul [QuasiSeparated G.hom] (σ : Γ(omega G, ⊤)) {y z : epsR k ⟶ G} (hy : IsTangent y)
    (hz : IsTangent z) (h : IsTangent (y * z)) : tv σ _ h = tv σ y hy + tv σ z hz :=
  (congrArg (ev σ) (cotMap_mul (T := specO k (DualNumber k)) (epsZero_comp_of_isTangent hy)
    (epsZero_comp_of_isTangent hz) (epsZero_comp_of_isTangent h))).trans (map_add _ _ _)

theorem tv_one (σ : Γ(omega G, ⊤)) (h : IsTangent (1 : epsR k ⟶ G)) : tv σ _ h = 0 :=
  (congrArg (ev σ) (cotMap_eq_zero (T' := specO k (DualNumber k)) (Hom.one_def).symm
    (epsZero_comp_of_isTangent h))).trans (map_zero _)

def Good (σ : Γ(omega G, ⊤)) (c : primDR G) (h : HdR G) : Prop :=
  ∀ (v : epsR k ⟶ G) (hv : IsLieImage h v), h c = tv σ v hv.1

variable {σ : Γ(omega G, ⊤)} {c : primDR G}

theorem Good.add [QuasiSeparated G.hom] (H : LieExact G) {a b : HdR G} (ha : Good σ c a) (hb : Good σ c b) :
    Good σ c (a + b) := fun v hv ↦ by
  obtain ⟨va, ea, -⟩ := H.1 a
  obtain ⟨vb, eb, -⟩ := H.1 b
  obtain rfl := (H.1 _).unique hv (ea.add eb)
  rw [tv_mul σ ea.1 eb.1, ← ha _ ea, ← hb _ eb, LinearMap.add_apply]

theorem Good.zero (H : LieExact G) : Good σ c 0 := fun v hv ↦ by
  obtain rfl := (H.1 _).unique hv (isLieImage_one_iff.2 (zero_mem _))
  rw [tv_one, LinearMap.zero_apply]

theorem Good.smul (H : LieExact G) (r : k) {a : HdR G} (ha : Good σ c a) : Good σ c (r • a) := fun v hv ↦ by
  obtain ⟨va, ea, -⟩ := H.1 a
  obtain rfl := (H.1 _).unique hv (ea.smul r)
  rw [tv_scale σ r ea.1, ← ha _ ea, LinearMap.smul_apply, smul_eq_mul]

end Form

section DeRham

variable {R R' : Type} [CommRing R] [CommRing R']

variable [Algebra R R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)

open GlobalTheory.Published.AbelianDeRham (bcMor)

theorem mem_of_corr [Module.Finite R (primDR A)] [Module.Projective R (primDR A)] (hm : (bcMor hφ).IsBC)
    (N : HdR A' → Prop) (h0 : N 0) (ha : ∀ a b, N a → N b → N (a + b)) (hs : ∀ (r : R') a, N a → N (r • a))
    (hN : ∀ h h', (bcMor hφ).Corr h h' → N h') (h' : HdR A') : N h' := by
  obtain ⟨n, p, q, -, -, hpq⟩ := Module.Finite.exists_comp_eq_id_of_projective R (primDR A)
  choose l hl using fun i : Fin n ↦ hm.exists (LinearMap.proj i ∘ₗ q)
  have : h' = ∑ i, h' ((bcMor hφ).pull (p (Pi.single i 1))) • l i := by
    refine LinearMap.ext fun c ↦ ?_
    obtain ⟨z, rfl⟩ := hm.2 c
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      rw [liftSemi_tmul, map_smul, map_smul]
      congr 1
      have hc : c = ∑ i, q c i • p (Pi.single i 1) := by
        conv_lhs => rw [← show p (q c) = c from LinearMap.congr_fun hpq c, pi_eq_sum_univ' (q c), map_sum]
        simp only [map_smul]
      rw [LinearMap.sum_apply]
      conv_lhs => rw [hc, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, hl i c, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
  rw [this]
  exact Finset.sum_induction _ N ha h0 fun i _ ↦ hs _ _ (hN _ _ (hl i))

end DeRham

theorem corr_res : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
      letI := resAlg h
      ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
        (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
        φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
        ∀ (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c : primDR (onAff A hV)), GlobalTheory.HodgeSub.Corr A hV s c →
          GlobalTheory.HodgeSub.Corr A hV' (GlobalTheory.Twist.resM _ h s) ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  intro P T A _ g hA hg V V' hV hV' h φ hφ eφ s c hc
  letI := resAlg h
  have hA₁ := VB.isAbelianScheme_onAff A hA hV
  have hg₁ := VB.smooth_onAff A hg hV
  have hA₂ := VB.isAbelianScheme_onAff A hA hV'
  have hg₂ := VB.smooth_onAff A hg hV'
  have H := (P.p5.2.1 _ _ g hA₁ hg₁).1
  have H' := (P.p5.2.1 _ _ g hA₂ hg₂).1
  obtain ⟨hm, hF⟩ := P.p5.2.2.1 _ _ g hA₁ hg₁ _ _ φ hφ
  obtain ⟨_, _, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.p5.1 hA₁ hg₁
  have := hA.proper
  have := hA₂.proper
  have hp : IsGrpPullback (onAff A hV) A hV.fromSpec _ := isGrpPullback_pullback A hV.fromSpec
  have hp' : IsGrpPullback (onAff A hV') A hV'.fromSpec _ := isGrpPullback_pullback A hV'.fromSpec
  let σ := (omegaBase hp').app ⊤ (pullbackSections hV'.fromSpec (omega A) hV'.fromSpec_preimage_self.ge
    (resM _ h s))
  have hσ (v' : epsR Γ(T, V') ⟶ onAff A hV') (hv' : IsTangent v')
      (w : (v'.left ≫ pullback.fst A.hom hV'.fromSpec) ≫ A.hom =
        (specO Γ(T, V') (DualNumber Γ(T, V'))).hom ≫ hV'.fromSpec)
      (we : sec (epsZero Γ(T, V')) ≫ v'.left ≫ pullback.fst A.hom hV'.fromSpec =
        hV'.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A) :
      (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V'))).hom ((form w we).app ⊤
        (pullbackSections hV'.fromSpec (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) hV'.fromSpec_preimage_self.ge (resM _ h s))) =
      tv σ v' hv' :=
    congr((Scheme.ΓSpecIso (CommRingCat.of Γ(T, V'))).hom
      (($(form_eq_fibre hp' (epsZero_comp_of_isTangent hv') w we)).app ⊤ _))
  have sq {W : T.Opens} (hW : IsAffineOpen W) (v : epsR Γ(T, W) ⟶ onAff A hW) (hv : IsTangent v) :
      (v.left ≫ pullback.fst A.hom hW.fromSpec) ≫ A.hom =
        (specO Γ(T, W) (DualNumber Γ(T, W))).hom ≫ hW.fromSpec ∧
      sec (epsZero Γ(T, W)) ≫ v.left ≫ pullback.fst A.hom hW.fromSpec =
        hW.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A := by
    constructor
    · rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ hW.fromSpec) (Over.w v)
    · rw [← Category.assoc]
      exact (congrArg (· ≫ pullback.fst A.hom hW.fromSpec) hv).trans
        (unitSec_comp (isGrpPullback_pullback A hW.fromSpec))
  intro v' h' hv' w we
  rw [hσ v' hv'.1 w we]
  refine mem_of_corr hφ hm (Good σ ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c)) (Good.zero H')
    (fun _ _ ↦ Good.add H') (fun r _ ↦ Good.smul H' r) ?_ h' v' hv'
  intro k k' hk u' hu'
  obtain ⟨u, hu, -⟩ := H.1 k
  obtain ⟨u'', e⟩ := ArcQ.NormalForm.exists_baseChange hφ u
  obtain rfl := (H'.1 _).unique hu' (hu.baseChange (hφ := hφ) hF H' hk e)
  have t := hu'.1
  rw [← hσ u' t (sq hV' u' t).1 (sq hV' u' t).2, hk, hc u k hu (sq hV u hu.1).1 (sq hV u hu.1).2]
  have b := form_baseChange (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec_comp A) (algebraMap Γ(T, V) Γ(T, V'))
    (sq hV u hu.1).1 (sq hV u hu.1).2 (sq hV' u' t).1 (sq hV' u' t).2 (VB.fromSpec_res hV hV' h)
    (by rw [← eφ, ← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ _) e.symm)
    hV.fromSpec_preimage_self.ge (hV'.fromSpec_preimage_self.ge.trans (hV'.fromSpec.preimage_mono h)) s
  refine Eq.symm ((congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V'))).hom ((form _ _).app ⊤ z))
    (QCoh.pullbackSections_res hV'.fromSpec _ hV'.fromSpec_preimage_self.ge h s)).trans ?_)
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V'))).hom b).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V'))).hom (appLE_top (spMap _) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap Γ(T, V) Γ(T, V')))) _)

end GlobalTheory.HodgeSub.Nat
