import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.Vec

open TopologicalSpace GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO LieG)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [CommRing k] {x : Sp k ⟶ S}
  {G₁ : Over (Sp k)} [GrpObj G₁] {φ : G₁.left ⟶ G.left}

def form (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) :
    (Scheme.Modules.pullback x).obj (omega G) ⟶ GlobalTheory.structureModule (Sp k) :=
  omegaBase h ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso k).hom

theorem form_app (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {T : (Sp k).Opens}
    (s : Γ((Scheme.Modules.pullback x).obj (omega G), T)) :
    (form h p).app T s = dualApp (tangent p) le_top ((omegaBase h).app T s) := rfl

theorem pre_le (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W :=
  preimage_le_of_lieG p (le_of_sq (unitSec_comp h) hW hT)

theorem form_dUnit (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(G.left, W))
    (a b : Γ(Sp k, T))
    (e : ((p.1.left ≫ φ).appLE W _ (pre_le h p hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (form h p).app T (pullbackSections x (omega G) hT (dUnit G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  rw [form_app, omegaBase_dUnit h hW hT (le_of_sq (unitSec_comp h) hW hT) le_rfl]
  exact dualApp_tangent_dUnit p _ _ hV le_rfl (pre_le h p hW hT) a b
    ((appLE_appLE rfl _ _ _ f).trans e)

variable {k' : Type} [CommRing k'] (r : k →+* k') (F : DualNumber k →+* DualNumber k')

theorem spMap_comp_hom (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a)) :
    spMap F ≫ (specO k (DualNumber k)).hom = (specO k' (DualNumber k')).hom ≫ spMap r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext hF)

theorem spMap_epsFn (he : F DualNumber.eps = DualNumber.eps) :
    (spMap F).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F)) DualNumber.eps).symm.trans ?_
  exact congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom he

theorem epsZero_spMap (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) :
    sec (epsZero k') ≫ spMap F = spMap r ≫ sec (epsZero k) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (F a).fst = r a.fst
  have : a = algebraMap k _ a.fst + algebraMap k _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add, map_mul, hF, hF, he]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {G₂ : Over (Sp k')} [GrpObj G₂] {ψ : G₂.left ⟶ G.left}

theorem form_baseChange [QuasiSeparated G.hom] (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) (q : LieG G₂) (hq : q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ)
    {V : S.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap r ≫ x) ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      (spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤)) := by
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := GlobalTheory.Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V)
      (x := x (spMap r y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap r y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := G))) (resM _ hle s)
    have hf' : dUnit G c.le f = resM (omega G) hle s := hf
    have hTU' : spMap r ⁻¹ᵁ T ≤ (spMap r ≫ x) ⁻¹ᵁ U := (spMap r).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      ((p.1.left ≫ φ).appLE W _ (pre_le h₁ p c.le hTU) f)
    have e₁ := form_dUnit h₁ p c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        spMap F ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_comp_hom r F hF)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap r) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap F).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap r).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_comp_hom r F hF) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap F).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_epsFn F he)))
    have e₂ := form_dUnit h₂ q c.le hTU' f ((spMap r).appLE T _ le_rfl a)
      ((spMap r).appLE T _ le_rfl b) (by
        refine (appLE_appLE hq.symm (pre_le h₁ p c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap F).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap r ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (form h₂ q) le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap r) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap r) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (form h₁ p) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem exists_lieG (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) : ∃ q : LieG G₂, q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := by
  have w : (spMap F ≫ p.1.left ≫ φ) ≫ G.hom = (specO k' (DualNumber k')).hom ≫ spMap r ≫ x := by
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc p.1.left, Over.w p.1, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ x) (spMap_comp_hom r F hF)
  let q : specO k' (DualNumber k') ⟶ G₂ :=
    Over.homMk (h₂.1.lift _ (specO k' (DualNumber k')).hom w) (h₂.1.lift_snd _ _ _)
  have hq : q.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := h₂.1.lift_fst _ _ _
  have ht : (toUnit (specO k' k')).left = 𝟙 (Sp k') := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  refine ⟨⟨q, Over.OverMorphism.ext (h₂.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hq⟩
  rw [Over.comp_left, Over.comp_left, ht, Category.assoc, hq, Category.assoc]
  have e : sec (epsZero k') ≫ spMap F ≫ p.1.left ≫ φ = (spMap r ≫ x) ≫ unitSec G := by
    rw [← Category.assoc, epsZero_spMap r F hF he, Category.assoc, ← Category.assoc (sec _), sec_epsZero_comp,
      unitSec_comp h₁, Category.assoc]
  exact e.trans ((unitSec_comp h₂).symm.trans (Category.id_comp _).symm)

theorem dual_vec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  rintro S G _ _ g c R R' _ _ ξ r _ y y' rfl hG - ⟨hc, hy⟩ ⟨hc', hy'⟩ F hF he j
  obtain ⟨p, hp, hp'⟩ := hy j
  obtain ⟨q, hq, hq'⟩ := hy' j
  have h₁ := isGrpPullback_pullback G ξ
  have h₂ := isGrpPullback_pullback G (spMap r ≫ ξ)
  obtain ⟨w, hw⟩ := exists_lieG r F hF he h₁ h₂ p
  have hfr : VB.IsFrame (pfr c (spMap r ≫ ξ) hc') := by
    have k₁ := ((c.isFrame.pullback (spMap r ≫ ξ)).res hc').map_iso (omegaBase h₂)
    have k₂ (b : Fin g) : resM _ hc' (pullbackSections (spMap r ≫ ξ) (omega G) le_rfl (c.e b)) =
        pullbackSections (spMap r ≫ ξ) (omega G) hc' (c.e b) := QCoh.res_pullbackSections _ _ _ _ _
    simp only [k₂] at k₁
    exact k₁
  obtain rfl : w = q := tangent_injective R' _ (hfr.dual_ext le_rfl fun b => by
    rw [resM_self]
    refine (form_baseChange r F hF he h₁ h₂ p w hw hc hc' (c.e b)).trans ?_
    refine .trans (congrArg ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)) (hp' b)) (.trans ?_ (hq' b).symm)
    exact (apply_ite _ _ _ _).trans (if_congr Iff.rfl
      (map_one ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom) (map_zero ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom)))
  rw [← hq, ← hp]
  exact hw

end GlobalTheory.KeyVals.Vec

end
