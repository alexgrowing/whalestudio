import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)
open GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB GlobalTheory.LieVB.TangentSurj
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.TanFibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ π = 𝟙 X)
  {x : Sp k ⟶ X} {v v' : (specO k (DualNumber k)).left ⟶ Y}

def form (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e) :
    (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k) :=
  baseMap (sec_hom (epsZero k)) w we ≫ (epsIso k).hom

theorem form_d (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ e ⁻¹ᵁ W) (f : Γ(Y, W)) {U : (Sp k).Opens} (hU : U ≤ x ⁻¹ᵁ V)
    (q : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W) (a b : Γ(Sp k, U))
    (H : v.appLE W _ q f = (specO k (DualNumber k)).hom.appLE U _ le_rfl a +
      (specO k (DualNumber k)).hom.appLE U _ le_rfl b * resG _ le_top (epsFn k)) :
    (form w we).app U (pullbackSections x _ hU (d he h f)) = b := by
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  refine (congrArg ((epsIso k).hom.app U) (baseMap_d he (sec_hom (epsZero k)) w we h hU hV q f)).trans ?_
  rw [H, map_add, d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : U ≤ ⊤)))).trans (_root_.mul_one b)

theorem preimage_le (we : sec (epsZero k) ≫ v = x ≫ e) {U : (Sp k).Opens} {W : Y.Opens}
    (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ e) ⁻¹ᵁ W := h h₁
  rw [← we] at h₂
  exact h₂

theorem appLE_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {U : (Sp k).Opens} (hU : IsAffineOpen U) {W : Y.Opens} (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(Y, W)) :
    v.appLE W _ (preimage_le we h) f =
      (specO k (DualNumber k)).hom.appLE U _ le_rfl ((x ≫ e).appLE W U h f) +
        (specO k (DualNumber k)).hom.appLE U _ le_rfl
          ((form w we).app U (pullbackSections x _ h (d he le_rfl f))) * resG _ le_top (epsFn k) := by
  obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k U hU).2 (v.appLE W _ (preimage_le we h) f)
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have hb := form_d he w we le_rfl f h (preimage_le we h) a b E.symm
  have ha : (x ≫ e).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero k)).appLE _ U hV) E
    simp only [map_add, map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      resG_self, appLE_appLE we _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact E.symm

include he in

theorem eq_of_form_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    (w' : v' ≫ π = (specO k (DualNumber k)).hom ≫ x) (we' : sec (epsZero k) ≫ v' = x ≫ e)
    (H : form w we = form w' we') : v = v' := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, hW', -⟩ := QCoh.exists_affine_mem_le (U := ⊤)
    (e (x ((specO k (DualNumber k)).hom t))) trivial
  obtain ⟨U, hU, hU', h⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ e ⁻¹ᵁ W)
    ((specO k (DualNumber k)).hom t) hW'
  have hT : IsAffineOpen ((specO k (DualNumber k)).hom ⁻¹ᵁ U) := hU.preimage _
  have E : v.appLE W _ (preimage_le we h) = v'.appLE W _ (preimage_le we' h) := by
    ext f
    exact (appLE_eq he w we hU h f).trans (H ▸ (appLE_eq he w' we' hU h f).symm)
  refine ⟨(specO k (DualNumber k)).hom ⁻¹ᵁ U, hU', ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we h),
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we' h), E]

include he in

theorem exists_form_eq [QuasiSeparated π]
    (L : (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k)) :
    ∃ (v : (specO k (DualNumber k)).left ⟶ Y) (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x)
      (we : sec (epsZero k) ≫ v = x ≫ e), form w we = L := by
  let e' : Sp k ⟶ pullback π x := pullback.lift (x ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd π x = 𝟙 _ := pullback.lift_snd _ _ _
  have we' : e' ≫ pullback.fst π x = x ≫ e := pullback.lift_fst _ _ _
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have : QuasiCompact e' :=
    have : QuasiCompact (e' ≫ pullback.snd π x) := he' ▸ inferInstance
    .of_comp _ (pullback.snd π x)
  have := isIso_baseMap he he' (IsPullback.of_hasPullback π x) we'
  let β := baseMap he' (IsPullback.of_hasPullback π x).w we'
  let D := homEquivDer _ he' (inv β ≫ L)
  let u := deform (specO k (DualNumber k)).hom (epsFn k) (epsFn_sq k) D
  have w : (u ≫ pullback.fst π x) ≫ π = (specO k (DualNumber k)).hom ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, deform_comp _ _ _ D he']
  have we : sec (epsZero k) ≫ u ≫ pullback.fst π x = x ≫ e := by
    rw [← Category.assoc, comp_deform _ _ (epsFn_sq k) D (sec_hom (epsZero k)) (epsZero_epsFn k), we']
  refine ⟨_, w, we, pullback_hom_ext he fun W f => ?_⟩
  have k₁ : x ⁻¹ᵁ e ⁻¹ᵁ W ≤ e' ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := le_of_sq we' le_rfl le_rfl
  have k₂ := (specO k (DualNumber k)).hom.preimage_mono k₁
  let g := (pullback.fst π x).appLE W _ le_rfl f
  refine (form_d he w we le_rfl f le_rfl (preimage_le we le_rfl) (e'.appLE _ _ k₁ g) (val D k₁ g) ?_).trans ?_
  · have k₃ : (specO k (DualNumber k)).hom ⁻¹ᵁ x ⁻¹ᵁ e ⁻¹ᵁ W ≤ u ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := k₂
    have e₁ : u.appLE _ _ k₃ g = resG _ k₂ (psi _ _ (epsFn_sq k) D _ g) :=
      deform_appLE _ _ (epsFn_sq k) D _ k₂ g
    rw [← appLE_appLE (f := u) (g := pullback.fst π x) rfl le_rfl k₃, e₁, psi_apply, map_add, map_mul, LB.resG_resG, DualPull.resG_appLE, DualPull.resG_appLE,
      ← DualPull.resG_appLE e' k₁ le_rfl, DualPull.appLE_resG,
      show val D k₁ g = resG _ k₁ (val D le_rfl g) from (D.res_app le_rfl k₁ g).symm, DualPull.appLE_resG]
  · have b := baseMap_d he he' (IsPullback.of_hasPullback π x).w we' le_rfl le_rfl k₁ le_rfl f
    have c : val D k₁ g = (inv β ≫ L).app _ (d he' k₁ g) := homEquivDer_app he' (inv β ≫ L) k₁ g
    rw [c, ← b]
    generalize pullbackSections x (conormal e) _ (d he _ f) = s
    have i : β ≫ inv β ≫ L = L := IsIso.hom_inv_id_assoc β L
    conv_rhs => rw [← i]
    rw [Scheme.Modules.Hom.comp_app β, AddCommGrpCat.comp_apply]

theorem exists_hom_of_isFrame {F : X.Modules} {n : ℕ} {s : Fin n → Γ(F, ⊤)} (hs : IsFrame s) (c : Fin n → Γ(X, ⊤)) :
    ∃ L : F ⟶ structureModule X, ∀ l, L.app ⊤ (s l) = c l := by
  refine ⟨homGlobalEquiv _ _ (∑ i, c i • hs.coord i), fun l => ?_⟩
  change dualApp (∑ i, c i • hs.coord i) le_rfl (s l) = c l
  have hsum (T : Finset (Fin n)) : dualApp (∑ i ∈ T, c i • hs.coord i) le_rfl (s l) = if l ∈ T then c l else 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have := dualApp_smul (0 : Γ(X, ⊤)) (hs.coord l) le_rfl
      rw [zero_smul, map_zero, zero_smul] at this
      rw [Finset.sum_empty, this]
      simp
    | insert i T hi ih =>
      have := hs.dualApp_coord_frame i l le_rfl
      rw [Twist.resM_self] at this
      rw [Finset.sum_insert hi, dualApp_add, LinearMap.add_apply, ih, dualApp_smul, LinearMap.smul_apply, this,
        resG_self]
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  simpa using hsum Finset.univ

theorem existsUnique_tanEv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  intro E _ _ _ H X t k _ x V h n m hm c
  have := t.semi
  have hf : IsFrame fun l => pullbackSections x (omega t.G) h (m l) := by
    have := (hm.pullback x).res h
    exact (funext fun l => QCoh.res_pullbackSections x (omega t.G) le_rfl h (m l)) ▸ this
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame hf fun l => cst k (c l)
  obtain ⟨v, w, we, hv⟩ := exists_form_eq (sec_hom η[t.G]) L
  have hv' : IsTanAtG t x v := ⟨w, we.trans (by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl)⟩
  have hval (l) : tanEv t hv' h (m l) = c l :=
    (congrArg (fun (a : Γ(Sp k, ⊤)) => (Scheme.ΓSpecIso (.of k)).hom a)
      ((congr(($hv).app ⊤ _)).trans (hL l))).trans (Iso.inv_hom_id_apply _ _)
  refine ⟨v, ⟨hv', hval⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  refine eq_of_form_eq (sec_hom η[t.G]) hu.1 (epsZero_comp_of_isTanAtG t hu) w we (hom_ext_of_isFrame hf fun l => ?_)
  exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ((hu' l).trans (hval l).symm)

end GlobalTheory.TanFibre
