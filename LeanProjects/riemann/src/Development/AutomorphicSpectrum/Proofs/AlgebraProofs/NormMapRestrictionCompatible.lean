import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatLocallyFreeAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.FinFlatNorm

open TopologicalSpace GlobalTheory.FiniteAmple GlobalTheory.LB ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm
open GlobalTheory.FlatNorm (nm nm_of_isPushout isUnit_of_nm exists_preimage_le)

variable {X Y : Scheme.{0}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]

theorem exists_finFree_app_of_finitePresentation {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (π.app V).hom := by
  obtain ⟨V0, hV0, hxV0, hV0U⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hfin : (π.app V0).hom.Finite := IsFinite.finite_app π V0 hV0
  have hfl : (π.app V0).hom.Flat := by
    have := HasRingHomProperty.appLE @Flat π inferInstance ⟨V0, hV0⟩ ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hfp : (π.app V0).hom.FinitePresentation := by
    have := HasRingHomProperty.appLE @LocallyOfFinitePresentation π inferInstance ⟨V0, hV0⟩
      ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  obtain ⟨r, hr, H⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_finFree_away_of_finitePresentation hfin hfl hfp
    (hV0.primeIdealOf ⟨x, hxV0⟩)
  refine ⟨X.basicOpen r, hV0.basicOpen r, ?_, (X.basicOpen_le r).trans hV0U, ?_⟩
  · have h1 : hV0.primeIdealOf ⟨x, hxV0⟩ ∈
        (TopologicalSpace.Opens.map hV0.fromSpec.base).obj (X.basicOpen r) := by
      rw [hV0.fromSpec_preimage_basicOpen]
      exact hr
    have h2 : hV0.fromSpec (hV0.primeIdealOf ⟨x, hxV0⟩) ∈ X.basicOpen r := h1
    rwa [hV0.fromSpec_primeIdealOf] at h2
  · exact H (isPushout_app π hV0 (hV0.basicOpen r) (X.basicOpen_le r))
      (RingedSpace.isUnit_res_basicOpen _ r)

abbrev FreeOpen (V : X.Opens) : Type := {W : X.Opens // IsAffineOpen W ∧ W ≤ V ∧ FinFree (π.app W).hom}

theorem le_iSup_freeOpen (V : X.Opens) : V ≤ ⨆ W : FreeOpen π V, W.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWV, hF⟩, hxW⟩

theorem ext_freeOpen {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ W : FreeOpen π V, resG X W.2.2.1 a = resG X W.2.2.1 b) : a = b := by
  refine TopCat.Presheaf.section_ext X.sheaf V a b fun x hx => ?_
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp (le_iSup_freeOpen π V hx)
  have e := congrArg (X.presheaf.germ W.1 x hxW).hom (h W)
  simp [resG] at e
  exact e

omit [Flat π] [LocallyOfFinitePresentation π] in
theorem resG_nm {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (π.app V).hom) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (nm (π.app V).hom b) = nm (π.app W).hom (resG Y (π.preimage_mono h) b) := by
  exact (nm_of_isPushout (isPushout_app π hV hW h) hF b).symm

private theorem resG_nm_app_eq_nm_app_of_le_freeOpen {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (k : FreeOpen π V) {W' : X.Opens}
    (hW' : IsAffineOpen W') (h : W' ≤ k.1) :
    resG X h (nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) =
      nm (π.app W').hom (resG Y (π.preimage_mono (h.trans k.2.2.1)) b) := by
  rw [resG_nm π k.2.1 hW' h k.2.2.2, resG_resG]

theorem exists_normFun (V : X.Opens) (b : Γ(Y, π ⁻¹ᵁ V)) : ∃ a : Γ(X, V), ∀ W : FreeOpen π V,
    resG X W.2.2.1 a = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  refine exists_fun_of_cover (fun k : FreeOpen π V => k.1) (fun k => k.2.2.1) (le_iSup_freeOpen π V)
    (fun k => nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) fun k l => ?_
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_resG, resG_nm_app_eq_nm_app_of_le_freeOpen π b k W'.2.1, resG_nm_app_eq_nm_app_of_le_freeOpen π b l W'.2.1]

def normFun (V : X.Opens) : Γ(Y, π ⁻¹ᵁ V) →* Γ(X, V) where
  toFun b := (exists_normFun π V b).choose
  map_one' := ext_freeOpen π fun W => by
    rw [(exists_normFun π V 1).choose_spec W, map_one, map_one, map_one]
  map_mul' a b := ext_freeOpen π fun W => by
    rw [(exists_normFun π V _).choose_spec W, map_mul, map_mul, map_mul,
      (exists_normFun π V a).choose_spec W, (exists_normFun π V b).choose_spec W]

theorem resG_normFun_free {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (W : FreeOpen π V) :
    resG X W.2.2.1 (normFun π V b) = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  exact (exists_normFun π V b).choose_spec W

theorem resG_normFun {V W : X.Opens} (h : W ≤ V) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (normFun π V b) = normFun π W (resG Y (π.preimage_mono h) b) := by
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_normFun_free π b ⟨W'.1, W'.2.1, W'.2.2.1.trans h, W'.2.2.2⟩,
    resG_normFun_free π _ W', resG_resG]

private theorem basicOpen_resG_eq_inf_basicOpen {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U)) :
    Z.basicOpen (resG Z h f) = V ⊓ Z.basicOpen f :=
  Z.basicOpen_res f (homOfLE h).op

private theorem isUnit_resG_of_le_basicOpen' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U))
    (hV : V ≤ Z.basicOpen f) : IsUnit (resG Z h f) := by
  rw [← resG_resG (Z.basicOpen_le f) hV f]
  exact (RingedSpace.isUnit_res_basicOpen _ f).map (resG Z hV)

theorem mem_basicOpen_normFun {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (normFun π V b) ↔ ∀ y, π y = x → y ∈ Y.basicOpen b := by
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  have e0 := resG_normFun_free π b ⟨W, hW, hWV, hF⟩
  have key : x ∈ X.basicOpen (normFun π V b) ↔
      x ∈ X.basicOpen (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b)) := by
    rw [← e0, basicOpen_resG_eq_inf_basicOpen]
    exact ⟨fun h => ⟨hxW, h⟩, fun h => h.2⟩
  rw [key]
  constructor
  · intro hx' y hy
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ := exists_finFree_app_of_finitePresentation π hx'
    have hW''W : W'' ≤ W := hle.trans (X.basicOpen_le _)
    have hu := isUnit_resG_of_le_basicOpen' hW''W _ hle
    rw [resG_nm π hW hW'' hW''W hF, resG_resG] at hu
    have hu' := isUnit_of_nm hF'' hu
    have hy'' : y ∈ Y.basicOpen (resG Y (π.preimage_mono (hW''W.trans hWV)) b) := by
      rw [Y.basicOpen_of_isUnit hu']
      show π y ∈ W''
      rw [hy]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at hy''
    exact hy''.2
  · intro hall
    have hall' : ∀ y, π y = x → y ∈ Y.basicOpen (resG Y (π.preimage_mono hWV) b) := by
      intro y hy
      rw [basicOpen_resG_eq_inf_basicOpen]
      refine ⟨?_, hall y hy⟩
      show π y ∈ W
      rw [hy]
      exact hxW
    obtain ⟨V', hxV', hV'⟩ := exists_preimage_le π hall'
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ :=
      exists_finFree_app_of_finitePresentation π (U := W ⊓ V') ⟨hxW, hxV'⟩
    have hW''W : W'' ≤ W := hle.trans inf_le_left
    have hu := isUnit_resG_of_le_basicOpen' (π.preimage_mono hW''W) (resG Y (π.preimage_mono hWV) b)
      ((π.preimage_mono (hle.trans inf_le_right)).trans hV')
    have hu2 := hu.map (nm (π.app W'').hom)
    rw [← resG_nm π hW hW'' hW''W hF] at hu2
    have h3 : x ∈ X.basicOpen (resG X hW''W (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b))) := by
      rw [X.basicOpen_of_isUnit hu2]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at h3
    exact h3.2

end GlobalTheory.CompanionTheory.FinFlatNorm

open GlobalTheory.CompanionTheory.FinFlatNorm in

theorem GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  intro X Y q h1 h2 h3
  exact ⟨normFun q, fun V W h a => resG_normFun q h a, fun V a y hy => mem_basicOpen_normFun q a hy⟩
