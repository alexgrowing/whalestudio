import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}

def gm (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* P.presheaf.stalk z :=
  (P.presheaf.germ (f ⁻¹ᵁ V) z hz).hom.comp (f.app V).hom

theorem germ_appLE (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (W : P.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hz : z ∈ W) (u : Γ(X.left, V)) :
    (P.presheaf.germ W z hz).hom ((f.appLE V W h).hom u) = gm f z V (h hz) u :=
  TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE h) z hz _

theorem gm_res (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V) (hz : z ∈ f ⁻¹ᵁ V')
    (u : Γ(X.left, V)) :
    gm f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gm f z V (h hz) u := by
  rw [← germ_appLE f z V' _ le_rfl hz, ← germ_appLE f z V (f ⁻¹ᵁ V') (fun _ hx => h hx) hz]
  congr 1
  exact congrArg (fun φ => φ.hom u) (f.map_appLE le_rfl (homOfLE h).op)

def gmDual (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* DualNumber (P.presheaf.stalk z) where
  toFun b := (gm f z V hz b, gm f z V hz (D.D V b))
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    show gm f z V hz (D.D V 1) = 0
    have := D.const V 1
    rw [map_one] at this
    rw [this, map_zero])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show gm f z V hz (D.D V (a * b)) = gm f z V hz a * gm f z V hz (D.D V b) +
      gm f z V hz (D.D V a) * gm f z V hz b
    rw [D.leibniz, map_add, map_mul, map_mul]; ring)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by
    show gm f z V hz (D.D V 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    show gm f z V hz (D.D V (a + b)) = gm f z V hz (D.D V a) + gm f z V hz (D.D V b)
    rw [map_add, map_add])

theorem gmDual_res (D : VF X) (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V)
    (hz : z ∈ f ⁻¹ᵁ V') (u : Γ(X.left, V)) :
    gmDual D f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gmDual D f z V (h hz) u :=
  TrivSqZeroExt.ext (gm_res f z V V' h hz u) (by
    show gm f z V' hz (D.D V' _) = gm f z V (h hz) (D.D V u)
    rw [D.res, gm_res])

theorem extend (D : VF X) (f : P ⟶ X.left) (z : P)
    (Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z)) (V₀ : X.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hz₀ : z ∈ f ⁻¹ᵁ V₀)
    (H : ∀ u, Φ (gm f z V₀ hz₀ u) = gmDual D f z V₀ hz₀ u)
    (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    Φ (gm f z V hz u) = gmDual D f z V hz u := by
  obtain ⟨r, hr, hzr⟩ := hV₀.exists_basicOpen_le (V := V) ⟨f z, hz⟩ hz₀
  have hzr' : z ∈ f ⁻¹ᵁ X.left.basicOpen r := hzr
  have := hV₀.isLocalization_basicOpen r
  have e : Φ.comp (gm f z _ hzr') = gmDual D f z _ hzr' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    refine RingHom.ext fun a => ?_
    have h1 := gm_res f z V₀ _ (X.left.basicOpen_le r) hzr' a
    have h2 := gmDual_res D f z V₀ _ (X.left.basicOpen_le r) hzr' a
    exact ((congrArg Φ h1).trans (H a)).trans h2.symm
  rw [← gm_res f z V _ hr hzr', ← gmDual_res D f z V _ hr hzr']
  exact RingHom.congr_fun e _

theorem gmDual_const (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V)
    (c : Γ(Sp K, ⊤)) :
    gmDual D f z V hz ((X.hom.appLE ⊤ V le_top).hom c) =
      TrivSqZeroExt.inl ((P.presheaf.germ ⊤ z trivial).hom (((f ≫ X.hom).appLE ⊤ ⊤ le_top).hom c)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show gm f z V hz _ = (P.presheaf.germ ⊤ z trivial).hom _
    rw [← germ_appLE f z V _ le_rfl hz,
      ← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)) z hz]
    congr 1
    have e1 := Scheme.Hom.appLE_comp_appLE f X.hom ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
    have e2 := (f ≫ X.hom).appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
    exact congrArg (fun φ => φ.hom c) (e1.trans e2.symm)
  · show gm f z V hz (D.D V _) = 0
    have e : (X.hom.appLE ⊤ V le_top).hom c =
        cstK X V ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c) := by
      show _ = (X.hom.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _)
      congr 1
      exact (congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id).symm
    rw [e, D.const, map_zero]

theorem exists_dual {Y : Over (Sp K)} (p : P ⟶ X.left) (q : P ⟶ Y.left)
    (H : IsPullback p q X.hom Y.hom) (D : VF X) (E : VF Y) (z : P) :
    ∃ Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z), (∀ a, (Φ a).fst = a) ∧
      (∀ V hz u, Φ (gm p z V hz u) = gmDual D p z V hz u) ∧
      ∀ V hz u, Φ (gm q z V hz u) = gmDual E q z V hz u := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p z)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hW : IsAffineOpen W := hW
  have hzU : z ∈ p ⁻¹ᵁ U := hzU
  have hzW : z ∈ q ⁻¹ᵁ W := hzW
  have hO : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
    have : IsAffine _ := isAffineOpen_top (Sp K)
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top
    le_top rfl).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have hz : z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W := ⟨hzU, hzW⟩
  have w : X.hom.appLE ⊤ U le_top ≫ CommRingCat.ofHom (gmDual D p z U hzU) =
      Y.hom.appLE ⊤ W le_top ≫ CommRingCat.ofHom (gmDual E q z W hzW) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    refine (gmDual_const D p z U hzU c).trans (Eq.trans ?_ (gmDual_const E q z W hzW c).symm)
    simp only [H.w]
  let φ := po.desc _ _ w
  have h1 : ∀ u, φ.hom ((p.appLE U _ inf_le_left).hom u) = gmDual D p z U hzU u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inl_desc _ _ w)
  have h2 : ∀ u, φ.hom ((q.appLE W _ inf_le_right).hom u) = gmDual E q z W hzW u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inr_desc _ _ w)
  have hf : φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
      (P.presheaf.stalk z)).toRingHom = P.presheaf.germ _ z hz := by
    refine po.hom_ext (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
      (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
    · exact (congrArg TrivSqZeroExt.fst (h1 u)).trans (germ_appLE p z U _ inf_le_left hz u).symm
    · exact (congrArg TrivSqZeroExt.fst (h2 u)).trans (germ_appLE q z W _ inf_le_right hz u).symm
  have hf' : ∀ b, (φ.hom b).fst = (P.presheaf.germ _ z hz).hom b := fun b =>
    congrArg (fun φ => φ.hom b) hf
  letI := P.presheaf.algebra_section_stalk (⟨z, hz⟩ : (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W : P.Opens))
  have loc := hO.isLocalization_stalk ⟨z, hz⟩
  have hu : ∀ s : (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl, IsUnit (φ.hom s) := fun s => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf']
    exact IsLocalization.map_units (P.presheaf.stalk z) s
  let Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z) := IsLocalization.lift hu
  have hΦ : ∀ b, Φ ((P.presheaf.germ _ z hz).hom b) = φ.hom b := fun b =>
    IsLocalization.lift_eq hu b
  refine ⟨Φ, fun a => ?_, extend D p z Φ U hU hzU fun u => ?_, extend E q z Φ W hW hzW fun u => ?_⟩
  · have : (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
        (P.presheaf.stalk z)).toRingHom.comp Φ = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      refine RingHom.ext fun b => ?_
      exact (congrArg TrivSqZeroExt.fst (hΦ b)).trans (hf' b)
    exact congrArg (fun f => f a) this
  · rw [← germ_appLE p z U _ inf_le_left hz, hΦ, h1]
  · rw [← germ_appLE q z W _ inf_le_right hz, hΦ, h2]

end GlobalTheory.SS.StalkDer

namespace GlobalTheory.SS
open StalkDer in

theorem exists_stalk_derivation_of_isPullback : ∀ (K : Type) [Field K] (P X Y : Over (Sp K)) (p : P.left ⟶ X.left) (q : P.left ⟶ Y.left), IsPullback p q X.hom Y.hom → ∀ (D : VF X) (z : P.left), ∃ δ : P.left.presheaf.stalk z →+ P.left.presheaf.stalk z, (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(X.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom u)) = (P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom (D.D V u))) ∧ ∀ (V : Y.left.Opens) (W : P.left.Opens) (h : W ≤ q ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(Y.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((q.appLE V W h).hom u)) = 0 := by
  intro K _ P X Y p q H D z
  obtain ⟨Φ, h0, h1, h2⟩ := exists_dual p q H D (VF.zero Y) z
  refine ⟨⟨⟨fun x => (Φ x).snd, by simp⟩, fun a b => by simp⟩, fun a b => ?_,
    fun V W h hz u => ?_, fun V W h hz u => ?_⟩
  · show (Φ (a * b)).snd = a * (Φ b).snd + b * (Φ a).snd
    rw [map_mul, DualNumber.snd_mul, h0, h0]; ring
  · rw [germ_appLE, germ_appLE]
    exact congrArg TrivSqZeroExt.snd (h1 V (h hz) u)
  · rw [germ_appLE]
    exact (congrArg TrivSqZeroExt.snd (h2 V (h hz) u)).trans (map_zero (gm q z V (h hz)))
end GlobalTheory.SS
end
