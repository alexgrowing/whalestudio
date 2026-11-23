import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistLoc

section Glue

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_sec_of_cover (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) {I : Type} (V : I → Y.Opens)
    (hV : ∀ y, ∃ i, y ∈ V i) (p : I → K → L.ι) (hp : ∀ i, V i ≤ LB.wchart L φ (p i)) (a : ∀ i, Γ(Y, V i))
    (ha : ∀ i i' y, y ∈ V i → y ∈ V i' →
      gs (𝟙 Y) y _ (a i) = (trF φ ε (𝟙 Y) y (p i) (p i')).val * gs (𝟙 Y) y _ (a i')) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : I) (j : K → L.ι),
      r z ∈ V i → r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j (p i)).val * gs r z _ (a i) := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : I),
      r z ∈ V i → r z ∈ LB.wchart L φ j → gs r z _ s = (trF φ ε r z j (p i)).val * gs r z _ (a i) := by
    intro j
    let W : I → Y.Opens := fun i => LB.wchart L φ j ⊓ V i
    have le : ∀ i, W i ≤ LB.wchart L φ j ⊓ LB.wchart L φ (p i) := fun i => inf_le_inf_left _ (hp i)
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (u i) = (trF φ ε r z j (p i)).val * gs r z _ (a i) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom ((LB.LinComb L φ ε).g j (p i)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ V i)).op).hom (a i), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ (le i hz) _).trans
          (congrArg Units.val (gm_linComb L φ ε r z _ _ hz.1 (hp i hz.2))))) (gs_res r z _ hz _))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := hV y
        exact Opens.mem_iSup.2 ⟨i, hy, hi⟩) u
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, ha i i' y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hp i hy.1.2) (hp i' hy.2.2)])
    refine ⟨s, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W i)) (hs i)).trans (hu Z r z i hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i j => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := hV y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y i hi hy.1).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y i hi hy.2)).symm)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hp i hi), Units.val_mul, _root_.mul_assoc]; rfl

theorem exists_up_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ψ : K → (Y ⟶ X)} (hψ : ∀ k, φ' k ≫ F = ψ k) (ε : K → ℤ)
    (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s : LB.Sec (LB.LinComb L ψ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L ψ p) (s.f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
  choose u hu using fun p q => exists_pw w φ' ε p q
  let V : (K → L.ι) × (K → L'.ι) → Y.Opens := fun i =>
    LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(Y, V i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ V i →
      gs r z (V i) (v i) = (pw w φ' ε r z i.1 i.2).val * gs r z (LB.wchart L' φ' i.2) (a.f i.2) :=
    ⟨fun i => (u i.1 i.2).val * (Y.presheaf.map (homOfLE (inf_le_right : V i ≤ LB.wchart L' φ' i.2)).op).hom (a.f i.2),
      fun Z r z i hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
        ((gs_unit r z _ hz _).trans (congrArg Units.val (hu i.1 i.2 Z r z hz))) (gs_res r z _ hz _))⟩
  obtain ⟨s, hs⟩ := exists_sec_of_cover hL (fun k => φ' k ≫ F) ε V (fun y => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) (fun i => i.1) (fun i => inf_le_left) v
    (fun i i' y hi hi' => by
      rw [hv _ _ y i hi, hv _ _ y i' hi', sec_trans a (𝟙 Y) y hi.2 hi'.2,
        pw_trans hw φ' ε (𝟙 Y) y hi.1 hi'.1 hi.2 hi'.2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
        ← Units.val_mul, mul_right_comm _ _ (trF φ' ε (𝟙 Y) y i.2 i'.2), inv_mul_cancel_right])
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  rw [hs Z r z (p, q) p ⟨hp, hq⟩ hp, trF_self hL _ ε r z hp, Units.val_one, _root_.one_mul, hv Z r z (p, q) ⟨hp, hq⟩]

end Glue

section Loc

variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}

def cst (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : CommRingCat.of R ⟶ Γ(Y, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top

def gc (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (t : R) : Z.presheaf.stalk z :=
  gs π z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t)

theorem gc_mul (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (s t : R) : gc π z (s * t) = gc π z s * gc π z t := by
  rw [gc, map_mul, gs_mul π z ⊤ trivial]; rfl

theorem gs_cst (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (t : R) :
    gs r z U ((cst π U).hom t) = gc (r ≫ π) z t :=
  (gs_res r z (le_top : U ≤ π ⁻¹ᵁ ⊤) hz _).trans (gs_pull r π z ⊤ trivial _)

variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H

theorem isLocalization_app {U : Y.Opens} (hU : IsCompact (U : Set Y)) (hU' : IsQuasiSeparated (U : Set Y)) :
    letI := (h.app U).hom.toAlgebra
    IsLocalization (M.map (cst π U).hom) Γ(Y', h ⁻¹ᵁ U) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat Rm M)
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := h ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  have po' : IsPushout (cst π U) (CommRingCat.ofHom (algebraMap R Rm)) (h.app U) (cst π' (h ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of Rm)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [cst]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [cst]
  let := (h.app U).hom.toAlgebra
  let : Algebra R Γ(Y, U) := (cst π U).hom.toAlgebra
  let : Algebra Rm Γ(Y', h ⁻¹ᵁ U) := (cst π' (h ⁻¹ᵁ U)).hom.toAlgebra
  let : Algebra R Γ(Y', h ⁻¹ᵁ U) := (cst π U ≫ h.app U).hom.toAlgebra
  have : IsScalarTower R Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R Rm Γ(Y', h ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(po'.w).hom)
  exact (Algebra.isLocalization_iff_isPushout M Rm).mpr (CommRingCat.isPushout_iff_isPushout.mp po')

theorem exists_numerator {U : Y.Opens} (hU : IsAffineOpen U) (x : Γ(Y', h ⁻¹ᵁ U)) :
    ∃ t ∈ M, ∃ a : Γ(Y, U), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), h (r z) ∈ U →
      gs (r ≫ h) z U a = gc (r ≫ h ≫ π) z t * gs r z _ x := by
  let := (h.app U).hom.toAlgebra
  have := isLocalization_app M H hU.isCompact hU.isQuasiSeparated
  obtain ⟨⟨a, _, t, ht, rfl⟩, e⟩ := IsLocalization.surj (M.map (cst π U).hom) x
  refine ⟨t, ht, a, fun Z r z hz => ?_⟩
  have e' : (h.app U).hom a = x * (h.app U).hom ((cst π U).hom t) := e.symm
  rw [← gs_pull r h z U hz, e', gs_mul r z _ hz, gs_pull r h z U hz, gs_cst π (r ≫ h) z U hz, Category.assoc, mul_comm]

theorem exists_annihilator {U : Y.Opens} (hU : IsCompact (U : Set Y)) (hU' : IsQuasiSeparated (U : Set Y))
    (a b : Γ(Y, U)) (hab : ∀ y, h y ∈ U → gs h y U a = gs h y U b) :
    ∃ t ∈ M, ∀ y ∈ U, gc π y t * gs (𝟙 Y) y U a = gc π y t * gs (𝟙 Y) y U b := by
  let := (h.app U).hom.toAlgebra
  have := isLocalization_app M H hU hU'
  have e : algebraMap Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) a = algebraMap Γ(Y, U) Γ(Y', h ⁻¹ᵁ U) b := fn_ext fun y hy =>
    (gs_pull (𝟙 Y') h y U hy a).trans (Eq.trans (by rw [Category.id_comp]; exact hab y hy)
      (gs_pull (𝟙 Y') h y U hy b).symm)
  obtain ⟨⟨_, t, ht, rfl⟩, e'⟩ := IsLocalization.exists_of_eq (M := M.map (cst π U).hom) e
  refine ⟨t, ht, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 Y) y U) e'
  rw [gs_mul _ y U hy, gs_mul _ y U hy] at e''
  have c := gs_cst π (𝟙 Y) y U hy t
  rw [Category.id_comp] at c
  rw [← c]; exact e''

theorem exists_clear_denominator [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (r ≫ h) z (LB.wchart L φ j) (s.f j) =
        gc (r ≫ h ≫ π) z t * gs r z (LB.wchart L (fun k => h ≫ φ k) j) (s'.f j) := by
  classical
  have loc : ∀ y : Y, ∃ (p : K → L.ι) (V : Y.Opens), IsAffineOpen V ∧ y ∈ V ∧ V ≤ LB.wchart L φ p := fun y => by
    choose p hp using fun k => exists_chart hL (φ k y)
    obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ (LB.wchart L φ p : Set Y) from Set.mem_iInter.2 hp) (LB.wchart L φ p).isOpen
    exact ⟨p, V, hV, hy, hle⟩
  choose p V hV hy hle using loc
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set Y)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  have cov : ∀ y, ∃ i : S, y ∈ V i := fun y => by
    obtain ⟨i, hi, h'⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h'⟩
  have le' : ∀ i, h ⁻¹ᵁ V i ≤ LB.wchart L (fun k => h ≫ φ k) (p i) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hle i hy) k
  choose t ht a ha using fun i : S => exists_numerator M H (hV i)
    ((Y'.presheaf.map (homOfLE (le' i)).op).hom (s'.f (p i)))
  obtain ⟨T, hT, a', ha'⟩ : ∃ T ∈ M, ∃ a' : ∀ i : S, Γ(Y, V i), ∀ (i : S) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z),
      h (r z) ∈ V i → gs (r ≫ h) z (V i) (a' i) =
        gc (r ≫ h ≫ π) z T * gs r z (LB.wchart L (fun k => h ≫ φ k) (p i)) (s'.f (p i)) := by
    refine ⟨∏ i, t i, prod_mem fun i _ => ht i, fun i => (cst π _).hom (∏ j ∈ Finset.univ.erase i, t j) * a i,
      fun i Z r z hz => ?_⟩
    rw [gs_mul (r ≫ h) z _ hz, gs_cst π (r ≫ h) z _ hz, ha i Z r z hz, gs_res r z (le' i) hz (s'.f (p i)), Category.assoc,
      ← _root_.mul_assoc, ← gc_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have ov : ∀ i i' : S, ∃ u ∈ M, ∀ y, y ∈ V i → y ∈ V i' → gc π y u * gs (𝟙 Y) y _ (a' i) =
      gc π y u * ((trF φ ε (𝟙 Y) y (p i) (p i')).val * gs (𝟙 Y) y _ (a' i')) := fun i i' => by
    have lw : V i ⊓ V i' ≤ LB.wchart L φ (p i) ⊓ LB.wchart L φ (p i') := inf_le_inf (hle i) (hle i')
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V i ⊓ V i' → gs r z (V i ⊓ V i')
        ((Y.presheaf.map (homOfLE lw).op).hom ((LB.LinComb L φ ε).g (p i) (p i')).val *
          (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V i' ≤ V i')).op).hom (a' i')) =
        (trF φ ε r z (p i) (p i')).val * gs r z _ (a' i') := fun Z r z hz =>
      (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ (lw hz) _).trans
        (congrArg Units.val (gm_linComb L φ ε r z _ _ (lw hz).1 (lw hz).2)))) (gs_res r z _ hz _))
    obtain ⟨u, hu, e⟩ := exists_annihilator M H (U := V i ⊓ V i')
      (QuasiSeparatedSpace.inter_isCompact _ _ (V i).isOpen (hV i).isCompact (V i').isOpen (hV i').isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _)
      ((Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V i' ≤ V i)).op).hom (a' i)) _ (fun y hy => by
        refine (gs_res h y _ hy _).trans (Eq.trans ?_ (v _ h y hy).symm)
        have e₁ := ha' i _ (𝟙 Y') y hy.1
        have e₂ := ha' i' _ (𝟙 Y') y hy.2
        have e₃ := SecPull.trF_comp (L := L) (F := 𝟙 X) (φ' := fun k => h ≫ φ k) (φ := φ) (h := h)
          (fun k => Category.comp_id _) ε (𝟙 Y') y (p i) (p i')
        simp only [Category.id_comp, Category.comp_id] at e₁ e₂ e₃
        rw [e₁, e₂, sec_trans s' (𝟙 Y') y (le' i hy.1) (le' i' hy.2), e₃, mul_left_comm])
    refine ⟨u, hu, fun y h₁ h₂ => ?_⟩
    have e' := e y ⟨h₁, h₂⟩
    rwa [v _ (𝟙 Y) y ⟨h₁, h₂⟩, gs_res (𝟙 Y) y (inf_le_left : V i ⊓ V i' ≤ V i) ⟨h₁, h₂⟩] at e'
  choose u hu hov using ov
  let U : R := ∏ q : S × S, u q.1 q.2
  obtain ⟨s, hs⟩ := exists_sec_of_cover hL φ ε (fun i : S => V i) cov (fun i => p i) (fun i => hle i)
    (fun i => (cst π _).hom U * a' i) (fun i i' y h₁ h₂ => by
      obtain ⟨c, hc⟩ : u i i' ∣ U := Finset.dvd_prod_of_mem (fun q : S × S => u q.1 q.2) (Finset.mem_univ (i, i'))
      rw [gs_mul _ y _ h₁, gs_mul _ y _ h₂, gs_cst π _ y _ h₁, gs_cst π _ y _ h₂, Category.id_comp, hc, mul_comm _ c,
        gc_mul, _root_.mul_assoc, hov i i' y h₁ h₂]
      ring)
  refine ⟨U * T, mul_mem (prod_mem fun q _ => hu q.1 q.2) hT, s, fun Z r z j hj => ?_⟩
  obtain ⟨i, hi⟩ := cov (h (r z))
  have e₃ := SecPull.trF_comp (L := L) (F := 𝟙 X) (φ' := fun k => h ≫ φ k) (φ := φ) (h := h)
    (fun k => Category.comp_id _) ε r z j (p i)
  simp only [Category.comp_id] at e₃
  rw [hs Z (r ≫ h) z i j hi (wchart_comp_le L φ h j hj), gs_mul (r ≫ h) z _ hi, gs_cst π (r ≫ h) z _ hi,
    ha' i Z r z hi, sec_trans s' r z hj (le' i hi), e₃, gc_mul, Category.assoc]
  ring

end Loc

section Basis

variable {X X' Y Y₁ Y₂ T Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K] {m : ℕ}

def IsComb (π : Y ⟶ T) {N : LB Y} (b : Fin m → LB.Sec N) (s : LB.Sec N) (c : Fin m → Γ(T, ⊤)) : Prop :=
  ∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (π.appTop.hom (c i)) * (b i).f j

theorem gs_comb (π : Y ⟶ T) (U : Y.Opens) (c : Fin m → Γ(T, ⊤)) (a : Fin m → Γ(Y, U)) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ U) : gs r z U (∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (π.appTop.hom (c i)) * a i) =
      ∑ i, gs (r ≫ π) z ⊤ (c i) * gs r z U (a i) := by
  rw [gs_eq r z U hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z U hz, gs_mul r z U hz]
  exact congrArg (· * _) ((gs_res r z (le_top : U ≤ π ⁻¹ᵁ ⊤) hz _).trans (gs_pull r π z ⊤ trivial _))

theorem IsComb.gs {π : Y ⟶ T} {N : LB Y} {b : Fin m → LB.Sec N} {s : LB.Sec N} {c : Fin m → Γ(T, ⊤)}
    (h : IsComb π b s c) (r : Z ⟶ Y) (z : Z) (j : N.ι) (hz : r z ∈ N.U j) :
    gs r z (N.U j) (s.f j) = ∑ i, gs (r ≫ π) z ⊤ (c i) * gs r z (N.U j) ((b i).f j) := by
  rw [h j, gs_comb π _ c _ r z hz]

theorem isComb_of_gs {π : Y ⟶ T} {N : LB Y} {b : Fin m → LB.Sec N} {s : LB.Sec N} {c : Fin m → Γ(T, ⊤)}
    (h : ∀ y j, y ∈ N.U j →
      gs (𝟙 Y) y (N.U j) (s.f j) = ∑ i, gs (𝟙 Y ≫ π) y ⊤ (c i) * gs (𝟙 Y) y (N.U j) ((b i).f j)) :
    IsComb π b s c := fun j => fn_ext fun y hy => (h y j hy).trans (gs_comb π _ c _ (𝟙 Y) y hy).symm

theorem basis_transport {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    (θ : Y₁ ≅ Y₂) (π₁ : Y₁ ⟶ T) (π₂ : Y₂ ⟶ T) (hπ : θ.hom ≫ π₂ = π₁) (ψ₁ : K → (Y₁ ⟶ X)) (ψ₂ : K → (Y₂ ⟶ X'))
    (hψ : ∀ k, θ.hom ≫ ψ₂ k ≫ F = ψ₁ k) (ε : K → ℤ) (b₁ : Fin m → LB.Sec (LB.LinComb L ψ₁ ε))
    (b₂ : Fin m → LB.Sec (LB.LinComb L' ψ₂ ε)) (u : Fin m → Γ(T, ⊤)) (hu : ∀ i, IsUnit (u i))
    (hb : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L ψ₁ p →
      (r ≫ θ.hom) z ∈ LB.wchart L' ψ₂ q → gs r z (LB.wchart L ψ₁ p) ((b₁ i).f p) =
        gs (r ≫ π₁) z ⊤ (u i) * ((pw w ψ₂ ε (r ≫ θ.hom) z p q).val * gs (r ≫ θ.hom) z (LB.wchart L' ψ₂ q) ((b₂ i).f q)))
    (h₂ : ∀ s, ∃! c, IsComb π₂ b₂ s c) (s : LB.Sec (LB.LinComb L ψ₁ ε)) : ∃! c, IsComb π₁ b₁ s c := by
  have hc : ∀ k, ψ₂ k ≫ F = θ.inv ≫ ψ₁ k := fun k => by rw [← hψ, Iso.inv_hom_id_assoc]
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull X X' Y₁ Y₂ L L' F hL hL' w hw K ψ₂ ψ₁ ε θ.inv hc s
  obtain ⟨c, hc₂, uniq⟩ := h₂ a
  choose v hv using fun i => (hu i).exists_right_inv
  refine ⟨fun i => c i * v i, isComb_of_gs fun y p hy => ?_, fun c' hc' => ?_⟩
  · choose q hq using fun k => exists_chart hL' (ψ₂ k ((𝟙 Y₁ ≫ θ.hom) y))
    have mq : (𝟙 Y₁ ≫ θ.hom) y ∈ LB.wchart L' ψ₂ q := Set.mem_iInter.2 hq
    have e := ha _ (𝟙 Y₁ ≫ θ.hom) y p q (fun k => by
      show (θ.hom ≫ ψ₂ k ≫ F) y ∈ L.U (p k)
      rw [hψ]; exact Set.mem_iInter.1 hy k) hq
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at e
    refine e.trans ?_
    refine (congrArg (_ * ·) (hc₂.gs (𝟙 Y₁ ≫ θ.hom) y q mq)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ?_ (congrArg (_ * ·) (hb i _ (𝟙 Y₁) y p q hy mq)).symm
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← gs_mul _ y ⊤ trivial, _root_.mul_assoc (c i), mul_comm (v i), hv,
      _root_.mul_one, Category.assoc, hπ, mul_comm _ (gs _ y ⊤ (c i)), _root_.mul_assoc]
    rfl
  · have e : IsComb π₂ b₂ a (fun i => c' i * u i) := isComb_of_gs fun y q hy => by
      choose p hp using fun k => exists_chart hL (F (ψ₂ k y))
      have i₁ : θ.inv ≫ θ.hom = 𝟙 Y₂ := θ.inv_hom_id
      have mp : θ.inv y ∈ LB.wchart L ψ₁ p := Set.mem_iInter.2 fun k => by
        show (θ.inv ≫ ψ₁ k) y ∈ L.U (p k)
        rw [← hc]; exact hp k
      have e₁ := ha _ (𝟙 Y₂) y p q hp (Set.mem_iInter.1 hy)
      rw [Category.id_comp] at e₁
      have e₂ := hc'.gs θ.inv y p mp
      have e₃ := fun i => hb i _ θ.inv y p q mp (by rw [i₁]; exact hy)
      have hπ' : θ.inv ≫ π₁ = 𝟙 Y₂ ≫ π₂ := by rw [← hπ, Iso.inv_hom_id_assoc, Category.id_comp]
      rw [i₁] at e₃
      refine (Units.mul_right_inj (pw w ψ₂ ε (𝟙 Y₂) y p q)).1 (e₁.symm.trans (e₂.trans ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => (congrArg (_ * ·) (e₃ i)).trans ?_
      rw [hπ', gs_mul _ y ⊤ trivial, ← _root_.mul_assoc, mul_left_comm]
      rfl
    have e' := uniq _ e
    funext i
    rw [← e', _root_.mul_assoc, hv, _root_.mul_one]

end Basis

section Main

theorem fam_comm {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') (x : D'.X) (k : Fin 4) :
    D'.famφB x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) k := by
  have gp := pull_grp hD
  have he := hD.he
  have hc := hD.c_pr x
  generalize hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = F at gp he hc ⊢
  have pt : ∀ (y' : 𝟙_ _ ⟶ D'.P.A) (y : 𝟙_ _ ⟶ D.P.A), y'.left ≫ F = specOf φ ≫ y.left →
      (toUnit D'.P.A ≫ y').left ≫ F = F ≫ (toUnit D.P.A ≫ y).left := fun y' y e => by
    show (D'.P.A.hom ≫ y'.left) ≫ F = F ≫ D.P.A.hom ≫ y.left
    rw [Category.assoc, e, ← Category.assoc, ← gp.1.w, Category.assoc]
  fin_cases k
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · let U : Over.mk (D'.P.A.hom ≫ spMap φ) ⟶ D.P.A := Over.homMk F gp.1.w
    have m := gp.2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) (U ≫ 𝟙 _) (U ≫ toUnit _ ≫ D.c (hD.xe x))
      ((Category.comp_id _).trans (Category.id_comp _).symm) (pt _ _ hc).symm
    rw [← MonObj.comp_mul] at m
    exact m.symm
  · exact pt _ _ hc
  · exact pt _ _ he

theorem exists_basis_off_prime : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
  intro hP _ hT R _ _ _ D ⟨W, hW, hψ⟩ p _ k hk α
  let Rp := Localization.AtPrime p
  have inj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp p.primeCompl_le_nonZeroDivisors
  obtain ⟨D', hD, -, hg⟩ := DegPull.exists_isPullDeg hP R Rp (algebraMap R Rp) D W hψ (by
    have : (specOf (algebraMap R Rp)).base (genericPoint (Spec (CommRingCat.of Rp))) =
        genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      exact Ideal.comap_bot_of_injective _ inj
    rw [this]; exact hW)
  obtain ⟨α', rfl⟩ := hD.xe.surjective α
  obtain ⟨m, b₀, hm, hb₀⟩ := hT Rp D' k hk α'
  rw [hg] at hm
  subst hm
  have gp := pull_grp hD
  have hw := hD.w_gen
  have hφ := fam_comm hD α'
  generalize hD.w = w at hw
  generalize hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (algebraMap R Rp)) = F at gp w hw hφ
  have := D.P.isAb.proper
  have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
  have : QuasiSeparatedSpace D.P.A.left := (quasiSeparated_iff_quasiSeparatedSpace D.P.A.hom).mp inferInstance
  choose a ha using fun i => exists_up_sec ((isGen_iff w).1 hw) D.P.isLB D'.P.isLB hφ (DegPre.famε k) (b₀ i)
  choose t ht b hb using fun i => exists_clear_denominator p.primeCompl gp.1 D.P.isLB _ _ (a i)
  refine ⟨b, fun R' _ f hf b' hb' => ?_⟩
  let g : Rp →+* R' := IsLocalization.lift (M := p.primeCompl) (g := f) fun s => hf s.1 s.2
  have hfg : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Rp)) =
      Spec.map (CommRingCat.ofHom f) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]
  let T₁ : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let T₂ : Over (Spec (CommRingCat.of Rp)) := Over.mk (Spec.map (CommRingCat.ofHom g))
  have H₁ : IsPullback (snd T₁ D.P.A).left (fst T₁ D.P.A).left D.P.A.hom (Spec.map (CommRingCat.ofHom f)) :=
    (IsPullback.of_hasPullback T₁.hom D.P.A.hom).flip
  have H₂ : IsPullback ((snd T₂ D'.P.A).left ≫ F) (fst T₂ D'.P.A).left D.P.A.hom (Spec.map (CommRingCat.ofHom f)) := by
    rw [← hfg]
    exact (IsPullback.of_hasPullback T₂.hom D'.P.A.hom).flip.paste_horiz gp.1
  let θ := H₁.isoIsPullback _ _ H₂
  have θ₁ : θ.hom ≫ (snd T₂ D'.P.A).left ≫ F = (snd T₁ D.P.A).left := H₁.isoIsPullback_hom_fst _ _ H₂
  have θ₂ : θ.hom ≫ (fst T₂ D'.P.A).left = (fst T₁ D.P.A).left := H₁.isoIsPullback_hom_snd _ _ H₂
  refine basis_transport hw D.P.isLB D'.P.isLB θ _ _ θ₂ _ (fun i => (snd T₂ D'.P.A).left ≫ D'.famφB α' i)
    (fun i => by rw [Category.assoc, hφ, ← θ₁]; simp only [Category.assoc]) _ b'
    (fun i => DVR.pullSec _ _ _ (b₀ i) (snd T₂ D'.P.A).left)
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f (t i))) (fun i => (hf _ (ht i)).map _)
    (fun i Z r z j q hj hq => ?_) (hb₀ R' g _ fun i j => rfl)
  have mj : (r ≫ (snd T₁ D.P.A).left) z ∈ LB.wchart D.P.L (D.famφB (hD.xe α')) j :=
    wchart_comp_le _ _ (snd T₁ D.P.A).left j hj
  have mq : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) z ∈ LB.wchart D'.P.L (D'.famφB α') q :=
    wchart_comp_le _ _ (snd T₂ D'.P.A).left q hq
  have er : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) ≫ F = r ≫ (snd T₁ D.P.A).left := by
    rw [← θ₁]; simp only [Category.assoc]
  have mj' : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) z ∈
      LB.wchart D.P.L (fun κ => F ≫ D.famφB (hD.xe α') κ) j := Set.mem_iInter.2 fun κ => by
    show ((((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) ≫ F) ≫ D.famφB (hD.xe α') κ) z ∈ D.P.L.U (j κ)
    rw [er]; exact Set.mem_iInter.1 mj κ
  have e₁ := hb i Z _ z j mj'
  rw [er, ha i Z _ z j q mj' mq] at e₁
  refine (congrArg (gs r z _) (hb' i j)).trans ((gs_res r z _ hj _).trans ((gs_pull r _ z _ mj _).trans
    (e₁.trans (congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)))))
  · rw [← Category.assoc, er, Category.assoc, H₁.w, ← Category.assoc, gc, ← gs_pull _ _ z ⊤ trivial]
    exact congrArg (gs _ z ⊤) congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).hom (t i)).symm
  · simp only [pw, Category.assoc]
  · exact ((gs_res _ z _ hq _).trans (gs_pull _ _ z _ mq _)).symm

end Main

end GlobalTheory.TwistLoc
