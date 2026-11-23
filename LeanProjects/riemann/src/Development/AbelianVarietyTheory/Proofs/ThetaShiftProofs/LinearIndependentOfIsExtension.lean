import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {X X' Y Y' Z : Scheme.{0}}

theorem exists_sec_transfer {A B : LB Y} (hB : ∀ y, ∃ q, y ∈ B.U q) (u : ∀ p q, Γ(Y, A.U p ⊓ B.U q)ˣ)
    (h₁ : ∀ (y : Y) p q q', y ∈ A.U p → y ∈ B.U q → y ∈ B.U q' →
      gm (𝟙 Y) y _ (u p q) * gm (𝟙 Y) y _ (B.g q q') = gm (𝟙 Y) y _ (u p q'))
    (h₂ : ∀ (y : Y) p p' q, y ∈ A.U p → y ∈ A.U p' → y ∈ B.U q →
      gm (𝟙 Y) y _ (u p q) = gm (𝟙 Y) y _ (A.g p p') * gm (𝟙 Y) y _ (u p' q)) (b : LB.Sec B) :
    ∃ a : LB.Sec A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ A.U p → r z ∈ B.U q →
      gs r z _ (a.f p) = (gm r z _ (u p q)).val * gs r z _ (b.f q) := by
  have hb : ∀ (y : Y) q q', y ∈ B.U q → y ∈ B.U q' →
      gs (𝟙 Y) y _ (b.f q) = (gm (𝟙 Y) y _ (B.g q q')).val * gs (𝟙 Y) y _ (b.f q') := fun y q q' hq hq' => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U q ⊓ B.U q' := ⟨hq, hq'⟩
    exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs _ y _) (b.compat q q')).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))
  have glue : ∀ p, ∃ s : Γ(Y, A.U p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ A.U p → r z ∈ B.U q →
      gs r z _ s = (gm r z _ (u p q)).val * gs r z _ (b.f q) := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ A.U p ⊓ B.U q →
        gs r z (A.U p ⊓ B.U q) ((u p q).val * (Y.presheaf.map (homOfLE inf_le_right).op).hom (b.f q)) =
          (gm r z _ (u p q)).val * gs r z _ (b.f q) := fun Z r z q hz =>
      (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun q => A.U p ⊓ B.U q) (A.U p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨q, hq⟩ := hB y
        exact Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (u p q).val * (Y.presheaf.map (homOfLE inf_le_right).op).hom (b.f q))
      (fun q q' => fn_ext (V := (A.U p ⊓ B.U q) ⊓ (A.U p ⊓ B.U q')) fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        refine (hv _ (𝟙 Y) y q hy.1).trans (Eq.trans ?_ (hv _ (𝟙 Y) y q' hy.2).symm)
        rw [hb y q q' hy.1.2 hy.2.2, ← mul_assoc, ← Units.val_mul,
          h₁ y p q q' hy.1.1 hy.1.2 hy.2.2])
    refine ⟨s, fun Z r z q a₁ a₂ => ?_⟩
    have hz : r z ∈ A.U p ⊓ B.U q := ⟨a₁, a₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun p p' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  obtain ⟨q, hq⟩ := hB y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [hs p _ _ y q hy.1 hq, hs p' _ _ y q hy.2 hq, h₂ y p p' q hy.1 hy.2 hq, Units.val_mul, mul_assoc]

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (y : Y) : ∃ j, y ∈ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k y)
  exact ⟨j, Set.mem_iInter.2 hj⟩

theorem exists_good' (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

theorem exists_sec_up {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ t : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  obtain ⟨t, ht⟩ := exists_sec_transfer (A := LB.LinComb L (fun k => φ' k ≫ F) ε) (B := LB.LinComb L' φ' ε)
    (exists_wchart hL' φ') u (fun y p q q' hp hq hq' => by
      refine (congrArg₂ (· * ·) (hu p q _ (𝟙 Y) y ⟨hp, hq⟩) (gm_linComb L' φ' ε (𝟙 Y) y q q' hq hq')).trans
        (Eq.trans ?_ (hu p q' _ (𝟙 Y) y ⟨hp, hq'⟩).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp hq hq', trF_self hL _ ε (𝟙 Y) y hp, one_mul]
      exact inv_mul_cancel_comm _ _) (fun y p p' q hp hp' hq => by
      refine (hu p q _ (𝟙 Y) y ⟨hp, hq⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
        (gm_linComb L _ ε (𝟙 Y) y p p' hp hp') (hu p' q _ (𝟙 Y) y ⟨hp', hq⟩)).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp' hq hq, trF_self hL' _ ε (𝟙 Y) y hq, inv_one, mul_one]
      rfl) a
  exact ⟨t, fun Z r z p q hp hq => (ht Z r z p q hp hq).trans
    (congrArg (fun v : (Z.presheaf.stalk z)ˣ => v.val * _) (hu p q Z r z ⟨hp, hq⟩))⟩

theorem exists_sec_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (t : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have hu' : ∀ q p (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L' φ' q →
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
      gm r z (LB.wchart L' φ' q ⊓ LB.wchart L (fun k => φ' k ≫ F) p) (res (inf_comm _ _).le (u p q))⁻¹ =
        (pw w φ' ε r z p q)⁻¹ := fun q p Z r z hq hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ (show r z ∈ LB.wchart L' φ' q ⊓
      LB.wchart L (fun k => φ' k ≫ F) p from ⟨hq, hp⟩) _).trans (hu p q Z r z ⟨hp, hq⟩)))
  obtain ⟨a, ha⟩ := exists_sec_transfer (B := LB.LinComb L (fun k => φ' k ≫ F) ε) (A := LB.LinComb L' φ' ε)
    (exists_wchart hL _) (fun q p => (res (inf_comm _ _).le (u p q))⁻¹) (fun y q p p' hq hp hp' => by
      refine (congrArg₂ (· * ·) (hu' q p _ (𝟙 Y) y hq hp) (gm_linComb L _ ε (𝟙 Y) y p p' hp hp')).trans
        (Eq.trans ?_ (hu' q p' _ (𝟙 Y) y hq hp').symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp' hq hq, trF_self hL' _ ε (𝟙 Y) y hq, inv_one, mul_one, mul_inv]
      exact inv_mul_cancel_comm _ _) (fun y q q' p hq hq' hp => by
      refine (hu' q p _ (𝟙 Y) y hq hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
        (gm_linComb L' _ ε (𝟙 Y) y q q' hq hq') (hu' q' p _ (𝟙 Y) y hq' hp)).symm)
      rw [pw_trans hw φ' ε (𝟙 Y) y hp hp hq hq', trF_self hL _ ε (𝟙 Y) y hp, one_mul, mul_inv, inv_inv]
      rfl) t
  refine ⟨a, fun Z r z p q hp hq => ?_⟩
  have e := (ha Z r z q p hq hp).trans
    (congrArg (fun v : (Z.presheaf.stalk z)ˣ => v.val * _) (hu' q p Z r z hq hp))
  exact ((Units.eq_inv_mul_iff_mul_eq _).1 e).symm

def SecThrough (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (t : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι), (∀ k, F (φ' k (r z)) ∈ L.U (p k)) →
    (∀ k, φ' k (r z) ∈ L'.U (q k)) →
    gs (r ≫ h) z (LB.wchart L φ p) (t.f p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L' φ' q) (a.f q)

def wVal (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem SecThrough.sval (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Sec (LB.LinComb L' φ' ε)}
    {t : LB.Sec (LB.LinComb L φ ε)} (H : SecThrough w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : sval t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k).val * sval a r z J' := by
  rw [sval_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hψ])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem pmaps_val (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hψ])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem SecThrough.unique (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a a' : LB.Sec (LB.LinComb L' φ' ε)} {t : LB.Sec (LB.LinComb L φ ε)} (H : SecThrough w φ' φ ε a t h)
    (H' : SecThrough w φ' φ ε a' t h) : a = a' := sec_ext' hL' fun y J' hJ' => by
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_right_inj _).1 ((H.sval hψ _ hJ hJ').symm.trans (H'.sval hψ _ hJ hJ'))

theorem exists_secThrough (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Sec (LB.LinComb L φ ε)) : ∃ a, SecThrough w φ' φ ε a t h := by
  have e : (fun k => φ' k ≫ F) = fun k => h ≫ φ k := funext hψ
  have ex : ∃ t' : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → gs r z (LB.wchart L (fun k => φ' k ≫ F) p) (t'.f p) =
        gs (r ≫ h) z (LB.wchart L φ p) (t.f p) := by
    rw [e]
    exact ⟨ReciprocityTheory.ChartRestriction.G.DVR.pullSec L φ ε t h, fun Z r z p hp => (gs_res r z _ hp _).trans
      (gs_pull r h z _ (Out.wchart_comp_le L φ h p hp) _)⟩
  obtain ⟨t', ht'⟩ := ex
  obtain ⟨a, ha⟩ := exists_sec_down ((isGen_iff w).1 hw) hL hL' t'
  exact ⟨a, fun Z r z p q hp hq => (ht' Z r z p (Set.mem_iInter.2 hp)).symm.trans
    (ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq))⟩

theorem exists_gen_through (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
        val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨s, hs⟩ := exists_secThrough hw hL hL' hψ (Geo.Tor.genSec t ht)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hL' s y j hy
    obtain ⟨J, hJ⟩ := exists_good' hL y
    have e' := hs.sval hψ (𝟙 _) hJ hJ'
    rw [sval_genSec t ht _ y hJ] at e'
    rw [← (Units.inv_mul_eq_iff_eq_mul _).2 e', ← Units.val_mul, ← Units.val_mul] at e
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart L' φ' j) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun Z r z J J' hJ hJ' => Units.ext ?_⟩
  refine (sval_genSec t ht _ z hJ).symm.trans ((hs.sval hψ r hJ hJ').trans ?_)
  rw [Units.val_mul]
  exact congrArg _ (gs_unit r z _ (hJ'.mem φ' r) (hu _).unit)

section Linear

variable {R R' : Type} [CommRing R] [CommRing R'] {π : Y ⟶ Spec (CommRingCat.of R)}
  {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'}

def pullThrough (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (ε : K → ℤ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) :
    SecOver π (LB.LinComb L φ ε) →ₛₗ[f] SecOver π' (LB.LinComb L' φ' ε) where
  toFun t := (exists_secThrough hw hL hL' hψ t).choose
  map_add' s t := sec_ext' hL' fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    refine ((exists_secThrough hw hL hL' hψ _).choose_spec.sval hψ _ hJ hJ').symm.trans ((sval_add' hJ _ s t).trans
      (Eq.trans ?_ (congrArg _ (sval_add' (π := π') hJ' _ _ _).symm)))
    rw [mul_add, ← (exists_secThrough hw hL hL' hψ s).choose_spec.sval hψ _ hJ hJ',
      ← (exists_secThrough hw hL hL' hψ t).choose_spec.sval hψ _ hJ hJ']
  map_smul' c s := sec_ext' hL' fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    refine ((exists_secThrough hw hL hL' hψ _).choose_spec.sval hψ _ hJ hJ').symm.trans ((sval_smul' hJ _ c s).trans
      (Eq.trans ?_ (congrArg _ (sval_smul' (π := π') hJ' _ _ _).symm)))
    rw [mul_left_comm, ← (exists_secThrough hw hL hL' hψ s).choose_spec.sval hψ _ hJ hJ', Category.assoc, hp,
      ← Category.assoc, constVal_specMap]

variable (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
  (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f))

theorem secThrough_pullThrough (t : SecOver π (LB.LinComb L φ ε)) :
    SecThrough w φ' φ ε (pullThrough hw hL hL' hψ ε hp t) t h := (exists_secThrough hw hL hL' hψ t).choose_spec

theorem sval_pullThrough (t : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : sval t (r ≫ h) z J =
      (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k).val * sval (pullThrough hw hL hL' hψ ε hp t) r z J' :=
  (secThrough_pullThrough hw hL hL' hψ hp t).sval hψ r hJ hJ'

end Linear

theorem isExtension_comp {k E : Type} [Field k] [Field E] [Algebra k E] {V W W' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module E W] [AddCommGroup W'] [Module E W'] {a : V →ₛₗ[algebraMap k E] W}
    (ha : IsExtension a) (θ : W →ₗ[E] W') (hθ : Function.Bijective θ) (a' : V →ₛₗ[algebraMap k E] W')
    (e : ∀ v, a' v = θ (a v)) : IsExtension a' := by
  constructor
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x, rfl⟩ := hθ.2 x
    obtain ⟨n, c, v, rfl⟩ := ha.exists_sum x
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, e _⟩)
  · intro ℓ
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    refine ⟨Λ.comp (LinearEquiv.ofBijective θ hθ).symm.toLinearMap.toAddMonoidHom, fun c v => ?_⟩
    have : (LinearEquiv.ofBijective θ hθ).symm (c • a' v) = c • a v := by
      rw [LinearEquiv.symm_apply_eq, map_smul, e]; rfl
    exact (congrArg Λ this).trans (hΛ c v)

theorem linearIndependent_of_isExtension {k E : Type} [Field k] [Field E] [Algebra k E] {V W : Type} [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module E W] {a : V →ₛₗ[algebraMap k E] W} (ha : IsExtension a) {ι : Type*}
    {v : ι → V} (hv : LinearIndependent k v) : LinearIndependent E (fun i => a (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S c hc i hi
  refine (Module.forall_dual_apply_eq_zero_iff k (c i)).1 fun ℓ => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  refine hv S (fun i => ℓ (c i)) ?_ i hi
  have := congrArg Λ hc
  rw [map_sum, map_zero] at this
  exact (Finset.sum_congr rfl fun i _ => (hΛ _ _).symm).trans this

theorem isExtension_pullThrough {k E : Type} [Field k] [Field E] [Algebra k E] {π : Y ⟶ Spec (CommRingCat.of k)}
    {π' : Y' ⟶ Spec (CommRingCat.of E)} (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    [NoetherianSpace Y] (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) :
    IsExtension (pullThrough hw hL hL' hψ ε H.w) := by
  have hid : 𝟙 Y' ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (RingHom.id E)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  have hψ' : ∀ k, φ' k ≫ F = 𝟙 Y' ≫ φ' k ≫ F := fun k => (Category.id_comp _).symm
  let θ := pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' ε hid
  refine isExtension_comp (isExtension_pullOver H hL ε hψ) θ ⟨?_, fun a => ?_⟩ _ fun t => ?_
  · refine (injective_iff_map_eq_zero θ).2 fun t ht => sec_ext' hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := exists_good' hL' y
    have e := sval_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid t (𝟙 _) hJ hJ'
    rw [Category.id_comp] at e
    rw [e, show pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' ε hid t = 0 from ht, sval_zero' hJ',
      sval_zero' hJ, mul_zero]
  · obtain ⟨t, ht⟩ := exists_sec_up ((isGen_iff w).1 hw) hL hL' a
    refine ⟨t, (secThrough_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid t).unique hL hL' hψ'
      fun Z r z p q hp hq => ?_⟩
    rw [Category.comp_id]
    exact ht Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  · refine sec_ext' hL' fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := exists_good' hL y
    refine (Units.mul_right_inj (∏ k, wVal w y J J' (𝟙 Y' ≫ φ' k) ^ ε k)).1 ?_
    rw [← sval_pullThrough hw hL hL' hψ H.w t _ hJ hJ',
      ← sval_pullThrough (φ := fun k => φ' k ≫ F) hw hL hL' hψ' hid _ _ hJ hJ', sval_pullOver H.w hψ t _ hJ,
      Category.comp_id]

end GlobalTheory.ConstFam
