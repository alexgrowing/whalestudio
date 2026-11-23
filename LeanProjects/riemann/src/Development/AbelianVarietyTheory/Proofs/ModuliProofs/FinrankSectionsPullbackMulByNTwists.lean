import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyEquivPiOfWeights
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.TwistSplit

open GlobalTheory.MulSplit GlobalTheory.SecDim

section General

variable {K : Type} [Field K] {X Y Z : Scheme.{0}} {M N : LB X} {q : Y ⟶ X}

theorem gm_pull_g (r : Z ⟶ Y) (z : Z) (j j' : PUnit → M.ι) (hj : r z ∈ (M.pull q).U j)
    (hj' : r z ∈ (M.pull q).U j') :
    gm r z ((M.pull q).U j ⊓ (M.pull q).U j') ((M.pull q).g j j') =
      gm (r ≫ q) z (M.U (j .unit) ⊓ M.U (j' .unit)) (M.g (j .unit) (j' .unit)) :=
  (gm_linComb M _ _ r z j j' hj hj').trans ((Fintype.prod_unique _).trans (zpow_one _))

theorem chart_le {τ : Y ⟶ Y} (h : τ ≫ q = q) (j : PUnit → M.ι) : (M.pull q).U j ≤ τ ⁻¹ᵁ (M.pull q).U j :=
  fun y hy => mem_pull.2 ((congrArg (fun t => t y ∈ M.U (j .unit)) h).mpr (mem_pull.1 hy))

def pv (s : (M.pull q).Sec) (r : Z ⟶ Y) (z : Z) (i : M.ι) : Z.presheaf.stalk z :=
  gs r z ((M.pull q).U fun _ => i) (s.f fun _ => i)

theorem pv_compat (s : (M.pull q).Sec) (r : Z ⟶ Y) (z : Z) {i i' : M.ι} (h : q (r z) ∈ M.U i)
    (h' : q (r z) ∈ M.U i') : pv s r z i = (gm (r ≫ q) z (M.U i ⊓ M.U i') (M.g i i')).val * pv s r z i' :=
  (gs_compat s r z (j := fun _ => i) (j' := fun _ => i') (mem_pull.2 h) (mem_pull.2 h')).trans
    (congrArg (fun w : (Z.presheaf.stalk z)ˣ => w.val * pv s r z i')
      (gm_pull_g r z (fun _ => i) (fun _ => i') (mem_pull.2 h) (mem_pull.2 h')))

theorem pull_ext {s t : (M.pull q).Sec} (h : ∀ (y : Y) i, q y ∈ M.U i → pv s (𝟙 Y) y i = pv t (𝟙 Y) y i) : s = t :=
  lbSec_ext fun j => fn_ext fun y hy => h y (j .unit) (mem_pull.1 hy)

def tr {τ : Y ⟶ Y} (h : τ ≫ q = q) (s : (M.pull q).Sec) : (M.pull q).Sec where
  f j := (τ.appLE _ _ (chart_le h j)).hom (s.f j)
  compat j j' := fn_ext fun y hy => by
    have h1 : (𝟙 Y ≫ τ) y ∈ (M.pull q).U j := chart_le h j hy.1
    have h2 : (𝟙 Y ≫ τ) y ∈ (M.pull q).U j' := chart_le h j' hy.2
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gs_appLE _ _ _ _ _ y hy.1,
      gs_appLE _ _ _ _ _ y hy.2, gm_pull_g (𝟙 Y) y j j' hy.1 hy.2, gs_compat s (𝟙 Y ≫ τ) y h1 h2,
      gm_pull_g (𝟙 Y ≫ τ) y j j' h1 h2, Category.assoc, h]

theorem pv_tr {τ : Y ⟶ Y} (h : τ ≫ q = q) (s : (M.pull q).Sec) (r : Z ⟶ Y) (z : Z) {i : M.ι}
    (hi : q (r z) ∈ M.U i) : pv (tr h s) r z i = pv s (r ≫ τ) z i :=
  gs_appLE _ _ _ (chart_le h fun _ => i) r z (mem_pull.2 hi) _

theorem gs_smul (p : X ⟶ Sp K) (a : K) (s : M.Sec) (r : Z ⟶ X) (z : Z) (j : M.ι) (hj : r z ∈ M.U j) :
    gs r z _ ((constHom p a • s).f j) = cst (r ≫ p) z a * gs r z _ (s.f j) := by
  rw [GlobalTheory.LB.smul_f, gs_mul _ z _ hj, resG_constHom, gs_constFn _ _ _ _ hj]

theorem pv_smul (p : Y ⟶ Sp K) (a : K) (s : (M.pull q).Sec) (r : Z ⟶ Y) (z : Z) {i : M.ι} (hi : q (r z) ∈ M.U i) :
    pv (constHom p a • s) r z i = cst (r ≫ p) z a * pv s r z i :=
  gs_smul p a s r z (fun _ => i) (mem_pull.2 hi)

theorem pv_add (s t : (M.pull q).Sec) (r : Z ⟶ Y) (z : Z) {i : M.ι} (hi : q (r z) ∈ M.U i) :
    pv (s + t) r z i = pv s r z i + pv t r z i :=
  gs_add r z ((M.pull q).U fun _ => i) (mem_pull.2 hi) _ _

theorem tr_smul (p : Y ⟶ Sp K) {τ : Y ⟶ Y} (h : τ ≫ q = q) (hp : τ ≫ p = p) (a : K) (s : (M.pull q).Sec) :
    tr h (constHom p a • s) = constHom p a • tr h s :=
  pull_ext fun y i hy => by
    have hy' : q ((𝟙 Y ≫ τ) y) ∈ M.U i := (congrArg (fun t => t y ∈ M.U i) h).mpr hy
    rw [pv_tr h _ (𝟙 Y) y hy, pv_smul p a _ (𝟙 Y) y hy, pv_smul p a _ (𝟙 Y ≫ τ) y hy', pv_tr h _ (𝟙 Y) y hy,
      Category.assoc, hp]

theorem tr_add {τ : Y ⟶ Y} (h : τ ≫ q = q) (s t : (M.pull q).Sec) : tr h (s + t) = tr h s + tr h t :=
  lbSec_ext fun j => map_add (τ.appLE _ _ (chart_le h j)).hom _ _

theorem tr_tr {τ τ' τ'' : Y ⟶ Y} (h : τ ≫ q = q) (h' : τ' ≫ q = q) (h'' : τ'' ≫ q = q) (e : τ ≫ τ' = τ'')
    (s : (M.pull q).Sec) : tr h (tr h' s) = tr h'' s :=
  pull_ext fun y i hy => by
    have hy' : q ((𝟙 Y ≫ τ) y) ∈ M.U i := (congrArg (fun t => t y ∈ M.U i) h).mpr hy
    rw [pv_tr h _ (𝟙 Y) y hy, pv_tr h'' _ (𝟙 Y) y hy, pv_tr h' _ (𝟙 Y ≫ τ) y hy', Category.assoc, e]

theorem tr_id {τ : Y ⟶ Y} (h : τ ≫ q = q) (e : τ = 𝟙 Y) (s : (M.pull q).Sec) : tr h s = s :=
  pull_ext fun y i hy => by
    rw [pv_tr h _ (𝟙 Y) y hy, e, Category.comp_id]

def qv (s : (LB.div M N).Sec) (r : Z ⟶ X) (z : Z) (i : M.ι) (l : N.ι) : Z.presheaf.stalk z :=
  gs r z (M.U i ⊓ N.U l) (s.f (i, l))

theorem qv_compat (s : (LB.div M N).Sec) (r : Z ⟶ X) (z : Z) {i i' : M.ι} {l l' : N.ι}
    (h : r z ∈ M.U i ⊓ N.U l) (h' : r z ∈ M.U i' ⊓ N.U l') :
    qv s r z i l = (gm r z (M.U i ⊓ M.U i') (M.g i i') * (gm r z (N.U l ⊓ N.U l') (N.g l l'))⁻¹).val *
      qv s r z i' l' :=
  (gs_compat s r z (j := (i, l)) (j' := (i', l')) h h').trans
    (congrArg (fun w : (Z.presheaf.stalk z)ˣ => w.val * qv s r z i' l') (gm_div N M r z (i, l) (i', l') ⟨h, h'⟩))

theorem exists_mul (hM : M.IsLB) (hN : N.IsLB) (u : ∀ l, Γ(Y, q ⁻¹ᵁ N.U l)ˣ)
    (hu : ∀ (y : Y) l l', q y ∈ N.U l → q y ∈ N.U l' → gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l) =
      gm (𝟙 Y ≫ q) y (N.U l ⊓ N.U l') (N.g l l') * gm (𝟙 Y) y (q ⁻¹ᵁ N.U l') (u l')) (s : (LB.div M N).Sec) :
    ∃ v : (M.pull q).Sec, ∀ (r : Y ⟶ Y) (y : Y) (i : M.ι) (l : N.ι), q (r y) ∈ M.U i → q (r y) ∈ N.U l →
      pv v r y i = qv s (r ≫ q) y i l * (gm r y (q ⁻¹ᵁ N.U l) (u l)).val := by
  have hM' := Semi.LB.isLB_pull hM q
  have le : ∀ a : M.ι × N.ι, q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2) ≤ q ⁻¹ᵁ N.U a.2 := fun a y hy => hy.2
  obtain ⟨t, val⟩ : ∃ t : ∀ a : M.ι × N.ι, Γ(Y, q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2)), ∀ (r : Y ⟶ Y) (y : Y) (a : M.ι × N.ι),
      q (r y) ∈ M.U a.1 ⊓ N.U a.2 → gs r y _ (t a) =
        qv s (r ≫ q) y a.1 a.2 * (gm r y (q ⁻¹ᵁ N.U a.2) (u a.2)).val :=
    ⟨fun a => (q.app (M.U a.1 ⊓ N.U a.2)).hom (s.f a) * resG Y (le a) (u a.2).val, fun r y a hy =>
      (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_pull r q y _ hy _)
        ((gs_res r y _ hy _).trans (gs_unit r y _ (le a hy) _)))⟩
  obtain ⟨v, hv⟩ := exists_sec_of_refinement hM' (fun a : M.ι × N.ι => q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2))
    (fun a _ => a.1) (fun _ _ hy => mem_pull.2 hy.1)
    (fun y => (exists_chart hM (q y)).elim fun k hk => (exists_chart hN (q y)).elim fun l hl => ⟨(k, l), hk, hl⟩) t
    (fun y a b ha hb => by
      refine (val (𝟙 Y) y a ha).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val
        (gm_pull_g (𝟙 Y) y (fun _ => a.1) (fun _ => b.1) (mem_pull.2 ha.1) (mem_pull.2 hb.1)))
          (val (𝟙 Y) y b hb)).symm)
      rw [qv_compat s (𝟙 Y ≫ q) y ha hb, hu y a.2 b.2 ha.2 hb.2, Units.val_mul, Units.val_mul,
        _root_.mul_mul_mul_comm, _root_.mul_assoc (Units.val _), Units.inv_mul, _root_.mul_one])
  refine ⟨v, fun r y i l hi hl => ?_⟩
  have e := hv (r y) (fun _ => i) (i, l) (mem_pull.2 hi) ⟨hi, hl⟩
  have c := gm_self hM' (𝟙 Y) (r y) (i := fun _ => i) (mem_pull.2 hi)
  replace e := e.trans ((congrArg (fun w : (Y.presheaf.stalk (r y))ˣ => w.val * _) c).trans (_root_.one_mul _))
  exact (gs_stalkMap r y _ (mem_pull.2 hi) _).trans ((congrArg _ e).trans
    ((gs_stalkMap r y _ (show r y ∈ q ⁻¹ᵁ (M.U i ⊓ N.U l) from ⟨hi, hl⟩) _).symm.trans (val r y (i, l) ⟨hi, hl⟩)))

theorem ext_pull (H : ∀ U : X.Opens, Function.Injective (q.app U).hom) {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y : Y, q y ∈ U → gs (𝟙 Y ≫ q) y U a = gs (𝟙 Y ≫ q) y U b) : a = b :=
  H U (fn_ext fun y hy => (gs_pull (𝟙 Y) q y U hy a).trans ((h y hy).trans (gs_pull (𝟙 Y) q y U hy b).symm))

end General

section Weight

variable {K : Type} [Field K] {Y : Scheme.{0}} {M N : LB Y} {q : Y ⟶ Y} {G : Type} {τ : G → (Y ⟶ Y)}

theorem exists_div (H : Descends q τ) (hτq : ∀ g, τ g ≫ q = q) (p : Y ⟶ Sp K) (u : ∀ l, Γ(Y, q ⁻¹ᵁ N.U l)ˣ)
    (hu : ∀ (y : Y) l l', q y ∈ N.U l → q y ∈ N.U l' → gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l) =
      gm (𝟙 Y ≫ q) y (N.U l ⊓ N.U l') (N.g l l') * gm (𝟙 Y) y (q ⁻¹ᵁ N.U l') (u l')) (χ : G → K)
    (hχ : ∀ g (y : Y) l, q y ∈ N.U l → (gm (𝟙 Y ≫ τ g) y (q ⁻¹ᵁ N.U l) (u l)).val =
      cst (𝟙 Y ≫ p) y (χ g) * (gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l)).val)
    (v : (M.pull q).Sec) (hv : ∀ g, tr (hτq g) v = constHom p (χ g) • v) :
    ∃ s : (LB.div M N).Sec, ∀ (y : Y) (i : M.ι) (l : N.ι), q y ∈ M.U i → q y ∈ N.U l →
      pv v (𝟙 Y) y i = qv s (𝟙 Y ≫ q) y i l * (gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l)).val := by
  have le : ∀ a : M.ι × N.ι, q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2) ≤ q ⁻¹ᵁ N.U a.2 := fun a y hy => hy.2
  have le' : ∀ a : M.ι × N.ι, q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2) ≤ (M.pull q).U fun _ => a.1 :=
    fun a y hy => mem_pull.2 hy.1
  obtain ⟨t, val⟩ : ∃ t : ∀ a : M.ι × N.ι, Γ(Y, q ⁻¹ᵁ (M.U a.1 ⊓ N.U a.2)), ∀ (r : Y ⟶ Y) (y : Y) (a : M.ι × N.ι),
      q (r y) ∈ M.U a.1 ⊓ N.U a.2 → gs r y _ (t a) = pv v r y a.1 * ((gm r y (q ⁻¹ᵁ N.U a.2) (u a.2))⁻¹).val :=
    ⟨fun a => resG Y (le' a) (v.f fun _ => a.1) * resG Y (le a) ((u a.2)⁻¹).val, fun r y a hy =>
      (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y _ hy _)
        ((gs_res r y _ hy _).trans ((gs_unit r y _ (le a hy) _).trans (congrArg Units.val (map_inv _ _)))))⟩
  have ex : ∀ a : M.ι × N.ι, ∃ b, (q.app (M.U a.1 ⊓ N.U a.2)).hom b = t a := fun a => H.2 _ _ fun g y hy => by
    have hy' : q ((𝟙 Y ≫ τ g) y) ∈ M.U a.1 ⊓ N.U a.2 :=
      (congrArg (fun t => t y ∈ M.U a.1 ⊓ N.U a.2) (hτq g)).mpr hy
    have e₁ := val (𝟙 Y ≫ τ g) y a hy'
    have e₂ := (pv_tr (hτq g) v (𝟙 Y) y hy.1).symm.trans ((congrArg (fun w => pv w (𝟙 Y) y a.1) (hv g)).trans
      (pv_smul p (χ g) v (𝟙 Y) y hy.1))
    have e₃ := hχ g y a.2 hy.2
    rw [← Category.id_comp (τ g), e₁, val (𝟙 Y) y a hy, Units.mul_inv_eq_iff_eq_mul, e₂, e₃]
    linear_combination (-(cst (𝟙 Y ≫ p) y (χ g) * pv v (𝟙 Y) y a.1)) *
      (gm (𝟙 Y) y (q ⁻¹ᵁ N.U a.2) (u a.2)).inv_mul
  choose b hb using ex
  have key : ∀ (y : Y) (a : M.ι × N.ι), q y ∈ M.U a.1 ⊓ N.U a.2 → gs (𝟙 Y ≫ q) y (M.U a.1 ⊓ N.U a.2) (b a) =
      pv v (𝟙 Y) y a.1 * ((gm (𝟙 Y) y (q ⁻¹ᵁ N.U a.2) (u a.2))⁻¹).val := fun y a hy =>
    (gs_pull (𝟙 Y) q y _ hy _).symm.trans ((congrArg (gs (𝟙 Y) y _) (hb a)).trans (val (𝟙 Y) y a hy))
  refine ⟨⟨b, fun a a' => ext_pull H.1 fun y hy => ?_⟩, fun y i l hi hl => ?_⟩
  · have hm : (𝟙 Y ≫ q) y ∈ M.U a.1 ⊓ N.U a.2 ⊓ (M.U a'.1 ⊓ N.U a'.2) := hy
    refine ((gs_res _ y _ hm _).trans (key y a hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans (congrArg Units.val (gm_div N M (𝟙 Y ≫ q) y a a' hm)))
        ((gs_res _ y _ hm _).trans (key y a' hy.2)))).symm)
    rw [pv_compat v (𝟙 Y) y hy.1.1 hy.2.1, hu y a.2 a'.2 hy.1.2 hy.2.2, mul_inv, Units.val_mul, Units.val_mul,
      _root_.mul_mul_mul_comm]
  · exact ((congrArg (· * _) (key y (i, l) ⟨hi, hl⟩)).trans (Units.inv_mul_cancel_right _ _)).symm

theorem exists_weight_map (hM : M.IsLB) (hN : N.IsLB) (H : Descends q τ) (hτq : ∀ g, τ g ≫ q = q)
    (p : Y ⟶ Sp K) (hq : q ≫ p = p) (u : ∀ l, Γ(Y, q ⁻¹ᵁ N.U l)ˣ)
    (hu : ∀ (y : Y) l l', q y ∈ N.U l → q y ∈ N.U l' → gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l) =
      gm (𝟙 Y ≫ q) y (N.U l ⊓ N.U l') (N.g l l') * gm (𝟙 Y) y (q ⁻¹ᵁ N.U l') (u l')) (χ : G → K)
    (hχ : ∀ g (y : Y) l, q y ∈ N.U l → (gm (𝟙 Y ≫ τ g) y (q ⁻¹ᵁ N.U l) (u l)).val =
      cst (𝟙 Y ≫ p) y (χ g) * (gm (𝟙 Y) y (q ⁻¹ᵁ N.U l) (u l)).val) :
    ∃ F : (LB.div M N).Sec → (M.pull q).Sec, (∀ s t, F (s + t) = F s + F t) ∧
      (∀ a s, F (constHom p a • s) = constHom p a • F s) ∧ Function.Injective F ∧
      ∀ v, (∃ s, F s = v) ↔ ∀ g, tr (hτq g) v = constHom p (χ g) • v := by
  choose F hF using exists_mul hM hN u hu
  refine ⟨F, fun s t => pull_ext fun y i hi => ?_, fun a s => pull_ext fun y i hi => ?_, fun s t h => ?_,
    fun v => ⟨?_, fun hv => ?_⟩⟩
  · obtain ⟨l, hl⟩ := exists_chart hN (q y)
    rw [pv_add _ _ (𝟙 Y) y hi, hF _ (𝟙 Y) y i l hi hl, hF _ (𝟙 Y) y i l hi hl, hF _ (𝟙 Y) y i l hi hl, ← add_mul]
    exact congrArg (· * _) (gs_add (𝟙 Y ≫ q) y (M.U i ⊓ N.U l) ⟨hi, hl⟩ _ _)
  · obtain ⟨l, hl⟩ := exists_chart hN (q y)
    have e : qv (constHom p a • s) (𝟙 Y ≫ q) y i l = cst ((𝟙 Y ≫ q) ≫ p) y a * qv s (𝟙 Y ≫ q) y i l :=
      gs_smul p a s (𝟙 Y ≫ q) y (i, l) ⟨hi, hl⟩
    rw [pv_smul p a _ (𝟙 Y) y hi, hF _ (𝟙 Y) y i l hi hl, hF _ (𝟙 Y) y i l hi hl, e, Category.assoc, hq,
      _root_.mul_assoc]
  · refine lbSec_ext fun a => ext_pull H.1 fun y hy => ?_
    have e := (hF s (𝟙 Y) y a.1 a.2 hy.1 hy.2).symm.trans ((congrArg (fun w => pv w (𝟙 Y) y a.1) h).trans
      (hF t (𝟙 Y) y a.1 a.2 hy.1 hy.2))
    exact (Units.mul_left_inj _).1 e
  · rintro ⟨s, rfl⟩ g
    refine pull_ext fun y i hi => ?_
    obtain ⟨l, hl⟩ := exists_chart hN (q y)
    have hi' : q ((𝟙 Y ≫ τ g) y) ∈ M.U i := (congrArg (fun t => t y ∈ M.U i) (hτq g)).mpr hi
    have hl' : q ((𝟙 Y ≫ τ g) y) ∈ N.U l := (congrArg (fun t => t y ∈ N.U l) (hτq g)).mpr hl
    rw [pv_tr _ _ (𝟙 Y) y hi, pv_smul p _ _ (𝟙 Y) y hi, hF _ (𝟙 Y) y i l hi hl, hF _ (𝟙 Y ≫ τ g) y i l hi' hl',
      hχ g y l hl, Category.assoc, hτq, mul_left_comm]
  · obtain ⟨s, hs⟩ := exists_div H hτq p u hu χ hχ v hv
    refine ⟨s, pull_ext fun y i hi => ?_⟩
    obtain ⟨l, hl⟩ := exists_chart hN (q y)
    exact (hF s (𝟙 Y) y i l hi hl).trans (hs y i l hi hl).symm

theorem exists_units {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ)
    (hτq : ∀ g, τ g ≫ q = q) (w : (LB.LinComb L (fun k => q ≫ φ k) ε).Gen) (hw : w.IsGen)
    (c : G → ∀ y : Y, Y.presheaf.stalk y)
    (hc : ∀ g (y : Y) J, Good L y J → (val w (τ g) y J).val = c g y * (val w (𝟙 Y) y J).val) :
    ∃ u : ∀ l, Γ(Y, q ⁻¹ᵁ (LB.LinComb L φ ε).U l)ˣ,
      (∀ (y : Y) l l', q y ∈ (LB.LinComb L φ ε).U l → q y ∈ (LB.LinComb L φ ε).U l' →
        gm (𝟙 Y) y (q ⁻¹ᵁ (LB.LinComb L φ ε).U l) (u l) =
          gm (𝟙 Y ≫ q) y ((LB.LinComb L φ ε).U l ⊓ (LB.LinComb L φ ε).U l') ((LB.LinComb L φ ε).g l l') *
            gm (𝟙 Y) y (q ⁻¹ᵁ (LB.LinComb L φ ε).U l') (u l')) ∧
      ∀ g (y : Y) l, q y ∈ (LB.LinComb L φ ε).U l →
        (gm (𝟙 Y ≫ τ g) y (q ⁻¹ᵁ (LB.LinComb L φ ε).U l) (u l)).val =
          c g y * (gm (𝟙 Y) y (q ⁻¹ᵁ (LB.LinComb L φ ε).U l) (u l)).val := by
  have le : ∀ j, q ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => q ≫ φ k) j :=
    fun j _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  refine ⟨fun l => res (le l) (w.s l), fun y l l' hl hl' => ?_, fun g y l hl => ?_⟩
  · refine (gm_res (𝟙 Y) y (le l) hl _).trans ((gen_trans hw (𝟙 Y) y (le l hl) (le l' hl')).trans
      (congrArg₂ (· * ·) (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y ≫ q) y l l' hl hl').symm)
        (gm_res (𝟙 Y) y (le l') hl' _).symm))
    simp only [trF, Category.assoc]
  · have hl' : τ g y ∈ q ⁻¹ᵁ LB.wchart L φ l := (congrArg (fun t => t y ∈ LB.wchart L φ l) (hτq g)).mpr hl
    choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have e₁ := (gm_res (τ g) y (le l) hl' _).trans (gen_trans hw (τ g) y (le l hl') (Good.mem hJ _ _))
    have e₂ := (gm_res (𝟙 Y) y (le l) hl _).trans (gen_trans hw (𝟙 Y) y (le l hl) (Good.mem hJ _ _))
    have e₃ : trF (fun k => q ≫ φ k) ε (τ g) y l (fun k => J (τ g ≫ q ≫ φ k)) =
        trF (fun k => q ≫ φ k) ε (𝟙 Y) y l (fun k => J (𝟙 Y ≫ q ≫ φ k)) := by
      have e : ∀ k, τ g ≫ q ≫ φ k = 𝟙 Y ≫ q ≫ φ k := fun k => by
        rw [← Category.assoc, hτq, Category.id_comp]
      refine Finset.prod_congr rfl fun k _ => ?_
      show gm (τ g ≫ q ≫ φ k) y (L.U (l k) ⊓ L.U (J (τ g ≫ q ≫ φ k))) (L.g (l k) (J (τ g ≫ q ≫ φ k))) ^ _ =
        gm (𝟙 Y ≫ q ≫ φ k) y (L.U (l k) ⊓ L.U (J (𝟙 Y ≫ q ≫ φ k))) (L.g (l k) (J (𝟙 Y ≫ q ≫ φ k))) ^ _
      rw [e]
    rw [Category.id_comp]
    refine (congrArg Units.val e₁).trans (Eq.trans ?_ (congrArg (fun t : (Y.presheaf.stalk y)ˣ => c g y * t.val) e₂).symm)
    rw [Units.val_mul, Units.val_mul, e₃, mul_left_comm]
    exact congrArg _ (hc g y J hJ)

end Weight

section Group

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommutatorPairing GlobalTheory.DescentPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem transl_mulA {T : Over S} (t : A ⟶ T) (n : ℕ) (y : T ⟶ A) (hy : y ^ n = 1) :
    ((t ≫ y) * 𝟙 A).left ≫ (mulA A n).left = (mulA A n).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy, MonObj.comp_one,
    _root_.one_mul]

theorem descends_mulA (n : ℕ)
    (H : ∀ (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over S) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤ ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f) :
    Descends (mulA A n).left
      (fun y : {y : 𝟙_ (Over S) ⟶ A // y ^ n = 1} => ((toUnit A ≫ y.1) * 𝟙 A).left) := by
  refine ⟨fun U a b hab => ?_, fun U f hf => ?_⟩
  · refine (H U _ fun y hy e => fn_ext fun z hz => ?_).unique hab rfl
    refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans ((gs_pull (𝟙 _ ≫ ((toUnit A ≫ y) * 𝟙 A).left) _ z U (e hz) b).trans
      (Eq.trans ?_ (gs_pull (𝟙 _) _ z U hz b).symm))
    rw [Category.assoc, transl_mulA _ n y hy]
  · refine (H U f fun y hy e => fn_ext fun z hz => ?_).exists
    refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans (Eq.trans ?_ (hf ⟨y, hy⟩ z hz))
    rw [Category.id_comp]

theorem exists_gen_weight (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (t : A ⟶ T) (ht : ∀ r : A ⟶ A, r ≫ t = t) (n : ℕ)
    (b : T ⟶ A) (hb : b ^ n = 1) :
    ∃ w : (LB.LinComb L.L (K := Fin 2)
        (fun k => (mulA A n).left ≫ ![𝟙 A.left, ((t ≫ b) * 𝟙 A).left] k) ![1, -1]).Gen, w.IsGen ∧
      ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n y b c → ∀ (z : A.left) J, Good L.L z J →
        val w ((t ≫ y) * 𝟙 A).left z J = gm t.left z ⊤ c * val w (𝟙 A.left) z J := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n b hb
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  obtain ⟨w, hw, vw⟩ := exists_gen L.isLB (K' := Fin 2)
    (φ' := fun k => (mulA A n).left ≫ ![𝟙 A.left, ((t ≫ θx.pt) * 𝟙 A).left] k) (ε' := ![1, -1]) (fun U _ h => by
      have e₁ : lift t (𝟙 A) ≫ mulT A T n ≫ translPt A θx.pt = mulA A n ≫ ((t ≫ θx.pt) * 𝟙 A) := by
        rw [← Category.assoc, mulT, comp_lift, lift_fst, lift_translPt, MonObj.comp_pow, lift_snd, MonObj.comp_mul,
          ← Category.assoc, ht, Category.comp_id]
      have e₂ : lift t (𝟙 A) ≫ (snd T A ^ n) = mulA A n := by rw [MonObj.comp_pow, lift_snd]
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show h (lift t (𝟙 A) ≫ mulT A T n ≫ translPt A θx.pt).left ^ (-1 : ℤ) *
        h (lift t (𝟙 A) ≫ (snd T A ^ n)).left ^ (1 : ℤ) = h ((mulA A n).left ≫ 𝟙 _) ^ (1 : ℤ) *
          h (mulA A n ≫ ((t ≫ θx.pt) * 𝟙 A)).left ^ (-1 : ℤ)
      rw [e₁, e₂, Category.comp_id, _root_.mul_comm])
    (LB.invGen L.L _ _ (LB.pullGen L.L _ _ u (lift t (𝟙 A)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨w, hw, fun y c hy hc z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c⁻¹).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c⁻¹).1
    (CommPairing.weilIs_symm L.isLB hc))
  have v : ∀ r : A ⟶ A, val w r.left z J = (val u (lift t r).left z J)⁻¹ := fun r => by
    refine (vw _ r.left z J hJ).trans ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans ?_)))
    rw [← Over.comp_left, comp_lift, ht, Category.comp_id]
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := (hcm _ t (𝟙 A) z J hJ).trans (map_inv _ _)
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) (𝟙 A) (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  have t₁ := hs' (𝟙 A)
  have t₂ := hs' ((t ≫ θx.pt) * 𝟙 A)
  refine ((v _).trans (congrArg (·⁻¹) (hs _))).trans (Eq.trans ?_
    (congrArg (gm t.left z ⊤ c * ·) ((v (𝟙 A)).trans (congrArg (·⁻¹) (hs _)))).symm)
  apply Additive.ofMul.injective
  have E := fun {p q : (A.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂; have a₄ := E k₁
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₂ - a₄ - a₃ - a₁

end Group

theorem finrank_sections_pullback_mulByN_twists : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k r : ℕ), M.IsLB → (k : K) ≠ 0 → (∀ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 → SectionsHaveFiniteDimension P.A.hom (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) r) → SectionsHaveFiniteDimension P.A.hom (M.pull (Out.mulA P.A k).left) (k ^ (2 * P.g) * r) := by
  intro h₁ h₂ K _ _ P M k r hM hk hr
  haveI := P.isAb.comm
  haveI : NeZero (k : K) := ⟨hk⟩
  haveI : NeZero k := .of_neZero_natCast K
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := h₁.cube _ P L rfl
  have hD := descends_mulA k (torsion_invariant_descends (fun S _ P n hn =>
    let h := h₁.mulN S P n hn; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P k hk)
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom k).ker
  have hcard : Nat.card G = k ^ (2 * P.g) := (h₁.mulN _ P k NeZero.one_le).2.2.2.2 K (𝟙 _) hk
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne k))
  haveI := Fintype.ofFinite G
  have hτq : ∀ y : {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ k = 1},
      ((toUnit P.A ≫ y.1) * 𝟙 P.A).left ≫ (Out.mulA P.A k).left = (Out.mulA P.A k).left :=
    fun y => transl_mulA _ k y.1 y.2
  letI := secModule P.A.hom (M.pull (Out.mulA P.A k).left)
  let ρ : Representation K G (M.pull (Out.mulA P.A k).left).Sec :=
    { toFun := fun y =>
        { toFun := tr (hτq ⟨y.1, y.2⟩)
          map_add' := tr_add _
          map_smul' := tr_smul P.A.hom _ (Over.w _) }
      map_one' := LinearMap.ext fun v => tr_id (hτq ⟨1, one_pow k⟩) (by
        rw [MonObj.comp_one, _root_.one_mul]; rfl) v
      map_mul' := fun x y => LinearMap.ext fun v => (tr_tr (hτq ⟨x.1, x.2⟩) (hτq ⟨y.1, y.2⟩) (hτq ⟨(x * y).1, (x * y).2⟩) (by
        rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
          ← _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_comm y.1]; rfl) v).symm }
  let p₀ : (𝟙_ (Over (Sp K))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hT : ∀ p : (𝟙_ (Over (Sp K))).left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum K) p p₀
  obtain ⟨e⟩ := nonempty_equiv_pi_of_weights (N := Fin r → K) k (Ne.isUnit hk) (fun g : G => Subtype.ext g.2) ρ ⊤
    (fun _ _ _ => trivial) (fun χ => by
      let eK : K →* Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom
      obtain ⟨b, ⟨hb, hbχ⟩, -⟩ := h₂.charPair K P k hk (fun x => Units.map eK (χ ⟨x.1, x.2⟩))
        (fun x y => (congrArg (Units.map eK) (χ.map_mul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩)).trans (map_mul _ _ _))
      obtain ⟨w, hw, vw⟩ := exists_gen_weight h₁.globalFns P.isAb cb p₀ hT (toUnit P.A) (fun _ => comp_toUnit _) k b hb
      obtain ⟨u, hu, hχ⟩ := exists_units P.isLB _ _ hτq w hw
        (fun g z => cst (𝟙 _ ≫ P.A.hom) z (χ ⟨g.1, g.2⟩).val) (fun g z J hJ => by
          refine (congrArg Units.val (vw g.1 _ g.2 (hbχ ⟨g.1, g.2⟩) z J hJ)).trans ((Units.val_mul _ _).trans
            (congrArg (· * _) ((gs_unit _ z ⊤ trivial _).symm.trans ?_)))
          rw [Category.id_comp]
          rfl)
      obtain ⟨F, hadd, hsmul, hinj, hF⟩ := exists_weight_map hM (Semi.LB.isLB_linComb P.isLB _ _) hD hτq P.A.hom
        (Over.w _) u hu (fun g => (χ ⟨g.1, g.2⟩).val) hχ
      obtain ⟨E⟩ := (lineBundle_global_sections_functionField_iff _ _ _).1 (hr b hb)
      letI := secModule P.A.hom (LB.div M (LB.LinComb P.L (K := Fin 2)
        ![𝟙 P.A.left, ((toUnit P.A ≫ b) * 𝟙 P.A).left] ![1, -1]))
      refine ⟨LinearMap.comp ⟨⟨F, hadd⟩, hsmul⟩ E.toLinearMap, hinj.comp E.injective, fun v => ?_⟩
      refine Iff.trans ⟨fun ⟨x, hx⟩ => ⟨_, hx⟩, fun ⟨x, hx⟩ => ⟨E.symm x, ?_⟩⟩ ((hF v).trans
        ⟨fun h => ⟨trivial, fun g => h ⟨g.1, g.2⟩⟩, fun h g => h.2 ⟨g.1, g.2⟩⟩)
      exact (congrArg F (E.apply_symm_apply x)).trans hx)
  refine (lineBundle_global_sections_functionField_iff _ _ _).2 ⟨(LinearEquiv.ofFinrankEq _ (G → Fin r → K) ?_).trans (e.symm.trans Submodule.topEquiv)⟩
  simp [Module.finrank_pi_fintype, ← hcard]

end GlobalTheory.TwistSplit
