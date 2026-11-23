import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorTensor

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}}

lemma nonempty_inf_of_mem [IsIntegral X] {V W : X.Opens} (y : V) (w : W) : Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨y.1, y.2⟩ ⟨w.1, w.2⟩
  exact ⟨⟨z, hz⟩⟩

abbrev asRing (V : X.Opens) (r : Γ(X, V)) : ringOn X V := r

section RatVal

variable {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀)

noncomputable def coeffOn {V : X.Opens} (l : P.obj (op V)) : ringOn X (V ⊓ U₀) :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).symm (resM P inf_le_left l)

lemma coeffOn_spec {V : X.Opens} (l : P.obj (op V)) :
    coeffOn hs₀ l • resM P inf_le_right s₀ = resM P inf_le_left l :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).apply_symm_apply _

variable [IsIntegral X] [Nonempty U₀]

noncomputable def ratVal {V : X.Opens} (l : P.obj (op V)) (y : V) : X.functionField :=
  haveI := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  X.germToFunctionField (V ⊓ U₀) (coeffOn hs₀ l)

theorem ratVal_eq {V W : X.Opens} (hWV : W ≤ V) (hWU : W ≤ U₀) [Nonempty W]
    (l : P.obj (op V)) (a : ringOn X W) (ha : a • resM P hWU s₀ = resM P hWV l) (y : V) :
    ratVal hs₀ l y = X.germToFunctionField W a := by
  have hW' : W ≤ V ⊓ U₀ := le_inf hWV hWU
  have h1 := congrArg (resM P hW') (coeffOn_spec hs₀ l)
  rw [resM_smul_res, resM_resM] at h1
  have h2 : a = resR hW' (coeffOn hs₀ l) := (hs₀ W hWU).1 (ha.trans h1.symm)
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [h2]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

lemma ratVal_const {V : X.Opens} (l : P.obj (op V)) (y z : V) :
    ratVal hs₀ l y = ratVal hs₀ l z := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) z]

lemma ratVal_res {V W : X.Opens} (h : W ≤ V) (l : P.obj (op V)) (y : W) :
    ratVal hs₀ (resM P h l) y = ratVal hs₀ l ⟨y.1, h y.2⟩ := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e := coeffOn_spec hs₀ (resM P h l)
  rw [resM_resM] at e
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ (coeffOn_spec hs₀ (resM P h l)) y,
    ratVal_eq hs₀ ((inf_le_left : W ⊓ U₀ ≤ W).trans h) inf_le_right l _ e]

lemma ratVal_smul {V : X.Opens} (a : ringOn X V) (l : P.obj (op V)) (y : V) :
    ratVal hs₀ (a • l) y = sectionValue V y a * ratVal hs₀ l y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (resR inf_le_left a * coeffOn hs₀ l) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (a • l) := by
    rw [mul_smul, coeffOn_spec, resM_smul]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y]
  refine (map_mul (X.germToFunctionField (V ⊓ U₀)).hom
    (show Γ(X, V ⊓ U₀) from resR inf_le_left a) (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)).trans ?_
  congr 1
  refine Eq.trans ?_ (sectionValue_eq V y (show Γ(X, V) from a)).symm
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

lemma ratVal_add {V : X.Opens} (l m : P.obj (op V)) (y : V) :
    ratVal hs₀ (l + m) y = ratVal hs₀ l y + ratVal hs₀ m y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (coeffOn hs₀ l + coeffOn hs₀ m) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (l + m) := by
    rw [add_smul, coeffOn_spec, coeffOn_spec, resM_add]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right m _ (coeffOn_spec hs₀ m) y]
  exact map_add (X.germToFunctionField (V ⊓ U₀)).hom (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)
    (show Γ(X, V ⊓ U₀) from coeffOn hs₀ m)

lemma ratVal_zero {V : X.Opens} (y : V) : ratVal hs₀ (0 : P.obj (op V)) y = 0 := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right (0 : P.obj (op V)) 0
    (by rw [zero_smul, resM_zero]) y]
  exact map_zero _

lemma ratVal_sub {V : X.Opens} (l m : P.obj (op V)) (y : V) :
    ratVal hs₀ (l - m) y = ratVal hs₀ l y - ratVal hs₀ m y := by
  have h := ratVal_add hs₀ (l - m) m y
  rw [sub_add_cancel] at h
  rw [h]
  ring

end RatVal

section Invertible

variable [IsIntegral X]
  {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀) [Nonempty U₀]

lemma ratVal_ne_zero_of_isBasisOn {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    (y : U) : ratVal hs₀ s y ≠ 0 := by
  intro h
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right s _ (coeffOn_spec hs₀ s) y] at h
  have hr : coeffOn hs₀ s = 0 := Scheme.germToFunctionField_injective X (U ⊓ U₀)
    (h.trans (map_zero _).symm)
  have hz : resM P (inf_le_left : U ⊓ U₀ ≤ U) s = 0 := by
    rw [← coeffOn_spec hs₀ s, hr, zero_smul]
  have hb := (hs (U ⊓ U₀) inf_le_left).1
  have h10 : (1 : ringOn X (U ⊓ U₀)) = 0 := hb (by simp only [hz, smul_zero])
  exact one_ne_zero (α := Γ(X, U ⊓ U₀)) h10

omit hs₀ in

lemma eq_zero_of_ratVal_eq_zero {L : X.Modules} (hL : IsInvertibleSheaf L) {U₀ : X.Opens}
    {s₀ : ((preMod X).obj L).obj (op U₀)} (hs₀ : IsBasisOn ((preMod X).obj L) U₀ s₀)
    [Nonempty U₀] {V : X.Opens} (l : ((preMod X).obj L).obj (op V))
    (h : ∀ y, ratVal hs₀ l y = 0) : l = 0 := by
  apply sheaf_eq_of_locally ⟨L.presheaf, L.isSheaf⟩ (V := V) l 0
  intro x hxV
  obtain ⟨U, hxU, s, hs⟩ := hL x
  refine ⟨V ⊓ U, inf_le_left, ⟨hxV, hxU⟩, ?_⟩
  obtain ⟨a, ha⟩ := (hs (V ⊓ U) inf_le_right).2 (resM _ inf_le_left l)
  have ha' : a • resM _ inf_le_right s = resM _ inf_le_left l := ha
  have hW : Nonempty (V ⊓ U : X.Opens) := ⟨⟨x, hxV, hxU⟩⟩
  have h1 := ratVal_smul hs₀ a (resM _ inf_le_right s) ⟨x, hxV, hxU⟩
  rw [ha', ratVal_res, h, ratVal_res] at h1
  have hs0 := ratVal_ne_zero_of_isBasisOn hs₀ hs ⟨x, hxU⟩
  have ha0 : sectionValue (V ⊓ U) ⟨x, hxV, hxU⟩ a = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_right hs0
  have ha0' : a = 0 := Scheme.germToFunctionField_injective X (V ⊓ U)
    ((sectionValue_eq _ _ _).symm.trans (ha0.trans (map_zero _).symm))
  change resM _ inf_le_left l = resM _ inf_le_left (0 : ((preMod X).obj L).obj (op V))
  rw [← ha', ha0', zero_smul, resM_zero]

variable {L : X.Modules} (hL : IsInvertibleSheaf L)

noncomputable def basisOpen (x : X) : X.Opens := (hL x).choose

omit [IsIntegral X] in
lemma mem_basisOpen (x : X) : x ∈ basisOpen hL x := (hL x).choose_spec.choose

noncomputable def basisSec (x : X) : ((preMod X).obj L).obj (op (basisOpen hL x)) :=
  (hL x).choose_spec.choose_spec.choose

omit [IsIntegral X] in
lemma isBasisOn_basisSec (x : X) :
    IsBasisOn ((preMod X).obj L) (basisOpen hL x) (basisSec hL x) :=
  (hL x).choose_spec.choose_spec.choose_spec

instance (x : X) : Nonempty (basisOpen hL x) := ⟨⟨x, mem_basisOpen hL x⟩⟩

noncomputable def secVal {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) (y : V) :
    X.functionField :=
  ratVal (isBasisOn_basisSec hL (Classical.arbitrary X)) l y

lemma secVal_basisSec_ne_zero (x : X) (y : basisOpen hL x) :
    secVal hL (basisSec hL x) y ≠ 0 :=
  ratVal_ne_zero_of_isBasisOn _ (isBasisOn_basisSec hL x) y

variable [IsNoetherian X] [IsLocallyFactorial X]

lemma ord_secVal_basisSec (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) =
      Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩) := by
  set W := basisOpen hL x ⊓ basisOpen hL Z.point
  have hZW : Z.point ∈ W := ⟨hZ, mem_basisOpen hL Z.point⟩
  have : Nonempty W := ⟨⟨Z.point, hZW⟩⟩
  obtain ⟨u, hu⟩ := (isBasisOn_basisSec hL Z.point W inf_le_right).2
    (resM _ inf_le_left (basisSec hL x))
  obtain ⟨v, hv⟩ := (isBasisOn_basisSec hL x W inf_le_left).2
    (resM _ inf_le_right (basisSec hL Z.point))
  have hu' : u • resM _ inf_le_right (basisSec hL Z.point) = resM _ inf_le_left (basisSec hL x) :=
    hu
  have hv' : v • resM _ inf_le_left (basisSec hL x) = resM _ inf_le_right (basisSec hL Z.point) :=
    hv
  have huv : u * v = 1 := (isBasisOn_basisSec hL x W inf_le_left).1 (by
    change (u * v) • resM _ inf_le_left (basisSec hL x) = (1 : ringOn X W) • _
    rw [mul_smul, hv', hu', one_smul])
  have hunit : IsUnit (M := Γ(X, W)) u := isUnit_iff_exists_inv.mpr ⟨v, huv⟩
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) u
    (resM _ inf_le_right (basisSec hL Z.point)) ⟨Z.point, hZW⟩
  rw [hu', ratVal_res, ratVal_res] at h1
  change secVal hL (basisSec hL x) ⟨Z.point, hZ⟩ = sectionValue W ⟨Z.point, hZW⟩ u *
    secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩ at h1
  have hsv : sectionValue W ⟨Z.point, hZW⟩ u ≠ 0 := by
    intro h0
    apply hunit.ne_zero
    exact Scheme.germToFunctionField_injective X W
      ((sectionValue_eq _ _ _).symm.trans (h0.trans (map_zero _).symm))
  have h0 : Z.ord (sectionValue W ⟨Z.point, hZW⟩ u) = 0 :=
    (congrArg Z.ord (sectionValue_eq _ _ _)).trans (Z.ord_germToFunctionField_of_isUnit hZW hunit)
  rw [h1, Z.ord_mul hsv (secVal_basisSec_ne_zero hL _ _), h0, zero_add]

noncomputable def divisorOfInvertible : WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun Z => - Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩)) (by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (basisOpen hL x : Set X))
      (fun x => (basisOpen hL x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_basisOpen hL x⟩)
    refine (t.finite_toSet.biUnion fun x _ => PrimeDivisor.finite_ord_ne_zero
      (secVal_basisSec_ne_zero hL x ⟨x, mem_basisOpen hL x⟩)).subset ?_
    intro Z hZ
    obtain ⟨x, hx, hZx⟩ : ∃ x ∈ t, Z.point ∈ basisOpen hL x := by
      have := ht (Set.mem_univ Z.point)
      simpa using this
    refine Set.mem_biUnion hx ?_
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hZ
    change Z.ord (ratVal _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩) ≠ 0
    rw [ratVal_const _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩ ⟨Z.point, hZx⟩]
    change Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZx⟩) ≠ 0
    rwa [ord_secVal_basisSec hL Z x hZx])

lemma ord_secVal_basisSec_eq (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) = - divisorOfInvertible hL Z := by
  rw [ord_secVal_basisSec hL Z x hZ]
  change _ = - - _
  rw [neg_neg]

lemma secVal_mem {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) :
    (fun y => secVal hL l y) ∈ divisorSections (divisorOfInvertible hL) V := by
  refine ⟨fun y => ⟨⊤, trivial, fun z _ => ratVal_const _ l z y⟩, fun y hy => ?_⟩
  set Z := PrimeDivisor.ofPoint y.1 hy
  by_cases h0 : secVal hL l y = 0
  · change Z.valuation (secVal hL l y) ≤ _
    rw [h0, map_zero]
    exact zero_le
  change Z.valuation (secVal hL l y) ≤ WithZero.exp (divisorOfInvertible hL Z)
  rw [Z.valuation_le_exp_iff h0]
  set W := V ⊓ basisOpen hL y.1
  have hyW : y.1 ∈ W := ⟨y.2, mem_basisOpen hL y.1⟩
  have : Nonempty W := ⟨⟨y.1, hyW⟩⟩
  obtain ⟨a, ha⟩ := (isBasisOn_basisSec hL y.1 W inf_le_right).2 (resM _ inf_le_left l)
  have ha' : a • resM _ inf_le_right (basisSec hL y.1) = resM _ inf_le_left l := ha
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) a
    (resM _ inf_le_right (basisSec hL y.1)) ⟨y.1, hyW⟩
  rw [ha', ratVal_res, ratVal_res] at h1
  change secVal hL l y = sectionValue W ⟨y.1, hyW⟩ a *
    secVal hL (basisSec hL y.1) ⟨y.1, mem_basisOpen hL y.1⟩ at h1
  have hb0 := secVal_basisSec_ne_zero hL y.1 ⟨y.1, mem_basisOpen hL y.1⟩
  have ha0 : sectionValue W ⟨y.1, hyW⟩ a ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact h0 h1
  have hpos : 0 ≤ Z.ord (sectionValue W ⟨y.1, hyW⟩ a) :=
    (Z.ord_nonneg_iff ha0).mpr ⟨X.presheaf.germ W y.1 hyW a, rfl⟩
  rw [h1, Z.ord_mul ha0 hb0]
  have := ord_secVal_basisSec_eq hL Z y.1 (mem_basisOpen hL y.1)
  change Z.ord (secVal hL (basisSec hL y.1) ⟨y.1, mem_basisOpen hL y.1⟩) = _ at this
  omega

noncomputable def toDivisorPresheaf :
    (preMod X).obj L ⟶ (preMod X).obj (divisorSheaf (divisorOfInvertible hL)) :=
  PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun l => (⟨fun y => secVal hL l y, secVal_mem hL l⟩ :
            divisorSections (divisorOfInvertible hL) V.unop)
          map_zero' := Subtype.ext (funext fun y => ratVal_zero _ y)
          map_add' := fun l m => Subtype.ext (funext fun y => ratVal_add _ l m y) }
      naturality := fun V W i => by
        ext l
        apply Subtype.ext
        funext y
        exact ratVal_res _ i.unop.le l y }
    (fun V r l => Subtype.ext (funext fun y => ratVal_smul _ r l y))

noncomputable def toDivisorSheaf : L ⟶ divisorSheaf (divisorOfInvertible hL) :=
  ⟨toDivisorPresheaf hL⟩

theorem secVal_bijective (V : X.Opens) :
    Function.Bijective (fun l : ((preMod X).obj L).obj (op V) =>
      (⟨fun y => secVal hL l y, secVal_mem hL l⟩ :
        divisorSections (divisorOfInvertible hL) V)) := by
  constructor
  · intro l m h
    have hlm : l - m = 0 := eq_zero_of_ratVal_eq_zero hL _ (l - m) (fun y => by
      rw [ratVal_sub]
      have := congrArg (fun t : divisorSections (divisorOfInvertible hL) V => t.1 y) h
      exact sub_eq_zero.mpr this)
    exact sub_eq_zero.mp hlm
  · intro t
    by_cases hne : Nonempty V
    swap
    · exact ⟨0, Subtype.ext (funext fun y => (hne ⟨y⟩).elim)⟩
    obtain ⟨y₀⟩ := hne
    set c := t.1 y₀
    have hW : ∀ x : V, Nonempty (V ⊓ basisOpen hL x.1 : X.Opens) :=
      fun x => ⟨⟨x.1, x.2, mem_basisOpen hL x.1⟩⟩
    have hord : ∀ x : V, ∀ Z : PrimeDivisor X, Z.point ∈ V ⊓ basisOpen hL x.1 →
        0 ≤ Z.ord (c * (secVal hL (basisSec hL x.1) ⟨x.1, mem_basisOpen hL x.1⟩)⁻¹) := by
      intro x Z hZ
      set β := secVal hL (basisSec hL x.1) ⟨x.1, mem_basisOpen hL x.1⟩
      have hβ : β ≠ 0 := secVal_basisSec_ne_zero hL _ _
      by_cases hc : c = 0
      · rw [hc, zero_mul, PrimeDivisor.ord_zero]
      have hβinv : Z.ord β⁻¹ = - Z.ord β := by
        have h := Z.ord_mul hβ (inv_ne_zero hβ)
        rw [mul_inv_cancel₀ hβ, PrimeDivisor.ord_one] at h
        omega
      have hβZ : Z.ord β = - divisorOfInvertible hL Z := by
        have := ord_secVal_basisSec_eq hL Z x.1 hZ.2
        rw [← this]
        exact congrArg Z.ord (ratVal_const _ _ _ _)
      have hcZ : -divisorOfInvertible hL Z ≤ Z.ord c := by
        have ht := t.2.2 ⟨Z.point, hZ.1⟩ Z.2
        have hct : t.1 ⟨Z.point, hZ.1⟩ = c := divisorSections_apply_eq _ t _ y₀
        rw [hct] at ht
        exact (Z.valuation_le_exp_iff hc (divisorOfInvertible hL Z)).mp ht
      rw [Z.ord_mul hc (inv_ne_zero hβ), hβinv, hβZ]
      omega
    choose a ha using fun x : V => exists_section_of_ord_nonneg (V ⊓ basisOpen hL x.1) _ (hord x)
    let lx : ∀ x : V, ((preMod X).obj L).obj (op (V ⊓ basisOpen hL x.1)) :=
      fun x => asRing _ (a x) • resM _ inf_le_right (basisSec hL x.1)
    have hlx : ∀ (x : V) (z : (V ⊓ basisOpen hL x.1 : X.Opens)), secVal hL (lx x) z = c := by
      intro x z
      have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) (asRing _ (a x))
        (resM _ inf_le_right (basisSec hL x.1)) z
      rw [ratVal_res] at h1
      refine h1.trans ((congrArg (· * ratVal _ (basisSec hL x.1) _)
        (sectionValue_eq _ z (a x))).trans ?_)
      simp only
      rw [ha x, ratVal_const _ (basisSec hL x.1) _ ⟨x.1, mem_basisOpen hL x.1⟩]
      exact inv_mul_cancel_right₀ (secVal_basisSec_ne_zero hL _ _) c
    obtain ⟨l, hl⟩ := sheaf_exists_glue ⟨L.presheaf, L.isSheaf⟩ (V := V) (ι := V)
      (fun x => V ⊓ basisOpen hL x.1) (fun _ => inf_le_left)
      (fun x hx => ⟨⟨x, hx⟩, hx, mem_basisOpen hL x⟩) lx (by
        intro p q
        have hsub : resM _ (inf_le_left : (V ⊓ basisOpen hL p.1) ⊓ (V ⊓ basisOpen hL q.1) ≤ _)
            (lx p) - resM _ inf_le_right (lx q) = 0 :=
          eq_zero_of_ratVal_eq_zero hL _ _ (fun z => by
            rw [ratVal_sub, ratVal_res, ratVal_res]
            change secVal hL (lx p) _ - secVal hL (lx q) _ = 0
            exact (congrArg₂ (· - ·) (hlx p _) (hlx q _)).trans (sub_self c))
        exact sub_eq_zero.mp hsub)
    refine ⟨l, Subtype.ext (funext fun y => ?_)⟩
    have e : resM ((preMod X).obj L) (inf_le_left : V ⊓ basisOpen hL y.1 ≤ V) l = lx y := hl y
    have h2 := ratVal_res (isBasisOn_basisSec hL (Classical.arbitrary X))
      (inf_le_left : V ⊓ basisOpen hL y.1 ≤ V) l ⟨y.1, y.2, mem_basisOpen hL y.1⟩
    rw [e] at h2
    change secVal hL (lx y) _ = secVal hL l y at h2
    change secVal hL l y = t.1 y
    rw [← h2, hlx, divisorSections_apply_eq _ t y y₀]

instance : IsIso (toDivisorSheaf hL) :=
  isIso_of_locally_bijective _ (fun _ => ⟨⊤, trivial, fun V _ => secVal_bijective hL V⟩)

theorem exists_iso_divisorSheaf (hL : IsInvertibleSheaf L) :
    ∃ D : WeilDivisor X, Nonempty (L ≅ divisorSheaf D) :=
  ⟨divisorOfInvertible hL, ⟨asIso (toDivisorSheaf hL)⟩⟩

end Invertible

end GroundTheory.Arith.SchemeCoh
