import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.SpecMapAwayFnEquivAwayChart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus RelAmple powOver)
open GlobalTheory.TangentOrigin GlobalTheory.LBGerm

namespace GlobalTheory

namespace LB

variable {X Y : Scheme.{0}} {U₀ U₁ : X.Opens} (u : Γ(X, U₀ ⊓ U₁)ˣ)

def twoChartFn (a : Γ(X, U₀)) (b : Γ(X, U₁)) : ∀ i, Γ(X, (twoChart U₀ U₁ u).U i)
  | true => a
  | false => b

theorem twoChartFn_compat (n : ℕ) {a : Γ(X, U₀)} {b : Γ(X, U₁)}
    (h : resG X inf_le_left a = (u : Γ(X, U₀ ⊓ U₁)) ^ n * resG X inf_le_right b) (i j : Bool) :
    resG X (inf_le_left : (twoChart U₀ U₁ u).U i ⊓ (twoChart U₀ U₁ u).U j ≤ _) (twoChartFn u a b i) =
      ((twoChart U₀ U₁ u).g i j).val ^ n * resG X inf_le_right (twoChartFn u a b j) := by
  rcases i with _ | _ <;> rcases j with _ | _
  · exact ((congrArg (· * _) (one_pow n)).trans (one_mul _)).symm
  · have l : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁ := le_inf inf_le_right inf_le_left
    have e := congrArg (resG X l) h
    simp only [map_mul, map_pow, resG_resG] at e
    change resG X (inf_le_left : U₁ ⊓ U₀ ≤ U₁) b = ((res l u)⁻¹).val ^ n *
      resG X (inf_le_right : U₁ ⊓ U₀ ≤ U₀) a
    rw [e, ← val_res, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  · exact h
  · exact ((congrArg (· * _) (one_pow n)).trans (one_mul _)).symm

def twoChartSec (a : Γ(X, U₀)) (b : Γ(X, U₁))
    (h : resG X inf_le_left a = (u : Γ(X, U₀ ⊓ U₁)) * resG X inf_le_right b) :
    (twoChart U₀ U₁ u).Sec where
  f := twoChartFn u a b
  compat i j := (twoChartFn_compat u 1 (by rwa [pow_one]) i j).trans (by rw [pow_one])

theorem resG_injective_of_eq_basicOpen {U V : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)}
    (ha : a ∈ nonZeroDivisors Γ(X, U)) (hV : V = X.basicOpen a) (h : V ≤ U) :
    Function.Injective (resG X h) := by
  subst hV
  have := hU.isLocalization_basicOpen a
  exact IsLocalization.injective Γ(X, X.basicOpen a) (Submonoid.powers_le.2 ha)

theorem appLE_injective_of_isIso (e : Y ⟶ X) [IsIso e] {U : X.Opens} {V : Y.Opens}
    (hV : V = e ⁻¹ᵁ U) : Function.Injective (e.appLE U V hV.le).hom := by
  subst hV
  rw [← Scheme.Hom.app_eq_appLE]
  exact (ConcreteCategory.bijective_of_isIso (e.app U)).1

theorem evalPt_eq_zero_iff {A : Type} [CommRing A] (x : Sp A ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a : Γ(X, U)) : evalPt x U h a = 0 ↔ (x.app U).hom a = 0 := by
  have e : evalPt x U h a = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (resG _ h ((x.app U).hom a)) := rfl
  rw [e, map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : x ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [resG_resG, resG_self, map_zero] at this

theorem wchart_le_const (L : LB X) (φ : Y ⟶ X) (n : ℕ) (k : Fin (n + 1) → L.ι) :
    LB.wchart L (fun _ : Fin (n + 1) => φ) k ≤
      LB.wchart L (fun _ : Fin (n + 1) => φ) k ⊓ LB.wchart L (fun _ : Fin (n + 1) => φ) fun _ => k 0 :=
  le_inf le_rfl fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

def finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (s : (lbPow L (n + 1)).Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).Sec :=
  secOfGerm (fun k => (res (wchart_le_const L φ n k)
      ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
      (φ.appLE _ _ (LB.wchart_le L (fun _ : Fin (n + 1) => φ) k 0)).hom (powSecFn s (k 0)))
    fun y k k' hk hk' => by
      have hM := LB.isLB_linComb hL (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)
      have h₀ := (wchart_le_const L φ n k hk).2
      have h₀' := (wchart_le_const L φ n k' hk').2
      have hy : φ y ∈ L.U (k 0) ⊓ L.U (k' 0) := ⟨Set.mem_iInter.1 hk 0, Set.mem_iInter.1 hk' 0⟩
      have e := congrArg (gs φ y _) (powSecFn_compat s (k 0) (k' 0))
      rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
      have e₀ := gm_linComb L (fun _ : Fin (n + 1) => φ) (fun _ => 1) (𝟙 Y) y _ _ h₀ h₀'
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, Category.id_comp] at e₀
      have c₁ := gm_cocycle hM (𝟙 Y) y hk h₀ h₀'
      have c₂ := gm_cocycle hM (𝟙 Y) y hk hk' h₀'
      have v : ∀ (k : Fin (n + 1) → L.ι) (hk : y ∈ LB.wchart L (fun _ : Fin (n + 1) => φ) k),
          gs (𝟙 Y) y _ ((res (wchart_le_const L φ n k)
            ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
            (φ.appLE _ _ (LB.wchart_le L (fun _ : Fin (n + 1) => φ) k 0)).hom (powSecFn s (k 0))) =
          (gm (𝟙 Y) y _
            ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
            gs φ y _ (powSecFn s (k 0)) := fun k hk =>
        (gs_mul _ y _ hk _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hk _).trans
          (congrArg Units.val (gm_res _ y _ hk _)))
          ((gs_appLE φ _ _ _ (𝟙 Y) y hk _).trans (by rw [Category.id_comp])))
      refine (v k hk).trans (Eq.trans ?_ (congrArg (_ * ·) (v k' hk')).symm)
      rw [e, ← Units.val_pow_eq_pow_val, ← e₀, ← mul_assoc, ← mul_assoc]
      exact congrArg (· * _) (congrArg Units.val (c₁.trans c₂.symm))

theorem exists_gs_finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (φ : Y ⟶ X) (y : Y)
    (k : Fin (n + 1) → L.ι) (hk : y ∈ LB.wchart L (fun _ : Fin (n + 1) => φ) k) :
    ∃ v : (Y.presheaf.stalk y)ˣ, ∀ s : (lbPow L (n + 1)).Sec,
      gs (𝟙 Y) y _ ((finPowSec hL s φ).f k) = v.val * gs φ y _ (powSecFn s (k 0)) :=
  ⟨_, fun _ => (gs_mul _ y _ hk _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hk _)
    ((gs_appLE φ _ _ _ (𝟙 Y) y hk _).trans (by rw [Category.id_comp])))⟩

theorem nonzeroLocus_finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (s : (lbPow L (n + 1)).Sec)
    (φ : Y ⟶ X) : nonzeroLocus (finPowSec hL s φ) = φ ⁻¹ᵁ nonzeroLocus s := by
  refine nonzeroLocus_eq_of _ _ (fun y _ => exists_chart (LB.isLB_linComb hL _ _) y) fun y k hk => ?_
  obtain ⟨v, hv⟩ := exists_gs_finPowSec hL φ y k hk
  have hy : φ y ∈ L.U (k 0) := Set.mem_iInter.1 hk 0
  rw [hv, Units.isUnit_units_mul, isUnit_gs_iff φ y _ hy, ← nonzeroLocus_inf_powSecFn]
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

theorem eval₂Hom_surjective_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {b : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (po : IsPushout a b inl inr) {R σ : Type} [CommRing R]
    (c : R →+* A) (r : σ → B) (h : Function.Surjective (MvPolynomial.eval₂Hom (a.hom.comp c) r)) :
    Function.Surjective (MvPolynomial.eval₂Hom inr.hom fun j => inl.hom (r j)) := by
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · obtain ⟨p, rfl⟩ := h d
    refine ⟨MvPolynomial.map (b.hom.comp c) p, ?_⟩
    have e : inr.hom.comp b.hom = inl.hom.comp a.hom := congrArg CommRingCat.Hom.hom po.w.symm
    rw [MvPolynomial.eval₂Hom_map_hom, ← RingHom.comp_assoc, e, RingHom.comp_assoc]
    exact (MvPolynomial.map_eval₂Hom _ _ _ p).symm
  · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end LB

namespace WeierstrassCurve

open LB

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def originCofactor (U : (scheme W).Opens) (hU : U ≤ coordOpen W 1) : Γ(scheme W, U) :=
  1 + constOn W U W.a₁ * ratioOn W U 1 hU 0 + constOn W U W.a₃ * ratioOn W U 1 hU 2
    - constOn W U W.a₂ * ratioOn W U 1 hU 0 ^ 2
    - constOn W U W.a₄ * ratioOn W U 1 hU 0 * ratioOn W U 1 hU 2
    - constOn W U W.a₆ * ratioOn W U 1 hU 2 ^ 2

section

variable {W} {U V : (scheme W).Opens}

theorem resG_originCofactor (hU : U ≤ coordOpen W 1) (h : V ≤ U) :
    resG _ h (originCofactor W U hU) = originCofactor W V (h.trans hU) := by
  simp only [originCofactor, map_add, map_sub, map_mul, map_pow, map_one, resG_constOn,
    resG_ratioOn]

theorem ratioOn_mul_originCofactor (hU : U ≤ coordOpen W 1) :
    ratioOn W U 1 hU 2 * originCofactor W U hU = ratioOn W U 1 hU 0 ^ 3 := by
  have h := (WeierstrassCurve.Projective.equation_iff _).1 (equation_ratioOn hU)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ratioOn_self] at h
  rw [originCofactor]
  linear_combination h

end

def originOpen : (scheme W).Opens := (scheme W).basicOpen (originCofactor W (coordOpen W 1) le_rfl)

theorem originOpen_le : originOpen W ≤ coordOpen W 1 := (scheme W).basicOpen_le _

theorem isAffineOpen_originOpen : IsAffineOpen (originOpen W) :=
  (isAffineOpen_coordOpen W 1).basicOpen _

variable {W} in

theorem isUnit_originCofactor {U : (scheme W).Opens} (h : U ≤ originOpen W) :
    IsUnit (originCofactor W U (h.trans (originOpen_le W))) := by
  have : IsUnit (resG _ (originOpen_le W) (originCofactor W (coordOpen W 1) le_rfl)) :=
    (scheme W).toRingedSpace.isUnit_res_basicOpen _
  have := this.map (resG _ h)
  rwa [resG_originCofactor, resG_originCofactor] at this

theorem originOpen_sup_coordOpen_two : originOpen W ⊔ coordOpen W 2 = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with hx | hx
  swap
  · exact Or.inr hx
  have key : ∀ {S : Type} [CommRing S] [IsLocalRing S] (z w u a b : S), w * u = z ^ 3 →
      u + (z * a + w * b) = 1 → IsUnit u ∨ IsUnit w := by
    intro S _ _ z w u a b h₁ h₂
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h₂ with h | h
    · exact Or.inl h
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact Or.inl (isUnit_of_mul_isUnit_right (h₁ ▸ (isUnit_of_mul_isUnit_left h).pow 3))
    · exact Or.inr (isUnit_of_mul_isUnit_left h)
  let γ := ((scheme W).presheaf.germ (coordOpen W 1) x hx).hom
  rcases key (γ (ratio W 1 0)) (γ (ratio W 1 2)) (γ (originCofactor W _ le_rfl))
    (γ (constOn W _ W.a₂ * ratio W 1 0 + constOn W _ W.a₄ * ratio W 1 2 - constOn W _ W.a₁))
    (γ (constOn W _ W.a₆ * ratio W 1 2 - constOn W _ W.a₃))
    (by rw [← map_mul, ratioOn_mul_originCofactor, map_pow])
    (by rw [← map_mul, ← map_mul, ← map_add, ← map_add, ← map_one γ, originCofactor]
        congr 1
        ring) with h | h
  · exact Or.inl (((scheme W).mem_basicOpen _ x hx).2 h)
  · exact Or.inr ((basicOpen_ratioOn le_rfl).le (((scheme W).mem_basicOpen _ x hx).2 h)).2

abbrev originParam : Γ(scheme W, originOpen W) := ratioOn W (originOpen W) 1 (originOpen_le W) 0

variable {W} in

theorem isUnit_ratioOn_one_zero {U : (scheme W).Opens} (h₀ : U ≤ originOpen W)
    (h₁ : U ≤ coordOpen W 2) : IsUnit (ratioOn W U 1 (h₀.trans (originOpen_le W)) 0) := by
  rw [← isUnit_pow_iff three_ne_zero, ← ratioOn_mul_originCofactor]
  exact (isUnit_ratioOn _ h₁).mul (isUnit_originCofactor h₀)

theorem basicOpen_originParam :
    (scheme W).basicOpen (originParam W) = originOpen W ⊓ coordOpen W 2 := by
  rw [← (scheme W).basicOpen_pow _ three_pos, ← ratioOn_mul_originCofactor, Scheme.basicOpen_mul,
    basicOpen_ratioOn, (scheme W).basicOpen_of_isUnit (isUnit_originCofactor le_rfl)]
  exact inf_eq_left.2 inf_le_left

theorem isRegularFn_originParam : Cartier.IsRegularFn (originParam W) := by
  have h := ((isRegularFn_ratio_one_two W).resG (originOpen_le W)).mul
    (.of_isUnit (isUnit_originCofactor (le_refl (originOpen W))))
  rw [resG_ratioOn, ratioOn_mul_originCofactor] at h
  exact h.of_dvd (dvd_pow_self _ three_ne_zero)

theorem resG_originOpen_injective :
    Function.Injective (resG _ (inf_le_left : originOpen W ⊓ coordOpen W 2 ≤ originOpen W)) :=
  resG_injective_of_eq_basicOpen (isAffineOpen_originOpen W) (isRegularFn_originParam W).mem
    (basicOpen_originParam W).symm _

def originUnit : Γ(scheme W, originOpen W ⊓ coordOpen W 2)ˣ :=
  (isUnit_ratioOn_one_zero inf_le_left inf_le_right).unit

@[simp] theorem val_originUnit : (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) =
    ratioOn W _ 1 (inf_le_left.trans (originOpen_le W)) 0 := rfl

def originLB : LB (scheme W) := twoChart (originOpen W) (coordOpen W 2) (originUnit W)

@[simp] theorem originLB_U_true : (originLB W).U true = originOpen W := rfl

@[simp] theorem originLB_U_false : (originLB W).U false = coordOpen W 2 := rfl

@[simp] theorem originLB_g_true_false : (originLB W).g true false = originUnit W := rfl

theorem originLB_isLB : (originLB W).IsLB := twoChart_isLB (originOpen_sup_coordOpen_two W) _

def originSecMk (f₀ : Γ(scheme W, originOpen W)) (f₁ : Γ(scheme W, coordOpen W 2))
    (h : resG _ inf_le_left f₀ = (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) *
      resG _ inf_le_right f₁) : (originLB W).Sec :=
  twoChartSec (originUnit W) f₀ f₁ h

def originSec : (originLB W).Sec :=
  originSecMk W (originParam W) 1 (by rw [map_one, mul_one]; rfl)

@[simp] theorem originSec_f_true : (originSec W).f true = originParam W := rfl

@[simp] theorem originSec_f_false : (originSec W).f false = (1 : Γ(scheme W, coordOpen W 2)) := rfl

theorem isRegularSec_originSec : Cartier.IsRegularSec (originSec W)
  | true => isRegularFn_originParam W
  | false => .of_isUnit isUnit_one

theorem nonzeroLocus_originSec : nonzeroLocus (originSec W) = coordOpen W 2 := by
  refine le_antisymm (iSup_le ?_) ?_
  · rintro (_ | _)
    · exact (scheme W).basicOpen_le _
    · exact (basicOpen_originParam W).le.trans inf_le_right
  · exact ((scheme W).basicOpen_of_isUnit (isUnit_one (M := Γ(scheme W, coordOpen W 2)))).ge.trans
      (basicOpen_le_nonzeroLocus (originSec W) false)

variable {W} in

theorem evalPt_zero_ratioOn {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1)
    (h : ⊤ ≤ zero W ⁻¹ᵁ U) (j : Fin 3) :
    evalPt (zero W) U h (ratioOn W U 1 hU j) = ![0, 1, 0] j :=
  (mul_one _).symm.trans (evalPt_ptHom_ratioOn_mul (algebraMap R R) ![0, 1, 0]
    (isUnimodularSol_zero _) hU h j)

variable {W} in

theorem evalPt_zero_constOn {U : (scheme W).Opens} (h : ⊤ ≤ zero W ⁻¹ᵁ U) (r : R) :
    evalPt (zero W) U h (constOn W U r) = r :=
  evalPt_constOn (ρ := RingHom.id R) ((zero_toSpec W).trans (Spec.map_id _).symm) h r

variable {W} in

theorem evalPt_zero_originCofactor {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1)
    (h : ⊤ ≤ zero W ⁻¹ᵁ U) : evalPt (zero W) U h (originCofactor W U hU) = 1 := by
  simp [originCofactor, evalPt_zero_ratioOn]

theorem zero_preimage_originOpen : zero W ⁻¹ᵁ originOpen W = ⊤ := by
  refine top_le_iff.1 fun p _ => ?_
  rcases (originOpen_sup_coordOpen_two W).ge (Set.mem_univ (zero W p)) with h | h
  · exact h
  · exact absurd ((zero_preimage_coordOpen_two W).le h) id

abbrev originValue : Γ(scheme W, originOpen W) →+* R :=
  evalPt (zero W) (originOpen W) (zero_preimage_originOpen W).ge

theorem originValue_originParam : originValue W (originParam W) = 0 := evalPt_zero_ratioOn _ _ 0

variable {W} in

theorem eq_spMap_zero_of_evalPt {A : Type} [CommRing A] {x : Sp A ⟶ scheme W} {ρ : R →+* A}
    (hx : x ≫ toSpec W = spMap ρ) (h : ⊤ ≤ x ⁻¹ᵁ originOpen W)
    (hz : evalPt x _ h (originParam W) = 0) : x = spMap ρ ≫ zero W := by
  have hw : evalPt x _ h (ratioOn W _ 1 (originOpen_le W) 2) = 0 := by
    have := congrArg (evalPt x _ h) (ratioOn_mul_originCofactor (originOpen_le W))
    rw [map_mul, map_pow, hz, zero_pow three_ne_zero] at this
    exact ((isUnit_originCofactor le_rfl).map (evalPt x _ h)).mul_left_eq_zero.1 this
  obtain ⟨hP, e⟩ := eq_ptHom_evalPt hx (originOpen_le W) h (P := ![0, 1, 0]) fun j => by
    fin_cases j
    · exact hz
    · exact (congrArg _ (ratioOn_self _)).trans (map_one _)
    · exact hw
  exact e.trans (SpecMap_zero W ρ).symm

theorem eq_comp_zero_iff {T : Scheme.{0}} (g : T ⟶ scheme W) : g = g ≫ toSpec W ≫ zero W ↔
    ⊤ ≤ g ⁻¹ᵁ originOpen W ∧ (g.app (originOpen W)).hom (originParam W) = 0 := by
  constructor
  · intro e
    have key : ∀ q : T ⟶ Sp R, ⊤ ≤ (q ≫ zero W) ⁻¹ᵁ originOpen W ∧
        ((q ≫ zero W).app (originOpen W)).hom (originParam W) = 0 := fun q => by
      refine ⟨fun t _ => (zero_preimage_originOpen W).ge (Set.mem_univ (q t)), ?_⟩
      have := (evalPt_eq_zero_iff _ _ _).1 (originValue_originParam W)
      exact (congrArg (q.app _).hom this).trans (map_zero _)
    rw [e, ← Category.assoc]
    exact key _
  · rintro ⟨h, hz⟩
    refine T.affineCover.hom_ext _ _ fun i => ?_
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (T.affineCover.f i ≫ g ≫ toSpec W)
    have h' : ⊤ ≤ (T.affineCover.f i ≫ g) ⁻¹ᵁ originOpen W :=
      fun t _ => h (Set.mem_univ (T.affineCover.f i t))
    have := eq_spMap_zero_of_evalPt (x := T.affineCover.f i ≫ g) (ρ := ρ.hom)
      ((Category.assoc _ _ _).trans hρ.symm) h' ((evalPt_eq_zero_iff _ _ _).2
        ((congrArg ((T.affineCover.f i).app _).hom hz).trans (map_zero _)))
    exact this.trans ((congrArg (· ≫ zero W) hρ).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

theorem secPull_originSec_eq_zero_iff {T : Scheme.{0}} (g : T ⟶ scheme W) :
    (∀ j, (Cartier.secPull (originSec W) g).f j = 0) ↔ g = g ≫ toSpec W ≫ zero W := by
  have key : ∀ j, (Cartier.secPull (originSec W) g).f j = 0 ↔
      (g.app _).hom ((originSec W).f (j ⟨⟩)) = 0 := fun j => by
    refine ⟨fun h0 => ?_, fun h0 => (congrArg (resG T _) h0).trans (map_zero _)⟩
    have := congrArg (resG T (Cartier.pull_U (originLB W) g j).ge) h0
    rw [map_zero] at this
    exact ((resG_resG _ _ _).trans (resG_self _ _)).symm.trans this
  simp only [key]
  constructor
  · intro h
    refine (eq_comp_zero_iff W g).2 ⟨fun t _ => ?_, h fun _ => true⟩
    rcases (originOpen_sup_coordOpen_two W).ge (Set.mem_univ (g t)) with ht | ht
    · exact ht
    · have h1 : (1 : Γ(T, g ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans (h fun _ => false)
      have := congrArg (T.presheaf.germ (g ⁻¹ᵁ coordOpen W 2) t ht).hom h1
      rw [map_one, map_zero] at this
      exact absurd this one_ne_zero
  · intro e j
    rcases hj : j ⟨⟩ with _ | _
    · refine Cartier.ext_germ fun t ht => ?_
      rw [e, ← Category.assoc] at ht
      exact absurd ((zero_preimage_coordOpen_two W).le ht) id
    · exact ((eq_comp_zero_iff W g).1 e).2

def originDivisor : EffCartierData (scheme W) :=
  .ofSec (originLB_isLB W) (originSec W) (isRegularSec_originSec W)

def coordFn (j : Fin 3) : ∀ i, Γ(scheme W, (originLB W).U i) :=
  twoChartFn (originUnit W)
    (originCofactor W _ (originOpen_le W) * ratioOn W _ 1 (originOpen_le W) j) (ratio W 2 j)

theorem coordFn_overlap (j : Fin 3) :
    resG _ (inf_le_left : originOpen W ⊓ coordOpen W 2 ≤ _)
        (originCofactor W _ (originOpen_le W) * ratioOn W _ 1 (originOpen_le W) j) =
      (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) ^ 3 *
        resG _ inf_le_right (ratio W 2 j) := by
  rw [map_mul, resG_originCofactor, resG_ratioOn, resG_ratioOn, val_originUnit,
    ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn, mul_comm]

theorem coordFn_compat (j : Fin 3) (i k : (originLB W).ι) :
    resG _ (inf_le_left : (originLB W).U i ⊓ (originLB W).U k ≤ _) (coordFn W j i) =
      ((originLB W).g i k).val ^ 3 * resG _ inf_le_right (coordFn W j k) :=
  twoChartFn_compat (originUnit W) 3 (coordFn_overlap W j) i k

def coordSec (j : Fin 3) : (lbPow (originLB W) 3).Sec :=
  powSecMk 3 (coordFn W j) (coordFn_compat W j)

@[simp] theorem powSecFn_coordSec (j : Fin 3) (i : (originLB W).ι) :
    powSecFn (coordSec W j) i = coordFn W j i :=
  (resG_resG _ _ _).trans (resG_self _ _)

theorem basicOpen_coordFn (j : Fin 3) : ∀ i,
    (scheme W).basicOpen (coordFn W j i) = (originLB W).U i ⊓ coordOpen W j
  | true => by
    change (scheme W).basicOpen (originCofactor W _ (originOpen_le W) *
      ratioOn W _ 1 (originOpen_le W) j) = originOpen W ⊓ coordOpen W j
    rw [Scheme.basicOpen_mul, basicOpen_ratioOn, (scheme W).basicOpen_of_isUnit (isUnit_originCofactor le_rfl)]
    exact inf_eq_right.2 inf_le_left
  | false => basicOpen_ratioOn le_rfl

theorem nonzeroLocus_coordSec (j : Fin 3) : nonzeroLocus (coordSec W j) = coordOpen W j := by
  rw [coordSec, nonzeroLocus_powSecMk]
  simp only [basicOpen_coordFn]
  rw [← iSup_inf_eq, (originLB_isLB W).cover, top_inf_eq]

variable {W} in

theorem resG_coordFn {V : (scheme W).Opens} {i : Fin 3} (hi : V ≤ coordOpen W i) (j : Fin 3) :
    ∀ (k : (originLB W).ι) (hk : V ≤ (originLB W).U k),
      resG _ hk (coordFn W j k) = ratioOn W V i hi j * resG _ hk (coordFn W i k)
  | true, hk => by
    have e : ∀ l, resG _ hk (coordFn W l true) = originCofactor W V (hk.trans (originOpen_le W)) *
        ratioOn W V 1 (hk.trans (originOpen_le W)) l := fun l =>
      (map_mul (resG _ hk) _ _).trans (congrArg (· * _) (resG_originCofactor (originOpen_le W) hk))
    rw [e, e, ← ratioOn_mul_ratioOn (hk.trans (originOpen_le W)) hi]
    ring
  | false, hk => (ratioOn_mul_ratioOn (U := V) (i := 2) hk hi).symm.trans (mul_comm _ _)

variable {W} in

theorem gs_coordFn {Z : Scheme.{0}} (r : Z ⟶ scheme W) (z : Z) {i : Fin 3} (j : Fin 3)
    {k : (originLB W).ι} (hi : r z ∈ coordOpen W i) (hk : r z ∈ (originLB W).U k) :
    gs r z _ (coordFn W j k) = gs r z _ (ratio W i j) * gs r z _ (coordFn W i k) := by
  have hm : r z ∈ coordOpen W i ⊓ (originLB W).U k := ⟨hi, hk⟩
  have e := congrArg (gs r z _) (resG_coordFn (i := i) inf_le_left j k inf_le_right)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, ← resG_ratioOn le_rfl inf_le_left,
    gs_res _ z _ hm] at e

theorem exists_eq_constOn (f₀ : Γ(scheme W, originOpen W)) (f₁ : Γ(scheme W, coordOpen W 2))
    (h : resG _ inf_le_left f₀ = (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) *
      resG _ inf_le_right f₁) :
    ∃ c : R, f₀ = constOn W _ c * originParam W ∧ f₁ = constOn W _ c := by
  obtain ⟨b, rfl⟩ := (affineFnEquiv W).surjective f₁
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq b
  have h₀ : originOpen W ⊓ coordOpen W 2 ≤ originOpen W := inf_le_left
  have h₁ : originOpen W ⊓ coordOpen W 2 ≤ coordOpen W 1 := h₀.trans (originOpen_le W)
  have h₂ : originOpen W ⊓ coordOpen W 2 ≤ coordOpen W 2 := inf_le_right
  set z := ratioOn W _ 1 h₁ 0 with hz
  set x := ratioOn W _ 2 h₂ 0 with hx
  set y := ratioOn W _ 2 h₂ 1 with hy
  set u := originCofactor W _ h₁ with hu
  have ey : z ^ 3 * y = u := by
    rw [hz, ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn, ratioOn_self, one_mul]
  have ex : z ^ 2 * x = u := by
    refine (isUnit_ratioOn_one_zero h₀ h₂).mul_left_cancel ?_
    rw [← mul_assoc, ← pow_succ', ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn]
  let ψ : W.toAffine.CoordinateRing →+* _ := (resG _ h₂).comp (affineFnEquiv W).toRingHom
  have hψ : ∀ p : Polynomial R, ψ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C p)) = ∑ i ∈ p.support, constOn W _ (p.coeff i) * x ^ i := fun p => by
    have : (ψ.comp (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine)).comp Polynomial.C =
        Polynomial.eval₂RingHom (constOn W _) x := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact (congrArg (resG _ h₂) (affineFnEquiv_algebraMap W r)).trans (resG_constOn h₂ r)
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        exact congrArg (resG _ h₂) (affineFnEquiv_affineX W)
    exact (RingHom.congr_fun this p).trans (Polynomial.eval₂_eq_sum.trans (Polynomial.sum_def _ _))
  have hψy : ψ (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) = y :=
    congrArg (resG _ h₂) (affineFnEquiv_affineY W)
  have key := coeff_eq_zero_of_simple_pole (constOn W (originOpen W)) (resG _ h₀)
    (resG_originOpen_injective W) (originValue W) (evalPt_zero_constOn _) (originParam W)
    (originValue_originParam W) (Sum.elim (fun i => 2 * i) (fun i => 2 * i + 3))
    (by rintro (i | i) (j | j) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e <;>
      (congr 1; omega))
    (Sum.elim (fun i => x ^ i) (fun i => x ^ i * y))
    (Sum.elim (fun i => originCofactor W _ (originOpen_le W) ^ i)
      (fun i => originCofactor W _ (originOpen_le W) ^ (i + 1)))
    (by
      rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        rw [map_pow, resG_originCofactor, resG_ratioOn, ← hz, ← hu]
      · rw [← ex]; ring
      · rw [pow_succ u]
        nth_rw 2 [← ey]
        rw [← ex]; ring)
    (by rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      rw [map_pow, evalPt_zero_originCofactor, one_pow])
    (Sum.elim p.coeff q.coeff) (p.support.disjSum q.support) f₀ (by
      rw [h, Finset.sum_disjSum]
      refine congrArg₂ (· * ·) rfl (Eq.symm ?_)
      change ψ _ = _
      rw [map_add, WeierstrassCurve.Affine.CoordinateRing.smul,
        WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, map_mul, hψ, hψ, hψy, Finset.sum_mul]
      simp only [Sum.elim_inl, Sum.elim_inr, resG_constOn, mul_assoc])
  have hq : q = 0 := by
    ext i
    by_contra hi
    exact hi (key (.inr i) (Finset.inr_mem_disjSum.2 (Polynomial.mem_support_iff.2 hi))
      (by simp only [Sum.elim_inr]; omega))
  have hp : p = Polynomial.C (p.coeff 0) := by
    ext i
    rcases i with _ | i
    · simp
    · rw [Polynomial.coeff_C_succ]
      by_contra hi
      exact hi (key (.inl (i + 1)) (Finset.inl_mem_disjSum.2 (Polynomial.mem_support_iff.2 hi))
        (by simp only [Sum.elim_inl]; omega))
  have e₁ : affineFnEquiv W (p • (1 : W.toAffine.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      constOn W _ (p.coeff 0) := by
    rw [hq, zero_smul, add_zero, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    conv_lhs => rw [hp]
    exact affineFnEquiv_algebraMap W _
  refine ⟨p.coeff 0, resG_originOpen_injective W ?_, e₁⟩
  rw [h, e₁, map_mul, resG_constOn, resG_constOn, mul_comm]
  rfl

theorem constOn_coordOpen_two_injective : Function.Injective (constOn W (coordOpen W 2)) := by
  intro c c' h
  have h₁ := congrArg (resG _ (inf_le_right : originOpen W ⊓ coordOpen W 2 ≤ _)) h
  rw [resG_constOn, resG_constOn, ← resG_constOn inf_le_left, ← resG_constOn inf_le_left c'] at h₁
  have h₂ := congrArg (originValue W) (resG_originOpen_injective W h₁)
  rwa [evalPt_zero_constOn, evalPt_zero_constOn] at h₂

theorem existsUnique_eq_const_mul_originSec (s : (originLB W).Sec) :
    ∃! c : R, ∀ i, s.f i = constFn (toSpec W) _ c * (originSec W).f i := by
  obtain ⟨c, h₀, h₁⟩ := exists_eq_constOn W (s.f true) (s.f false) (s.compat true false)
  refine ⟨c, ?_, fun c' hc' => constOn_coordOpen_two_injective W ?_⟩
  · rintro (_ | _)
    · exact h₁.trans (mul_one _).symm
    · exact h₀
  · exact ((hc' false).trans (mul_one _)).symm.trans h₁

section BaseChange

variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')

theorem mapHom_app_originCofactor {U : (scheme W).Opens} (hU : U ≤ coordOpen W 1) :
    ((mapHom W f h).app U).hom (originCofactor W U hU) = originCofactor W' (mapHom W f h ⁻¹ᵁ U)
      (((mapHom W f h).preimage_mono hU).trans (mapHom_preimage_coordOpen W f h 1).le) := by
  simp only [originCofactor, map_add, map_sub, map_mul, map_pow, map_one, mapHom_app_constOn,
    mapHom_app_ratioOn]
  subst h
  rfl

theorem mapHom_preimage_originOpen : mapHom W f h ⁻¹ᵁ originOpen W = originOpen W' := by
  have e := mapHom_preimage_coordOpen W f h 1
  have e₁ := mapHom_app_originCofactor W f h le_rfl
  rw [← resG_originCofactor le_rfl e.le] at e₁
  refine (Scheme.preimage_basicOpen _ _).trans ((congrArg (scheme W').basicOpen e₁).trans
    (((scheme W').basicOpen_res _ (homOfLE e.le).op).trans ?_))
  exact inf_eq_right.2 ((originOpen_le W').trans e.ge)

theorem mapHom_preimage_originLB_U : ∀ i : Bool,
    mapHom W f h ⁻¹ᵁ (originLB W).U i = (originLB W').U i
  | true => mapHom_preimage_originOpen W f h
  | false => mapHom_preimage_coordOpen W f h 2

theorem mapHom_app_originSec : ∀ i : Bool,
    ((mapHom W f h).app ((originLB W).U i)).hom ((originSec W).f i) =
      resG _ (mapHom_preimage_originLB_U W f h i).le ((originSec W').f i)
  | true => mapHom_app_ratioOn W f h (originOpen_le W) 0
  | false => (map_one _).trans (map_one _).symm

theorem gs_mapHom_originSec (i : Bool) (y : scheme W') (hy : y ∈ (originLB W').U i) :
    gs (mapHom W f h) y _ ((originSec W).f i) = gs (𝟙 _) y _ ((originSec W').f i) := by
  have hy' := (mapHom_preimage_originLB_U W f h i).ge hy
  have := gs_pull (𝟙 _) (mapHom W f h) y _ hy' ((originSec W).f i)
  rw [Category.id_comp, mapHom_app_originSec] at this
  exact this.symm.trans (gs_res (𝟙 _) y _ hy' _)

def chartPullOriginLB : ChartPull (originLB W') (originLB W) (mapHom W f h) where
  idx i := i
  le i := (mapHom_preimage_originLB_U W f h i).ge
  g y i j hi hj := by
    have hi' := (mapHom_preimage_originLB_U W f h i).ge hi
    have hj' := (mapHom_preimage_originLB_U W f h j).ge hj
    have e₁ := gs_compat (originSec W') (𝟙 _) y hi hj
    have e₂ := gs_compat (originSec W) (mapHom W f h) y hi' hj'
    rw [gs_mapHom_originSec W f h i y hi, gs_mapHom_originSec W f h j y hj, e₁] at e₂
    have hr := Cartier.isRegularFn_iff_germ.1 (isRegularSec_originSec W' j) y hj
    refine Units.ext ((mul_cancel_right_mem_nonZeroDivisors ?_).1 e₂)
    rw [gs_eq (𝟙 _) y _ hj]
    exact hr

theorem existsUnique_iso_pull_originLB :
    ∃! w : LB.Iso (originLB W') ((originLB W).pull (mapHom W f h)), w.IsGen ∧
      Cartier.SecMaps w (originSec W') (Cartier.secPull (originSec W) (mapHom W f h)) := by
  refine Cartier.existsUnique_secMaps (isRegularSec_originSec W') fun p q => ?_
  have hp : ((originLB W).pull (mapHom W f h)).U p ⊓ (originLB W').U q ≤ (originLB W').U (p ⟨⟩) :=
    inf_le_left.trans ((Cartier.pull_U _ _ p).trans (mapHom_preimage_originLB_U W f h _)).le
  have e : resG _ (inf_le_left : ((originLB W).pull (mapHom W f h)).U p ⊓ (originLB W').U q ≤ _)
      ((Cartier.secPull (originSec W) (mapHom W f h)).f p) = resG _ hp ((originSec W').f (p ⟨⟩)) :=
    (resG_resG _ _ _).trans ((congrArg (resG _ _) (mapHom_app_originSec W f h _)).trans
      (resG_resG _ _ _))
  rw [e, Cartier.sec_compat (originSec W') (p ⟨⟩) q hp inf_le_right]
  exact associated_unit_mul_right _ _ ((Units.isUnit _).map _)

theorem lbIso_pull_originLB : LBIso (originLB W') ((originLB W).pull (mapHom W f h)) :=
  let ⟨w, hw, _⟩ := existsUnique_iso_pull_originLB W f h
  ⟨w, hw.1⟩

end BaseChange

theorem existsUnique_eq_const_mul_secPull {R' : Type} [CommRing R'] {f : R →+* R'} {Y : Scheme.{0}}
    {φ : Y ⟶ scheme W} {p : Y ⟶ Sp R'} (H : IsPullback φ p (toSpec W) (spMap f))
    (s : ((originLB W).pull φ).Sec) :
    ∃! c : R', ∀ j, s.f j = constFn p _ c * (Cartier.secPull (originSec W) φ).f j := by
  let e : scheme (W.map f) ⟶ Y := ((isPullback_mapHom W f rfl).isoIsPullback _ _ H).hom
  have e₁ : e ≫ φ = mapHom W f rfl := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have e₂ : e ≫ p = toSpec (W.map f) := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hU : ∀ i : Bool, (originLB (W.map f)).U i = e ⁻¹ᵁ ((originLB W).pull φ).U (fun _ => i) :=
    fun i => by
      refine (mapHom_preimage_originLB_U W f rfl i).symm.trans ?_
      rw [← e₁]
      exact congrArg (e ⁻¹ᵁ ·) (Cartier.pull_U (originLB W) φ fun _ => i).symm
  let a : ChartPull (originLB (W.map f)) ((originLB W).pull φ) e :=
    { idx := fun i _ => i
      le := fun i => (hU i).le
      g := fun y i j hi hj => ((chartPullOriginLB W f rfl).g y i j hi hj).trans (by
        rw [gm_pull_g _ φ e y _ _ ((hU i).le hi) ((hU j).le hj), e₁]
        rfl) }
  have key : ∀ (c : R') (i : Bool), (e.appLE _ _ (hU i).le).hom
      (constFn p _ c * (Cartier.secPull (originSec W) φ).f (fun _ => i)) =
      constFn (toSpec (W.map f)) _ c * (originSec (W.map f)).f i := fun c i => fn_ext fun y hy => by
    have hy' := (hU i).le hy
    rw [gs_appLE e _ _ _ (𝟙 _) y hy, Category.id_comp, gs_mul e y _ hy', gs_mul _ y _ hy,
      gs_constFn p _ e y hy', gs_constFn _ _ _ y hy, e₂, Category.id_comp,
      ← gs_mapHom_originSec W f rfl i y hy, ← e₁]
    exact congrArg _ ((gs_res e y _ hy' _).trans (gs_pull e φ y _ (mem_pull.1 hy') _))
  refine (existsUnique_congr fun c => ?_).1
    (existsUnique_eq_const_mul_originSec (W.map f) (chartSec a s))
  exact ⟨fun hc j => appLE_injective_of_isIso e (hU (j ⟨⟩)) ((hc (j ⟨⟩)).trans (key c (j ⟨⟩)).symm),
    fun hc i => (congrArg (e.appLE _ _ (hU i).le).hom (hc fun _ => i)).trans (key c i)⟩

theorem existsUnique_eq_appLE_mul_secPull {T Y : Scheme.{0}} [IsAffine T] {t : T ⟶ Sp R}
    {φ : Y ⟶ scheme W} {p : Y ⟶ T} (H : IsPullback φ p (toSpec W) t)
    (s : ((originLB W).pull φ).Sec) :
    ∃! c : Γ(T, ⊤), ∀ j, s.f j =
      (p.appLE ⊤ _ le_top).hom c * (Cartier.secPull (originSec W) φ).f j := by
  obtain ⟨f, hf⟩ := Spec.map_surjective (T.isoSpec.inv ≫ t)
  have H' : IsPullback φ (p ≫ T.isoSpec.hom) (toSpec W) (spMap f.hom) :=
    H.of_iso (Iso.refl _) (Iso.refl _) T.isoSpec (Iso.refl _) (by simp) (by simp) (by simp)
      ((Category.comp_id _).trans ((Iso.hom_inv_id_assoc T.isoSpec t).symm.trans
        (congrArg (_ ≫ ·) hf.symm)))
  have e : ∀ (U : Y.Opens) (c : Γ(T, ⊤)),
      constFn (p ≫ T.isoSpec.hom) U c = (p.appLE ⊤ U le_top).hom c := fun U c => by
    have e₁ : (p ≫ T.isoSpec.hom).appLE ⊤ U le_top = T.isoSpec.hom.appTop ≫ p.appLE ⊤ U le_top :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have e₂ : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := Scheme.toSpecΓ_appTop T
    rw [e₂] at e₁
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom c)) e₁).trans
      (congrArg (p.appLE ⊤ U le_top).hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T, ⊤)) c))
  simpa only [e] using existsUnique_eq_const_mul_secPull W H' s

theorem isGen_one_pull_zero :
    LB.Gen.IsGen (L := (originLB W).pull (zero W)) ⟨fun _ => 1⟩ := fun i j =>
  unit_ext fun y hy => by
    have key : ∀ k : PUnit → Bool, y ∈ ((originLB W).pull (zero W)).U k → k = fun _ => true := by
      intro k hk
      have hk' := mem_pull.1 hk
      funext ⟨⟩
      rcases e : k PUnit.unit with _ | _
      · rw [e] at hk'
        exact absurd ((zero_preimage_coordOpen_two W).le hk') id
      · rfl
    obtain rfl := key i hy.1
    obtain rfl := key j hy.2
    refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ?_))
    exact (congrArg₂ (· * ·) (gm_self (LB.isLB_pull (originLB_isLB W) _) (𝟙 _) y hy.1)
      (gm_res _ y _ hy _)).trans (one_mul _)

theorem relAmple_originLB : RelAmple (schemeOver W) (originLB W) := by
  intro U hU
  let ι := (toSpec W ⁻¹ᵁ U).ι
  have H : IsPullback ι (toSpec W ∣_ U) (toSpec W) U.ι := (isPullback_morphismRestrict _ U).flip
  have : IsAffine U := hU
  have : IsAffineHom ι := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  let s : Fin 3 → (powOver (schemeOver W) (originLB W) U 3).Sec := fun j =>
    finPowSec (originLB_isLB W) (n := 2) (coordSec W j) ι
  have loc : ∀ j, nonzeroLocus (s j) = ι ⁻¹ᵁ coordOpen W j := fun j =>
    (nonzeroLocus_finPowSec _ _ _).trans (by rw [nonzeroLocus_coordSec])
  refine ⟨3, by norm_num, 2, s, top_le_iff.1 fun y _ => ?_, fun i => ⟨?_,
    fun j => (ι.appLE _ _ (loc i).le).hom (ratio W i j), fun j k => fn_ext fun y hy => ?_, ?_⟩⟩
  · rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ (ι y)) with h | h
    · exact Opens.mem_iSup.2 ⟨1, (loc 1).ge h⟩
    · exact Opens.mem_iSup.2 ⟨2, (loc 2).ge h⟩
  · rw [loc]
    exact (isAffineOpen_coordOpen W i).preimage ι
  · obtain ⟨v, hv⟩ := exists_gs_finPowSec (originLB_isLB W) (n := 2) ι y k hy.2
    have e := gs_coordFn ι y j (k := k 0) ((loc i).le hy.1) (Set.mem_iInter.1 hy.2 0)
    have e₁ := hv (coordSec W j)
    have e₂ := hv (coordSec W i)
    rw [powSecFn_coordSec] at e₁ e₂
    refine (gs_res _ y _ hy _).trans (e₁.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      ((congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE ι _ _ _ (𝟙 _) y hy.1 _).trans
        (by rw [Category.id_comp]))) ((gs_res _ y _ hy _).trans e₂)).trans ?_))))
    rw [e, mul_left_comm]
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := coordOpen W i) le_top le_top
      (UY := nonzeroLocus (s i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _)
        (isAffineOpen_coordOpen W i))
    exact eval₂Hom_surjective_of_isPushout po (Scheme.ΓSpecIso (.of R)).inv.hom (ratio W i)
      (eval₂Hom_ratio_surjective W i)

theorem not_isGen_originLB [Nontrivial R] (t : (originLB W).Gen) : ¬ t.IsGen := by
  intro ht
  obtain ⟨c, hc, -⟩ := existsUnique_eq_const_mul_originSec W
    ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have h : IsUnit (originParam W) :=
    isUnit_of_mul_isUnit_right ((congrArg IsUnit (hc true)).mp (t.s true).isUnit)
  have := h.map (originValue W)
  rw [originValue_originParam] at this
  exact not_isUnit_zero this

example (s : (originLB W).Sec) :
    resG _ (inf_le_left : originOpen W ⊓ coordOpen W 2 ≤ _) (s.f true) =
      ratioOn W _ 1 (inf_le_left.trans (originOpen_le W)) 0 * resG _ inf_le_right (s.f false) :=
  s.compat true false

example : (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) *
    resG _ inf_le_right (affineFnEquiv W (affineY W)) =
      resG _ inf_le_right (affineFnEquiv W (affineX W)) := by
  rw [affineFnEquiv_affineX, affineFnEquiv_affineY, mul_comm]
  exact ratioOn_mul_ratioOn inf_le_right (inf_le_left.trans (originOpen_le W))

example (hP : IsUnimodularSol ((⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).map (RingHom.id ℚ)) ![2, -5, 8])
    (h : ⊤ ≤ ptHom _ _ _ hP ⁻¹ᵁ coordOpen _ 1) :
    evalPt (ptHom _ _ _ hP) _ h (originCofactor _ _ le_rfl) = 1 / 25 := by
  have h₀ := evalPt_ptHom_ratioOn_mul _ _ hP le_rfl h 0
  have h₂ := evalPt_ptHom_ratioOn_mul _ _ hP le_rfl h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one] at h₀ h₂
  simp only [originCofactor, map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_neg]
  rw [eq_div_of_mul_eq (by norm_num) h₀, eq_div_of_mul_eq (by norm_num) h₂]
  norm_num

end WeierstrassCurve

end GlobalTheory
