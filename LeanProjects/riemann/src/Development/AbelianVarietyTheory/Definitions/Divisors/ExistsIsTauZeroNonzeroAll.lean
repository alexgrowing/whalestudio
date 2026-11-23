import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLevWithGeometric
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShiftNullValNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfEvalGridEqZeroOfTotalDegreeLe

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaConst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.ShFam GlobalTheory.CompHt

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def tauExpr {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) : S :=
  ∑ j, (cf j : S) * ∏ b, w (x j b)

theorem map_tauExpr {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {k : ℕ} {J : Type} [Fintype J] {n : ℕ}
    (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) :
    φ (tauExpr cf x w) = tauExpr cf x (fun q => φ (w q)) := by
  simp only [tauExpr, map_prod, map_sum, map_mul, map_intCast]

theorem tauExpr_scale {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (t : S) :
    tauExpr cf x (fun q => t * w q) = t ^ n * tauExpr cf x w := by
  rw [tauExpr, tauExpr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

def IsAdm (R : ℕ) {n : ℕ} (x₀ : Fin n → Dw.La) : Prop :=
  Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤

theorem IsAdm.spans {R : ℕ} (hR : 1 < R) {n : ℕ} {x₀ : Fin n → Dw.La} (h : IsAdm R x₀) :
    EtaAn.Spans (shiftFam R x₀ : (Fin n → LatMod Dw R) → Fin n → LatMod Dw (R ^ 4)) := fun u =>
  (EtaCard.card_levGrp_and_span E H Dw R hR).2.2.2.2.2.2 n x₀ h u (LinearEquiv.refl _ _)

variable (Dw) in

theorem exists_isAdm {R : ℕ} (hR : 1 < R) : ∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, IsAdm R x₀ :=
  (EtaCard.card_levGrp_and_span E H Dw R hR).2.2.2.2.2.1

variable (Xo : Moduli Dw l) (c : Coeff l)

def TauValAt (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsLevOf Xo c (R ^ 4) y'.x ev ∧
    (∀ q, IsNullVal Xo c (R ^ 2) y' (ev q) (w q)) ∧ φ v = tauExpr cf x w

def IsTauRule (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), TauValAt Xo c R cf x y (f p y)

def IsGenRule (R : ℕ) {n : ℕ} (x₀ : Fin n → Dw.La) (u : Fin n → LatMod Dw R) (f : Rul Xo c) : Prop :=
  IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => shiftFam R x₀ u) f

def genSpan (R : ℕ) {n : ℕ} (x₀ : Fin n → Dw.La) : Submodule c.F (Rul Xo c) :=
  Submodule.span c.F {f | ∃ u, IsGenRule Xo c R x₀ u f}

def IsTauZero (R : ℕ) [Fintype (LatMod Dw R)] {n : ℕ} (x₀ : Fin n → Dw.La) (cf : (Fin n → LatMod Dw R) → ℤ)
    (f : Rul Xo c) : Prop :=
  IsTauRule Xo c R cf (shiftFam R x₀) f

variable {Xo c}

def NonzeroOn (Z : Comp Xo c) (f : Rul Xo c) : Prop := genVal Z f ≠ 0

def NonzeroAll (f : Rul Xo c) : Prop := ∀ Z : Comp Xo c, NonzeroOn Z f

section Val

variable {R : ℕ} {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ} {x : J → Fin n → LatMod Dw (R ^ 4)}

theorem exists_lev_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsLevOf Xo c (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    ∃ ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G), IsLevOf Xo c (R ^ 4) z.x ev' ∧
      ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (ψ (w q)) :=
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  ⟨fun q => h ≫ ev q, hev.baseChange ψ h rfl, fun q => NullValue.baseChange ψ hm (ev q) (h ≫ ev q) rfl (hw q)⟩

theorem map_val_eq (hR : Odd R) {S₁ S₂ T : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂] [Algebra c.F S₂]
    [CommRing T] [Algebra c.F T] (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z : FrPt Xo c T} (h₁ : FrMap ψ₁ y₁ z) (h₂ : FrMap ψ₂ y₂ z)
    {ev₁ : LatMod Dw (R ^ 4) → (ptO Xo y₁.x ⟶ Xo.univ.t.G)} {w₁ : LatMod Dw (R ^ 4) → S₁}
    {ev₂ : LatMod Dw (R ^ 4) → (ptO Xo y₂.x ⟶ Xo.univ.t.G)} {w₂ : LatMod Dw (R ^ 4) → S₂}
    (hev₁ : IsLevOf Xo c (R ^ 4) y₁.x ev₁) (hw₁ : ∀ q, IsNullVal Xo c (R ^ 2) y₁ (ev₁ q) (w₁ q))
    (hev₂ : IsLevOf Xo c (R ^ 4) y₂.x ev₂) (hw₂ : ∀ q, IsNullVal Xo c (R ^ 2) y₂ (ev₂ q) (w₂ q)) :
    ψ₁ (tauExpr cf x w₁) = ψ₂ (tauExpr cf x w₂) := by
  obtain ⟨e₁, he₁, hv₁⟩ := exists_lev_baseChange ψ₁ h₁ hev₁ hw₁
  obtain ⟨e₂, he₂, hv₂⟩ := exists_lev_baseChange ψ₂ h₂ hev₂ hw₂
  obtain rfl := he₁.unique he₂
  have : (fun q => ψ₁ (w₁ q)) = fun q => ψ₂ (w₂ q) := funext fun q =>
    (existsUnique_nullVal GlobalTheory.firstFiveLaws.1 hR he₁.2.1 q).unique (hv₁ q) (hv₂ q)
  exact (map_tauExpr ψ₁.toRingHom cf x w₁).trans
    ((congrArg (tauExpr cf x) this).trans (map_tauExpr ψ₂.toRingHom cf x w₂).symm)

theorem tauValAt_self {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S}
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsLevOf Xo c (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    TauValAt Xo c R cf x y (tauExpr cf x w) :=
  ⟨S, inferInstance, inferInstance, AlgHom.id _ _, y, ev, w,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, FramedBaseChange.refl y, hev, hw, rfl⟩

theorem TauValAt.map_eq (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S} {v : T}
    (h₀ : TauValAt Xo c R cf x y₀ v₀) (h : TauValAt Xo c R cf x y v) : φ v₀ = v := by
  obtain ⟨S', _, _, α, y₀', ev₀, w₀, hα, hmα, hev₀, hw₀, e₀⟩ := h₀
  obtain ⟨T', _, _, β, y', ev, w, hβ, hmβ, hev, hw, e⟩ := h
  obtain ⟨U, _, _, ψ₁, ψ₂, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F S T' S' (β.comp φ) α hα
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T' U ψ₁ y'
  have hz₀ : FrMap (ψ₂.comp α) y₀ z :=
    hc ▸ FramedBaseChange.trans _ ψ₁ (FramedBaseChange.trans φ β hm hmβ) hz
  have key := map_val_eq (cf := cf) (x := x) hR ψ₁ ψ₂ hz (FramedBaseChange.cancel α ψ₂ hmα hz₀) hev hw hev₀ hw₀
  have hβi : Function.Injective β := hβ.injective
  refine hβi (hinj ?_)
  rw [e, key, ← e₀]
  exact DFunLike.congr_fun hc v₀

theorem TauValAt.unique (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {v v' : S}
    (h : TauValAt Xo c R cf x y v) (h' : TauValAt Xo c R cf x y v') : v = v' :=
  TauValAt.map_eq hR (AlgHom.id c.F S) (FramedBaseChange.refl y) h h'

theorem exists_cover (hR : Odd R) (hM : R ^ 4 ∣ l.M) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
      (ev : LatMod Dw (R ^ 4) → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → S'),
      φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsLevOf Xo c (R ^ 4) y'.x ev ∧
      ∀ q, IsNullVal Xo c (R ^ 2) y' (ev q) (w q) := by
  obtain ⟨B, _, _, φ, ev₀, hφ, hev₀⟩ := exists_isLevOf_cover Xo c hM y.x
  obtain ⟨y', hm⟩ := FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S B φ y
  obtain ⟨ev, hev⟩ : ∃ ev, IsLevOf Xo c (R ^ 4) y'.x ev := by
    rw [hm.1]
    exact ⟨ev₀, hev₀⟩
  choose w hw using fun q => (existsUnique_nullVal GlobalTheory.firstFiveLaws.1 hR hev.2.1 q).exists
  exact ⟨B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw⟩

variable (cf x) in

theorem exists_tauValAt (hR : Odd R) (hM : R ^ 4 ∣ l.M) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ v, TauValAt Xo c R cf x y v := by
  obtain ⟨B, _, _, φ, y', ev, w, hφ, hm, hev, hw⟩ := exists_cover hR hM y
  obtain ⟨v, hv, -⟩ := GlobalTheory.existsUnique_preimage_of_faithfullyFlat c.F S B φ hφ (tauExpr cf x w)
    fun T _ _ ψ₁ ψ₂ hc => by
      obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c B T ψ₁ y'
      have hz₀ : FrMap (ψ₂.comp φ) y z := hc ▸ FramedBaseChange.trans φ ψ₁ hm hz
      exact map_val_eq hR ψ₁ ψ₂ hz (FramedBaseChange.cancel φ ψ₂ hm hz₀) hev hw hev hw
  exact ⟨v, B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, hv⟩

theorem TauValAt.dvd {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {v : S}
    (h : TauValAt Xo c R cf x y v) : R ^ 4 ∣ l.M := by
  obtain ⟨_, _, _, _, _, _, _, -, -, hev, -⟩ := h
  exact hev.1

theorem TauValAt.map (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S}
    (h₀ : TauValAt Xo c R cf x y₀ v₀) : TauValAt Xo c R cf x y (φ v₀) := by
  obtain ⟨v, hv⟩ := exists_tauValAt cf x hR h₀.dvd y
  rwa [TauValAt.map_eq hR φ hm h₀ hv]

theorem TauValAt.frBor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (h : FrBor t y y') {v : S} (hv : TauValAt Xo c R cf x y v) :
    TauValAt Xo c R cf x y' ((t none : S) ^ n * v) := by
  obtain ⟨S', _, _, φ, z, ev, w, hφ, hz, hev, hw, hv⟩ := hv
  obtain ⟨z', hz'⟩ := FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S S' φ y'
  have hb := ScalarWeight.frBor_baseChange φ h hz hz'
  obtain ⟨ev', hev', he⟩ : ∃ ev', IsLevOf Xo c (R ^ 4) z'.x ev' ∧ ∀ q, (ev' q).left = (ev q).left := by
    rw [hb.1]
    exact ⟨ev, hev, fun _ => rfl⟩
  refine ⟨S', _, _, φ, z', ev', fun q => φ (t none) * w q, hφ, hz', hev', fun q => ?_, ?_⟩
  · exact NullValue.triangular hb (ev q) (ev' q) (he q) (hw q)
  · rw [tauExpr_scale, map_mul, map_pow, hv]

variable (Xo c cf x) in

theorem existsUnique_isTauRule (hR : Odd R) (hM : R ^ 4 ∣ l.M) : ∃! f, IsTauRule Xo c R cf x f :=
  ⟨fun _ y => (exists_tauValAt cf x hR hM y).choose, fun _ y => (exists_tauValAt cf x hR hM y).choose_spec,
    fun _ hf => funext fun p => funext fun y => (hf p y).unique hR (exists_tauValAt cf x hR hM y).choose_spec⟩

theorem IsTauRule.mem_sec (hR : Odd R) {f : Rul Xo c} (hf : IsTauRule Xo c R cf x f) : f ∈ sec Xo c 0 n := by
  refine ⟨fun p q φ y z h => (TauValAt.map_eq hR φ h (hf p y) (hf q z)).symm, fun p t y y' h => ?_⟩
  rw [(hf p y').unique hR ((hf p y).frBor h)]
  congr 1
  simp [wchar, ex, Fintype.prod_option]

theorem IsTauRule.tauValAt_evR (hR : Odd R) {f : Rul Xo c} (hf : IsTauRule Xo c R cf x f) {S : Type} [CommRing S]
    [Algebra c.F S] {y : FrPt Xo c S} (hy : Tested y) : TauValAt Xo c R cf x y (evR Xo c f y) := by
  unfold evR evalAt
  rw [dif_pos hy]
  exact (hf _ _).map hR _ hy.choose_spec.choose_spec.choose_spec

end Val

theorem tested_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : Tested (genFr h Z) :=
  (Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 h Z

theorem genVal_idem (Z : Comp Xo c) : genVal Z (idem Z) = 1 :=
  have h := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  (genVal_apply h Z _).trans (evR_idem (liesOn_genFr h Z) (tested_genFr h Z))

theorem NonzeroOn.ne_zero {Z : Comp Xo c} {f : Rul Xo c} (h : NonzeroOn Z f) : f ≠ 0 := by
  rintro rfl; exact h (map_zero _)

theorem exists_gen_val_ne_zero {R : ℕ} (hR : Odd R) (h1 : 1 < R) (hM : R ^ 4 ∣ l.M) {n : ℕ} (x₀ : Fin n → Dw.La)
    {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) :
    ∃ u : Fin n → LatMod Dw R, ∀ v, TauValAt Xo c R (fun _ : Unit => 1) (fun _ => shiftFam R x₀ u) y v → v ≠ 0 := by
  let φ : K →ₐ[c.F] AlgebraicClosure K := IsScalarTower.toAlgHom c.F K _
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c K _ φ y
  obtain ⟨ev, hev⟩ := exists_isLevOf_geometric Xo c hM z.x
  choose w hw using fun q => (existsUnique_nullVal GlobalTheory.firstFiveLaws.1 hR hev.2.1 q).exists
  obtain ⟨u, hu⟩ := GlobalTheory.exists_shift_nullVal_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR h1 _ z ev w hev.2.1 hw n x₀
    (LinearEquiv.refl _ _)
  refine ⟨u, fun v hv h0 => ?_⟩
  have := TauValAt.map_eq hR φ hz hv (tauValAt_self hev hw)
  rw [h0, map_zero, tauExpr, Fintype.sum_unique, Int.cast_one, _root_.one_mul] at this
  exact Finset.prod_ne_zero_iff.2 (fun b _ => hu b) this.symm

theorem exists_isGenRule_nonzeroOn {R : ℕ} (hR : Odd R) (h1 : 1 < R) (hM : R ^ 4 ∣ l.M) {n : ℕ} (x₀ : Fin n → Dw.La)
    (Z : Comp Xo c) : ∃ u f, IsGenRule Xo c R x₀ u f ∧ NonzeroOn Z f := by
  have h := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨u, hu⟩ := exists_gen_val_ne_zero hR h1 hM x₀ (genFr h Z)
  obtain ⟨f, hf, -⟩ := existsUnique_isTauRule Xo c (fun _ : Unit => 1) (fun _ => shiftFam R x₀ u) hR hM
  exact ⟨u, f, hf, hu _ (hf.tauValAt_evR hR (tested_genFr h Z))⟩

section Theta

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c}

def thetaOn (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (K : (Rul Xo c)ˣ) (f : Rul Xo c) : Rul Xo c :=
  f ^ 8 * (K : Rul Xo c) ^ (Dw.p + Dw.q) * (FlatSec.shift h s fun _ => -(4 * ((Dw.p + Dw.q : ℕ) : ℤ))).sig

theorem shift_sig (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (m : ℕ) :
    (FlatSec.shift h s fun _ => -(4 * (m : ℤ))).sig = idem Z * ∏ τ, (s τ).sig ^ (4 * m) := by
  have h1 : ∀ τ, ((s τ).zpow (- -(4 * (m : ℤ)))).sig = idem Z * (s τ).sig ^ (4 * m) := fun τ => by
    have a : (- -(4 * (m : ℤ))).toNat = 4 * m := by omega
    have b : (- - -(4 * (m : ℤ))).toNat = 0 := by omega
    rw [(ConstSec.zpow_spec _ _).1, a, b, pow_zero, _root_.mul_one]
  rw [(FlatSec.shift_spec h s _).1]
  simp only [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← _root_.mul_assoc, ← pow_succ',
    (show IsIdempotentElem (idem Z) from idem_mul_idem Z).pow_succ_eq]
  convert rfl

theorem pow_mem_secZ {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (m : ℕ) : f ^ m ∈ secZ Xo c (m • e) := by
  induction m with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_secZ
  | succ m ih => rw [pow_succ, succ_nsmul]; exact mul_mem_secZ ih hf

theorem ex_tau_key (m : ℕ) :
    (8 • fun i => (ex Dw 0 m i : ℤ)) + m • (4 : ℤ) • keyEx Dw =
      exOf Dw ((8 * (m : ℤ)) • hodgeWt Dw + parWt Dw fun _ => 4 * (m : ℤ)) 0 := by
  have h : ((8 * (m : ℤ)) • hodgeWt Dw + parWt Dw fun _ => 4 * (m : ℤ)) =
      weightOf Dw (fun y => (((0 : (E →+* ℂ) × ℕ → ℕ) y : ℕ) : ℤ)) ((4 * m : ℕ) : ℤ) := by
    funext τ j
    simp only [weightOf, hodgeWt, barWt, parWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    split_ifs <;> push_cast <;> ring
  rw [h, ← exKey_two_mul]
  funext i
  cases i <;> simp [exKey, keyEx, ex] <;> ring

theorem pow_mul_key_mem_secZ {m : ℕ} {K f : Rul Xo c} (hK : K ∈ secZ Xo c ((4 : ℤ) • keyEx Dw))
    (hf : f ∈ sec Xo c 0 m) :
    f ^ 8 * K ^ m ∈ secZ Xo c (exOf Dw ((8 * (m : ℤ)) • hodgeWt Dw + parWt Dw fun _ => 4 * (m : ℤ)) 0) := by
  rw [← secZ_nat] at hf
  exact ex_tau_key (Dw := Dw) m ▸ mul_mem_secZ (pow_mem_secZ hf 8) (pow_mem_secZ hK m)

theorem thetaOn_mem_secZ (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) {K : (Rul Xo c)ˣ}
    (hK : (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw)) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 (Dw.p + Dw.q)) :
    thetaOn h s K f ∈ secZ Xo c (exOf Dw ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • hodgeWt Dw) 0) := by
  have h1 := mul_mem_secZ (pow_mul_key_mem_secZ hK hf)
    (FlatSec.shift h s fun _ => -(4 * ((Dw.p + Dw.q : ℕ) : ℤ))).sig_mem
  rw [← exOf_add'] at h1
  have e : ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • hodgeWt Dw + parWt Dw fun _ => 4 * ((Dw.p + Dw.q : ℕ) : ℤ)) +
      parWt Dw (fun _ => -(4 * ((Dw.p + Dw.q : ℕ) : ℤ))) = (8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • hodgeWt Dw := by
    funext τ j
    simp [parWt]
  rw [e] at h1
  exact h1

theorem thetaOn_mem_suppOn (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (K : (Rul Xo c)ˣ) (f : Rul Xo c) :
    thetaOn h s K f ∈ suppOn Z := mul_mem_suppOn _ (ConstSec.sig_mem_suppOn _)

theorem nonzeroOn_thetaOn_iff (h : HasPts U Z) (s : ∀ τ, FlatSec U x Z τ) (K : (Rul Xo c)ˣ) (f : Rul Xo c) :
    NonzeroOn Z (thetaOn h s K f) ↔ NonzeroOn Z f := by
  have h1 := congrArg (genVal Z) (FlatSec.shift h s fun _ => -(4 * ((Dw.p + Dw.q : ℕ) : ℤ))).mul_inv
  rw [map_mul, genVal_idem] at h1
  have h2 := left_ne_zero_of_mul_eq_one h1
  have h3 := (K.isUnit.map (genVal Z)).ne_zero
  rw [NonzeroOn, NonzeroOn, thetaOn, map_mul, map_mul, map_pow, map_pow, mul_ne_zero_iff_right h2,
    mul_ne_zero_iff_right (pow_ne_zero _ h3), pow_ne_zero_iff (by norm_num)]

end Theta

example (τ : Psi H) (i : Fin (Dw.mult τ.1)) (j : Fin (Dw.mult (conjEmb τ.1))) (hi : (i : ℕ) < Dw.p)
    (hj : (j : ℕ) < Dw.q) (N : ℤ) : exOf Dw ((8 * N) • hodgeWt Dw) 0 (some ⟨τ.1, i⟩) = 0 ∧
      exOf Dw ((8 * N) • hodgeWt Dw) 0 (some ⟨conjEmb τ.1, j⟩) = 8 * N ∧ exOf Dw ((8 * N) • hodgeWt Dw) 0 none = 0 := by
  refine ⟨(wtOf_big _ 0 τ i hi).trans ?_, (wtOf_small _ 0 τ j hj).trans ?_, rfl⟩ <;> simp [hodgeWt, barWt, hi]

example {R : ℕ} (hR : Odd R) (hM : R ^ 4 ∣ l.M) (x₀ : Fin 0 → Dw.La) (u : Fin 0 → LatMod Dw R) :
    IsGenRule Xo c R x₀ u 1 := fun p y => by
  obtain ⟨B, _, _, φ, y', ev, w, hφ, hm, hev, hw⟩ := exists_cover hR hM y
  exact ⟨B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, by simp [tauExpr]⟩

example {R : ℕ} (hR : Odd R) (hM : R ^ 4 ∣ l.M) [Fintype (LatMod Dw R)] {n : ℕ} (x₀ : Fin n → Dw.La) (Z : Comp Xo c) :
    IsTauZero Xo c R x₀ 0 0 ∧ ¬ NonzeroOn Z 0 := by
  refine ⟨fun p y => ?_, fun h => h.ne_zero rfl⟩
  obtain ⟨B, _, _, φ, y', ev, w, hφ, hm, hev, hw⟩ := exists_cover hR hM y
  exact ⟨B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, by simp [tauExpr]⟩

end GlobalTheory.ThetaConst
