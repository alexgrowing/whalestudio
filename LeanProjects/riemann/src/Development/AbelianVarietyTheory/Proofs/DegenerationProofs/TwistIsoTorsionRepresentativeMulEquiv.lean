import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.Relabel.TwIso
variable {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def twP (r : Oˣ) (y : N.X) (g : N.Gt) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * r ^ β.be y z, (N.twG β r g (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩

theorem twistMap_add_mul (r : Oˣ) (y y' : N.X) (g g' : N.Gt) :
    twP β u r (y + y') (g * g') = twP β u r y g * twP β u r y' g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * r ^ β.be (y + y') z =
      g.s z * r ^ β.be y z * (g'.s z * r ^ β.be y' z) / N.θ (N.c z) g.b g'.b
    rw [map_add, LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_mul_mul (r r' : Oˣ) (y : N.X) (g g' : N.Gt) :
    twP β u (r * r') y (g * g') = twP β u r y g * twP β u r' y g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * (r * r') ^ β.be y z =
      g.s z * r ^ β.be y z * (g'.s z * r' ^ β.be y z) / N.θ (N.c z) g.b g'.b
    rw [mul_zpow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_pow (r : Oˣ) (y : N.X) (g : N.Gt) (m : ℕ) : twP β u r y g ^ m = twP β u (r ^ m) y (g ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show (1 : Oˣ) = 1 * 1 ^ β.be y z
    simp
  | succ m ih =>
    rw [pow_succ (twP β u r y g) m, ih, ← twistMap_mul_mul, ← pow_succ, ← pow_succ]

theorem twistMap_io (y : N.X) : twP β u u y (N.io y) = (N.twist β u).io y :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show N.τ y z * u ^ β.be y z = (N.twist β u).τ y z
    rw [NumD.twist_τ])

theorem twistMap_nsmul (r : Oˣ) (j : ℕ) (y : N.X) (g : N.Gt) : twP β u r (j • y) g = twP β u (r ^ j) y g :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * r ^ β.be (j • y) z = g.s z * (r ^ j) ^ β.be y z
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast])

theorem twistMap_bijective₂ (r : Oˣ) (y : N.X) : Function.Bijective (twP β u r y) := by
  constructor
  · intro g g' h
    have hb : g.b = g'.b := congrArg (fun x => x.b) h
    have hs : ∀ z, g.s z * r ^ β.be y z = g'.s z * r ^ β.be y z :=
      fun z => congrFun (congrArg (fun x => x.s) h) z
    exact NumD.Gt.ext hb (funext fun z => mul_right_cancel (hs z))
  · intro h
    refine ⟨⟨h.b, fun z => h.s z * r⁻¹ ^ β.be y z,
      (N.twG β r⁻¹ ⟨h.b, h.s, h.mult⟩ (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩, ?_⟩
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show h.s z * r⁻¹ ^ β.be y z * r ^ β.be y z = h.s z
    rw [inv_zpow, inv_mul_cancel_right]

def isoG {M M' : NumD O} (J : NumD.Iso M M') : M.Gt →* M'.Gt :=
  MonoidHom.mk' (NumD.Hom.ofIso J).img fun g h =>
    (((NumD.Hom.ofIso J).rel_iff _ _).1 (((NumD.Hom.ofIso J).rel_img g).mul ((NumD.Hom.ofIso J).rel_img h))).symm

theorem rel_iff_isoG {M M' : NumD O} (J : NumD.Iso M M') (g : M.Gt) (g' : M'.Gt) : J.Rel g g' ↔ g' = isoG J g := by
  rw [← NumD.Hom.ofIso_rel, NumD.Hom.rel_iff]
  exact Iff.rfl

theorem isoG_io {M M' : NumD O} (J : NumD.Iso M M') (y : M.X) : isoG J (M.io y) = M'.io (J.e y) :=
  (((NumD.Hom.ofIso J).rel_iff _ _).1 ((NumD.Hom.ofIso J).rel_io y)).symm

private theorem eq_of_div_eq_div_div {G : Type*} [CommGroup G] {a b c d x y : G} (h1 : a = b) (h2 : c = d)
    (h : x / y = a / b / (c / d)) : x = y := by
  rw [div_eq_one.mpr h1, div_eq_one.mpr h2, div_one] at h
  exact div_eq_one.mp h

theorem isoG_bijective {M M' : NumD O} (J : NumD.Iso M M') : Function.Bijective (isoG J) := by
  refine ⟨(injective_iff_map_eq_one (isoG J)).2 fun g hg => ?_, fun g' => ?_⟩
  · obtain ⟨hb, hs⟩ := (rel_iff_isoG J g 1).2 hg.symm
    have hgb : g.b = 1 := by
      have h1 : J.φ g.b = 1 := by rw [← hb]; rfl
      exact (MulEquiv.map_eq_one_iff J.φ).1 h1
    refine NumD.Gt.ext hgb (funext fun χ => ?_)
    have h2 := hs χ
    simp only [NumD.Gt.generator_inv_base, hgb, _root_.mul_one, J.h_one, _root_.one_mul] at h2
    show g.s χ = 1
    exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
  · refine ⟨⟨J.φ.symm g'.b, fun χ => g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)), fun χ χ' => ?_⟩, ?_⟩
    · have hm := g'.mult (J.e χ) (J.e χ')
      have ht := J.θ_eq (M.c χ) (M.c χ') (J.φ.symm g'.b)
      rw [J.c_eq, J.c_eq, ← map_add J.e χ χ'] at hm
      rw [MulEquiv.apply_symm_apply] at ht
      rw [M.c_add]
      refine eq_of_div_eq_div_div hm ht ?_
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    · refine ((rel_iff_isoG J _ g').1 ⟨(J.φ.apply_symm_apply _).symm, fun χ => ?_⟩).symm
      show g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) = g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)) * J.h (M.c χ) * J.h (J.φ.symm g'.b)
      rw [mul_assoc _ (J.h (M.c χ)), div_mul_cancel]

variable {β u} (J : NumD.Iso (N.twist β u) N')

theorem twJ_elim {r : Oˣ} {j : ℕ} {q : N.QT j} {q' : N'.QT j} (h : TwJ β u r J q q') :
    q'.1.1.toAdd = J.e q.1.1.toAdd ∧ q'.1.2 = isoG J (twP β u r q.1.1.toAdd q.1.2) := by
  obtain ⟨p, ⟨h1, h2, h3⟩, e, hr⟩ := h
  have hp : p.1.2 = twP β u r q.1.1.toAdd q.1.2 := NumD.Gt.ext h2 (funext h3)
  refine ⟨e.trans (congrArg (fun x => J.e (Multiplicative.toAdd x)) h1), ?_⟩
  rw [← hp]
  exact (rel_iff_isoG J _ _).1 hr

def twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q : N.QT j) : (N.twist β u).QT j :=
  ⟨(q.1.1, twP β u r q.1.1.toAdd q.1.2), by
    change twP β u r q.1.1.toAdd q.1.2 ^ j = (N.twist β u).io q.1.1.toAdd
    rw [twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]⟩

def tauHom {r : Oˣ} {j : ℕ} (h : r ^ j = u) : N.QT j →* N'.QT j :=
  MonoidHom.mk' (fun q => ⟨(Multiplicative.ofAdd (J.e q.1.1.toAdd), isoG J (twP β u r q.1.1.toAdd q.1.2)), by
      change isoG J (twP β u r q.1.1.toAdd q.1.2) ^ j = N'.io (J.e q.1.1.toAdd)
      rw [← map_pow, twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]
      exact isoG_io J _⟩)
    fun q q' => Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add J.e q.1.1.toAdd q'.1.1.toAdd))
      ((congrArg (isoG J) (twistMap_add_mul β u r q.1.1.toAdd q'.1.1.toAdd q.1.2 q'.1.2)).trans (map_mul _ _ _)))

theorem tauHom_bijective {r : Oˣ} {j : ℕ} (h : r ^ j = u) : Function.Bijective (tauHom J h) := by
  constructor
  · intro q₁ q₂ hq
    have h1 : J.e q₁.1.1.toAdd = J.e q₂.1.1.toAdd := congrArg (fun q => q.1.1.toAdd) hq
    have h2 : isoG J (twP β u r q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r q₂.1.1.toAdd q₂.1.2) :=
      congrArg (fun q => q.1.2) hq
    have e1 : q₁.1.1.toAdd = q₂.1.1.toAdd := J.e.injective h1
    rw [e1] at h2
    have e2 := (twistMap_bijective₂ β u r _).1 ((isoG_bijective J).1 h2)
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective e1) e2)
  · intro q'
    obtain ⟨g', hg'⟩ := (isoG_bijective J).2 q'.1.2
    obtain ⟨g, hg⟩ := (twistMap_bijective₂ β u r (J.e.symm q'.1.1.toAdd)).2 g'
    refine ⟨⟨(Multiplicative.ofAdd (J.e.symm q'.1.1.toAdd), g), ?_⟩, ?_⟩
    · have hq := N'.mem_QT.1 q'.2
      have e0 : twP β u r (J.e.symm q'.1.1.toAdd) g ^ j = twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j) :=
        (twistMap_pow β u r (J.e.symm q'.1.1.toAdd) g j).trans
          (congrArg (fun s => twP β u s (J.e.symm q'.1.1.toAdd) (g ^ j)) h)
      have hq2 : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j)) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) e0.symm).trans ((map_pow (isoG J) _ j).trans
          ((congrArg (fun t => isoG J t ^ j) hg).trans ((congrArg (· ^ j) hg').trans hq)))
      have hio : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (N.io (J.e.symm q'.1.1.toAdd))) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) (twistMap_io β u (J.e.symm q'.1.1.toAdd))).trans
          ((isoG_io J _).trans (congrArg N'.io (J.e.apply_symm_apply _)))
      exact N.mem_QT.2 ((twistMap_bijective₂ β u u _).1 ((isoG_bijective J).1 (hq2.trans hio.symm)))
    · refine Subtype.ext (Prod.ext ?_ ?_)
      · show Multiplicative.ofAdd (J.e (J.e.symm q'.1.1.toAdd)) = q'.1.1
        rw [J.e.apply_symm_apply]
        rfl
      · exact (congrArg (isoG J) hg).trans hg'

theorem tauHom_qTriv {r : Oˣ} {j : ℕ} (h : r ^ j = u) (z : N.X) : tauHom J h (N.qTriv j z) = N'.qTriv j (J.e z) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg Multiplicative.ofAdd (map_nsmul J.e j z)
  · exact (congrArg (isoG J) ((twistMap_nsmul β u r j z (N.io z)).trans
      (show twP β u (r ^ j) z (N.io z) = (N.twist β u).io z by rw [h, twistMap_io]))).trans (isoG_io J z)

theorem wp_twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q₁ q₂ : N.QT j) :
    (N.twist β u).wp (twQ (β := β) h q₁) (twQ h q₂) = N.wp q₁ q₂ := by
  show q₁.1.2.s q₂.1.1.toAdd * r ^ β.be q₁.1.1.toAdd q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * r ^ β.be q₂.1.1.toAdd q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b) =
    q₁.1.2.s q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b)
  rw [β.symm q₂.1.1.toAdd q₁.1.1.toAdd]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel

end GlobalTheory.Relabel.TwIso

open GlobalTheory.Relabel.TwIso in

theorem GlobalTheory.Relabel.twJ_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  intro O _ N N' k β u J
  refine ⟨fun r j h => ?_, fun r₁ r₂ n n' m q₁ q₂ q₁' q₂' hr e1 e2 t1 t2 => ?_⟩
  · refine ⟨MulEquiv.ofBijective (tauHom J h) (tauHom_bijective J h), fun q q' => ?_,
      fun q₁ q₂ => ?_, fun q₁ q₂ => ?_⟩
    · show tauHom J h q = q' ↔ _
      constructor
      · rintro rfl
        exact ⟨twQ (β := β) h q, ⟨rfl, rfl, fun _ => rfl⟩, rfl, (rel_iff_isoG J _ _).2 rfl⟩
      · intro ht
        obtain ⟨e, he⟩ := twJ_elim J ht
        refine Subtype.ext (Prod.ext ?_ he.symm)
        exact (congrArg Multiplicative.ofAdd e).symm
    · rw [NumD.qEq_iff, NumD.qEq_iff]
      show (∃ z, q₂ = q₁ * N.qTriv j z) ↔ ∃ z, tauHom J h q₂ = tauHom J h q₁ * N'.qTriv j z
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨J.e z, (map_mul _ _ _).trans (congrArg _ (tauHom_qTriv J h z))⟩
      · rintro ⟨z, hz⟩
        refine ⟨J.e.symm z, (tauHom_bijective J h).1 ?_⟩
        exact hz.trans ((congrArg (tauHom J h q₁ * ·) ((tauHom_qTriv J h (J.e.symm z)).trans
          (congrArg (N'.qTriv j) (J.e.apply_symm_apply z))).symm).trans (map_mul (tauHom J h) q₁ _).symm)
    · have hrel : ∀ q : N.QT j, (NumD.Hom.ofIso J).Rel (twQ (β := β) h q).1.2 (tauHom J h q).1.2 :=
        fun q => (NumD.Hom.ofIso J).rel_img _
      have hw := NumD.Hom.wp_eq (NumD.Hom.ofIso J) (twQ (β := β) h q₁) (twQ (β := β) h q₂)
        (tauHom J h q₁) (tauHom J h q₂) rfl (hrel q₁) rfl (hrel q₂)
      rw [wp_twQ] at hw
      show N'.wp (tauHom J h q₁) (tauHom J h q₂) = _
      rw [hw]
      exact Units.ext rfl
  · obtain ⟨a1, b1⟩ := twJ_elim J t1
    obtain ⟨a2, b2⟩ := twJ_elim J t2
    refine ⟨?_, ?_⟩
    · exact Multiplicative.toAdd.injective
        (a1.trans ((congrArg (fun x => J.e (Multiplicative.toAdd x)) e1).trans a2.symm))
    · rw [b1, b2]
      calc isoG J (twP β u r₁ q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r₂ q₂.1.1.toAdd q₂.1.2 ^ m) := by
            rw [twistMap_pow, hr, e1, e2]
        _ = _ := map_pow _ _ _
end
