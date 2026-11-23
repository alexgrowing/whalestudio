import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFrames
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioFieldStatement

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology

section Pt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_basic (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) (V : X.Opens) (hV : centre z ∈ V) :
    ∃ (cc : (k : K) → J k) (f : Ω), InFrameDomain y cc f w ∧ InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) cc p → unitAt ξ p f → p.1 ∈ V := by
  obtain ⟨cc, hcc⟩ := hT.cover ⟨centre z, h⟩
  obtain ⟨U, hU, hUiff⟩ := hT.affine cc hcc.1
  have hzU : centre z ∈ U := (hUiff _).2 ⟨h, hcc⟩
  obtain ⟨g, hgV, hzg⟩ := hU.exists_basicOpen_le (V := V) ⟨centre z, hV⟩ hzU
  have hsu : IsUnit (X.presheaf.germ U (centre z) hzU g) := (X.mem_basicOpen g _ hzU).1 hzg
  refine ⟨cc, genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU g),
    ChartFrames.inFrameDomain_of_unitAt hT hz h hcc (ChartFrames.unitAt_of_isUnit hsu), hcc, ?_⟩
  intro p hp hpf
  have hpU : p.1 ∈ U := (hUiff p.1).2 ⟨p.2, hp⟩
  have hfp := ChartFrames.genMap_germ_eq g p ⟨centre z, h⟩ hpU hzU
  apply hgV
  rw [X.mem_basicOpen g _ hpU]
  exact ChartFrames.isUnit_of_unitAt hT.gen (by rw [hfp]; exact hpf)

theorem analyticAt_eval {A : Type} {n : ℕ} {q : (Fin n → ℂ) → A → ℂ} {t₀ : Fin n → ℂ}
    (hq : ∀ i, AnalyticAt ℂ (fun t => q t i) t₀) (p : MvPolynomial A ℤ) :
    AnalyticAt ℂ (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) t₀ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.eval_C]
    exact analyticAt_const
  | add p r hp hr =>
    simp only [map_add]
    exact hp.add hr
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    exact hp.mul (hq i)

private theorem valAt_unique_lemma (hg : IsCptGen ξ) {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r r' : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hg.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

private theorem valAt_mul_lemma_2 {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, s1, hs, hs'⟩ := h
  obtain ⟨hz', s2, ht, ht'⟩ := h'
  refine ⟨hz, s1 * s2, by rw [map_mul, hs, ht], ?_⟩
  rw [← hs', ← ht']
  exact map_mul _ s1 s2

private theorem valAt_sub_lemma_3 {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a - b) (r - s) := by
  obtain ⟨hz, s1, hs, hs'⟩ := h
  obtain ⟨hz', s2, ht, ht'⟩ := h'
  refine ⟨hz, s1 - s2, by rw [map_sub, hs, ht], ?_⟩
  rw [← hs', ← ht']
  exact map_sub _ s1 s2

private theorem valAt_add_lemma_12 {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, s1, hs, hs'⟩ := h
  obtain ⟨hz', s2, ht, ht'⟩ := h'
  refine ⟨hz, s1 + s2, by rw [map_add, hs, ht], ?_⟩
  rw [← hs', ← ht']
  exact map_add _ s1 s2

private theorem valAt_intCast_lemma_13 {z : Spec (CommRingCat.of ℂ) ⟶ X} (h : genPt ξ ⤳ centre z) (m : ℤ) :
    ValAt ξ z (m : Ω) (m : ℂ) := by
  refine ⟨h, (m : ↑(X.presheaf.stalk (centre z))), by simp, ?_⟩
  exact map_intCast _ m

private theorem valAt_inv_lemma_4 {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r : ℂ}
    (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨hz, t, ht, ht'⟩ := h
  have hu : IsUnit t :=
    (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit t (by rw [ht']; exact hr.isUnit)
  have key : ∀ {L : Type} [Field L] (φ : ↑(X.presheaf.stalk (centre z)) →+* L),
      φ ↑hu.unit⁻¹ = (φ t)⁻¹ := fun φ =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu.val_inv_mul, map_one])
  refine ⟨hz, ↑hu.unit⁻¹, ?_, ?_⟩
  · exact (key (genMap ξ ⟨centre z, hz⟩)).trans (congrArg (·⁻¹) ht)
  · exact (key (Scheme.stalkClosedPointTo z).hom).trans (congrArg (·⁻¹) ht')

private theorem unitAt_of_valAt_lemma_5 {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r : ℂ}
    (h : ValAt ξ z a r) (hr : r ≠ 0) : ∃ hz : genPt ξ ⤳ centre z, unitAt ξ ⟨centre z, hz⟩ a := by
  obtain ⟨hz, t, ht, ht'⟩ := h
  have hu : IsUnit t :=
    (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit t (by rw [ht']; exact hr.isUnit)
  exact ⟨hz, ht ▸ ChartFrames.unitAt_of_isUnit hu⟩

private theorem valAt_sum_lemma_6 {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {I : Type*}
    (s : Finset I) (f : I → Ω) (v : I → ℂ) (h : ∀ i ∈ s, ValAt ξ z (f i) (v i)) :
    ValAt ξ z (∑ i ∈ s, f i) (∑ i ∈ s, v i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using valAt_intCast_lemma_13 (ξ := ξ) hz 0
  | @cons i s hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact valAt_add_lemma_12 (h i (Finset.mem_cons_self i s)) (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

private theorem valAt_prod_lemma_7 {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {I : Type*}
    (s : Finset I) (f : I → Ω) (v : I → ℂ) (h : ∀ i ∈ s, ValAt ξ z (f i) (v i)) :
    ValAt ξ z (∏ i ∈ s, f i) (∏ i ∈ s, v i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using valAt_intCast_lemma_13 (ξ := ξ) hz 1
  | @cons i s hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact valAt_mul_lemma_2 (h i (Finset.mem_cons_self i s)) (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

private theorem valAt_pow_lemma_8 {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ}
    (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  simpa using valAt_prod_lemma_7 hz (Finset.range n) (fun _ => a) (fun _ => r) (fun _ _ => h)

private theorem eval₂_div_lemma_9 {L : Type*} [Field L] {d : K → ℕ} {p : MRing J} (hp : IsMultiHomog p d)
    (u : (Σ k, J k) → L) (c : (k : K) → J k) :
    MvPolynomial.eval₂ (Int.castRingHom L) u p / ∏ k, u ⟨k, c k⟩ ^ d k =
      ∑ m ∈ p.support, ((MvPolynomial.coeff m p : ℤ) : L) * ∏ k, ∏ i, (u ⟨k, i⟩ / u ⟨k, c k⟩) ^ m ⟨k, i⟩ := by
  rw [MvPolynomial.eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eq_intCast, mul_div_assoc, Fintype.prod_sigma, ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hp m hm k]
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

private theorem valAt_ratio_lemma_10 {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (hz : CoordsAt ξ y z w) (h0 : genPt ξ ⤳ centre z) (c : (k : K) → J k) (hc : ∀ k, IsUnit (w ⟨k, c k⟩))
    {d : K → ℕ} {p : MRing J} (hp : IsMultiHomog p d) :
    ValAt ξ z (MvPolynomial.aeval y p / ∏ k, y ⟨k, c k⟩ ^ d k)
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) p) / ∏ k, w ⟨k, c k⟩ ^ d k) := by
  have hr : ∀ k i, ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro k i
    obtain ⟨r, hr, hw⟩ := (hz.2 k (c k) (hc k)).2 i
    rwa [hw, mul_div_assoc, div_self (hc k).ne_zero, _root_.mul_one]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map, algebraMap_int_eq, eval₂_div_lemma_9 hp, eval₂_div_lemma_9 hp]
  apply valAt_sum_lemma_6 h0
  intro m _
  apply valAt_mul_lemma_2 (valAt_intCast_lemma_13 h0 _)
  apply valAt_prod_lemma_7 h0
  intro k _
  apply valAt_prod_lemma_7 h0
  intro i _
  exact valAt_pow_lemma_8 h0 (hr k i) _

private theorem valAt_of_isValueAt_lemma_11 {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (hz : CoordsAt ξ y z w) (h0 : genPt ξ ⤳ centre z) {f : Ω} {d : K → ℕ} {g p : MRing J}
    (hg : IsMultiHomog g d) (hp : IsMultiHomog p d) (hyp : MvPolynomial.aeval y p ≠ 0)
    (hgf : MvPolynomial.aeval y g = f * MvPolynomial.aeval y p)
    (hwp : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) p) ≠ 0) :
    ValAt ξ z f (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) /
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) p)) := by
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hz.2 k (c k) (hc k)).1
  have hD : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hDw : ∏ k, w ⟨k, c k⟩ ^ d k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
  have e1 : f = (MvPolynomial.aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) *
      (MvPolynomial.aeval y p / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ := by
    rw [hgf]
    field_simp
  have e2 : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) /
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) p) =
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) / ∏ k, w ⟨k, c k⟩ ^ d k) *
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) p) / ∏ k, w ⟨k, c k⟩ ^ d k)⁻¹ := by
    field_simp
  rw [e1, e2]
  exact valAt_mul_lemma_2 (valAt_ratio_lemma_10 hz h0 c hc hg)
    (valAt_inv_lemma_4 (valAt_ratio_lemma_10 hz h0 c hc hp) (div_ne_zero hwp hDw))

theorem exists_val_fam (hT : CoordTie ℤ ξ (segreCoord y)) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ}
    {gm : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hq : ∀ q, AnalyticAt ℂ (fun t => gm t q) 0)
    {z₀ : Spec (CommRingCat.of ℂ) ⟶ X} (hz : CoordsAt ξ y z₀ (gm 0)) {a : Ω} {v₀ : ℂ} (hv : ValAt ξ z₀ a v₀) :
    ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = v₀ ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z (gm t) → ValAt ξ z a (F t) := by
  have h0 : genPt ξ ⤳ centre z₀ := hall _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v₀ + (m : ℂ) ≠ 0 := by
    by_cases h1 : v₀ + 1 = 0
    · refine ⟨0, ?_⟩
      intro h2
      simp only [Int.cast_zero, add_zero] at h2
      rw [h2] at h1
      norm_num at h1
    · exact ⟨1, by simpa using h1⟩
  have hv' : ValAt ξ z₀ (a + m) (v₀ + m) := valAt_add_lemma_12 hv (valAt_intCast_lemma_13 h0 m)
  obtain ⟨h0', hu⟩ := unitAt_of_valAt_lemma_5 hv' hm
  obtain ⟨cc, hcc⟩ := hT.cover ⟨centre z₀, h0'⟩
  obtain ⟨-, v, ⟨d, g, p, hg, hp, hyp, hgf, hwp, rfl⟩, -⟩ :=
    ChartFrames.inFrameDomain_of_unitAt hT hz h0' hcc hu
  have hv0 := valAt_unique_lemma hT.gen (valAt_of_isValueAt_lemma_11 hz h0' hg hp hyp hgf hwp) hv'
  have hA := (analyticAt_eval hq g).div (analyticAt_eval hq p) hwp
  refine ⟨fun t => MvPolynomial.eval (gm t) (MvPolynomial.map (Int.castRingHom ℂ) g) /
      MvPolynomial.eval (gm t) (MvPolynomial.map (Int.castRingHom ℂ) p) - m, hA.sub analyticAt_const, ?_, ?_⟩
  · show _ - _ = _
    rw [hv0]
    ring
  · filter_upwards [(analyticAt_eval hq p).continuousAt.eventually_ne hwp] with t ht z hzt
    have h5 := valAt_sub_lemma_3 (valAt_of_isValueAt_lemma_11 hzt (hall _) hg hp hyp hgf ht) (valAt_intCast_lemma_13 (hall _) m)
    rwa [add_sub_cancel_right] at h5

theorem valAt_int {z : Spec (CommRingCat.of ℂ) ⟶ X} (h : genPt ξ ⤳ centre z) (m : ℤ) : ValAt ξ z (m : Ω) (m : ℂ) :=
  ⟨h, m, map_intCast _ m, map_intCast (Scheme.stalkClosedPointTo z).hom m⟩

theorem exists_val_ne {z : Spec (CommRingCat.of ℂ) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ v : ℂ, v ≠ 0 ∧ ValAt ξ z a v := by
  obtain ⟨ha0, ⟨s, hs⟩, ⟨t, ht⟩⟩ := ha
  have hu : IsUnit s := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * t) with h1 | h1
    · exact isUnit_of_mul_isUnit_left h1
    · exfalso
      have h2 := h1.map (genMap ξ ⟨centre z, h⟩)
      rw [map_sub, map_one, map_mul, hs, ht, mul_inv_cancel₀ ha0, sub_self] at h2
      exact not_isUnit_zero h2
  refine ⟨(Scheme.stalkClosedPointTo z).hom s, ?_, h, s, hs, rfl⟩
  exact (hu.map _).ne_zero

end Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

private theorem exists_cst_val_lemma (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (b : 𝓞 c.F) :
    ∃ r : ℂ, ValAt 𝔐.ξ z (𝔐.cst (algebraMap (𝓞 c.F) c.F b)) r := by
  have hgen : ∀ (h : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (𝓞 c.F))),
      h = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) → ∀ x,
      (Scheme.stalkClosedPointTo h).hom ((Spec (CommRingCat.of (𝓞 c.F))).presheaf.germ ⊤ _ trivial x) =
        𝔐.cst (algebraMap _ _ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).hom x)) := by
    rintro h rfl x
    exact congrArg (fun φ => φ.hom x) (Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of (𝓞 c.F))
      (S := CommRingCat.of Ω) (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))))
  have hG : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) :=
    𝔐.cst_over
  have h := 𝔐.all (centre z)
  have e2 := hgen _ hG ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom b)
  rw [Scheme.stalkClosedPointTo_comp] at e2
  have hsp := Scheme.Hom.stalkSpecializes_stalkMap (𝔐.f ≫ Y.s) _ _ h
  refine ⟨_, h, (𝔐.f ≫ Y.s).stalkMap (centre z) ((Spec (CommRingCat.of (𝓞 c.F))).presheaf.germ ⊤ _ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom b)), ?_, rfl⟩
  have hm : (Spec (CommRingCat.of (𝓞 c.F))).presheaf.germ ⊤ _ trivial ≫ (𝔐.f ≫ Y.s).stalkMap (centre z) ≫
      𝔐.X.presheaf.stalkSpecializes h = (Spec (CommRingCat.of (𝓞 c.F))).presheaf.germ ⊤ _ trivial ≫
      (𝔐.f ≫ Y.s).stalkMap (genPt 𝔐.ξ) := by
    rw [← hsp, ← Category.assoc]
    congr 1
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo 𝔐.ξ).hom ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom b)) hm
  simp only [Iso.inv_hom_id_apply] at e2
  exact h3.trans e2

theorem exists_emb (𝔐 : HodgeCpt Y S y) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, J k) → ℂ}
    (hz : CoordsAt 𝔐.ξ y z w) : ∃ s : c.F →+* ℂ, ∀ a, ValAt 𝔐.ξ z (𝔐.cst a) (s a) := by
  have h0 : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hex : ∀ a : c.F, ∃ r : ℂ, ValAt 𝔐.ξ z (𝔐.cst a) r := by
    intro a
    haveI := c.fin
    have hx : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ c.F |>.mpr (.of_finite ℚ a)
    obtain ⟨m, b, hm, hmb⟩ := hx.exists_nsmul_eq (𝓞 c.F)
    obtain ⟨r, hr⟩ := exists_cst_val_lemma 𝔐 z b
    have hmi : ValAt 𝔐.ξ z (m : Ω) (m : ℂ) := by
      simpa using valAt_intCast_lemma_13 (ξ := 𝔐.ξ) h0 (m : ℤ)
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hmΩ : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
    have e : 𝔐.cst a = 𝔐.cst (algebraMap (𝓞 c.F) c.F b) * (m : Ω)⁻¹ := by
      rw [← hmb, nsmul_eq_mul, map_mul, map_natCast]
      field_simp
    rw [e]
    exact ⟨_, valAt_mul_lemma_2 hr (valAt_inv_lemma_4 hmi hmC)⟩
  choose sv hsv using hex
  have hu : ∀ a r, ValAt 𝔐.ξ z (𝔐.cst a) r → sv a = r := fun a r h =>
    valAt_unique_lemma 𝔐.tie.gen (hsv a) h
  let s : c.F →+* ℂ :=
    { toFun := sv
      map_one' := hu _ _ (by rw [map_one]; simpa using valAt_intCast_lemma_13 (ξ := 𝔐.ξ) h0 1)
      map_mul' := fun a b => hu _ _ (by rw [map_mul]; exact valAt_mul_lemma_2 (hsv a) (hsv b))
      map_zero' := hu _ _ (by rw [map_zero]; simpa using valAt_intCast_lemma_13 (ξ := 𝔐.ξ) h0 0)
      map_add' := fun a b => hu _ _ (by rw [map_add]; exact valAt_add_lemma_12 (hsv a) (hsv b)) }
  exact ⟨s, hsv⟩

theorem exists_emb_fam (𝔐 : HodgeCpt Y S y) {n : ℕ} {gm : (Fin n → ℂ) → (Σ k, J k) → ℂ}
    (hq : ∀ q, AnalyticAt ℂ (fun t => gm t q) 0) {z₀ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : CoordsAt 𝔐.ξ y z₀ (gm 0)) :
    ∃ s : c.F →+* ℂ, ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (gm t) →
      ∀ a, ValAt 𝔐.ξ z (𝔐.cst a) (s a) := by
  haveI : NumberField c.F := @NumberField.mk _ _ inferInstance c.fin
  obtain ⟨s₀, hs₀⟩ := exists_emb 𝔐 hz
  have claim : ∀ a : c.F, ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X,
      CoordsAt 𝔐.ξ y z (gm t) → ∀ s : c.F →+* ℂ, (∀ b, ValAt 𝔐.ξ z (𝔐.cst b) (s b)) → s a = s₀ a := by
    intro a
    obtain ⟨F, hF, hF0, hev⟩ := exists_val_fam 𝔐.tie 𝔐.all hq hz (hs₀ a)
    have hfin : (Set.range (fun σ : c.F →+* ℂ => σ a) \ {s₀ a}).Finite := (Set.finite_range _).diff
    have hnot : F 0 ∉ Set.range (fun σ : c.F →+* ℂ => σ a) \ {s₀ a} := by
      rw [hF0]
      simp
    filter_upwards [hev, hF.continuousAt.preimage_mem_nhds (hfin.isClosed.isOpen_compl.mem_nhds hnot)]
      with t ht ht2 z hzt s hs
    have e : F t = s a := valAt_unique_lemma 𝔐.tie.gen (ht z hzt) (hs a)
    by_contra hne
    exact ht2 ⟨⟨s, e.symm⟩, by rw [Set.mem_singleton_iff, e]; exact hne⟩
  have hw : ∀ σ : c.F →+* ℂ, ∃ a, σ ≠ s₀ → σ a ≠ s₀ a := by
    intro σ
    by_cases h : σ = s₀
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨a, ha⟩ := not_forall.1 (fun h'' => h (RingHom.ext h''))
      exact ⟨a, fun _ => ha⟩
  choose wit hwit using hw
  refine ⟨s₀, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun σ => claim (wit σ)] with t ht z hzt
  obtain ⟨s, hs⟩ := exists_emb 𝔐 hzt
  have hss : s = s₀ := by
    by_contra hne
    exact hwit s hne (ht s z hzt s hs)
  subst hss
  exact hs

end AnalyticReference.An
