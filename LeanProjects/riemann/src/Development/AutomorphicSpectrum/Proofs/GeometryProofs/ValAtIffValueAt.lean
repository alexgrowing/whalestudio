import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TieValue

section Germs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem val_mul {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) :
    ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem val_add {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) :
    ValAt ξ z (a + b) (r + t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s + s', map_add _ _ _, map_add _ _ _⟩

theorem val_int (h : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

theorem val_unique (hinj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)) {a : Ω} {r t : ℂ}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z a t) : r = t := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', e, rfl⟩ := hb
  rw [hinj _ e]

theorem val_inv {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  have hs : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨u, rfl⟩ := hs
  exact ⟨h, ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)),
    map_units_inv (genMap ξ ⟨centre z, h⟩) u, map_units_inv (Scheme.stalkClosedPointTo z).hom u⟩

theorem val_eval (h : genPt ξ ⤳ centre z) {σ : Type} {u : σ → Ω} {e : σ → ℂ}
    (hu : ∀ p, ValAt ξ z (u p) (e p)) (G : MvPolynomial σ ℤ) :
    ValAt ξ z (MvPolynomial.eval₂ (Int.castRingHom Ω) u G)
      (MvPolynomial.eval₂ (Int.castRingHom ℂ) e G) := by
  induction G using MvPolynomial.induction_on with
  | C n =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
    simpa using val_int h n
  | add p q hp hq => simpa [MvPolynomial.eval₂_add] using val_add hp hq
  | mul_X p i hp => simpa [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using val_mul hp (hu i)

end Germs

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_scale {F : Type} [CommRing F] (u : (Σ k, J k) → F) (lam : K → F) {G : MRing J} {d : K → ℕ}
    (hG : IsMultiHomog G d) :
    MvPolynomial.eval₂ (Int.castRingHom F) (fun p => lam p.1 * u p) G =
      (∏ k, lam k ^ d k) * MvPolynomial.eval₂ (Int.castRingHom F) u G := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have key : ∏ p, (lam p.1 * u p) ^ m p = (∏ k, lam k ^ d k) * ∏ p, u p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, lam k ^ m ⟨k, i⟩ = lam k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  rw [key]
  ring

def chartMonomial (j : ∀ k, J k) (d : K → ℕ) : MRing J := ∏ k, MvPolynomial.X ⟨k, j k⟩ ^ d k

theorem chartMonomial_homog (j : ∀ k, J k) (d : K → ℕ) : IsMultiHomog (chartMonomial j d) d := by
  classical
  have e : chartMonomial j d =
      MvPolynomial.monomial (∑ k, Finsupp.single (⟨k, j k⟩ : Σ k, J k) (d k)) (1 : ℤ) := by
    rw [MvPolynomial.monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  intro m hm k
  rw [e] at hm
  have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  subst hm'
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single (j k)]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj h).2).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro k' _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eval_chartMonomial {F : Type} [CommRing F] (f : (Σ k, J k) → F) (j : ∀ k, J k) (d : K → ℕ)
    (hf : ∀ k, f ⟨k, j k⟩ = 1) :
    MvPolynomial.eval₂ (Int.castRingHom F) f (chartMonomial j d) = 1 := by
  simp [chartMonomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, hf]

theorem C_homog (n : ℤ) : IsMultiHomog (MvPolynomial.C n : MRing J) (0 : K → ℕ) := by
  intro m hm k
  have hm' : m = 0 := by
    rw [← MvPolynomial.monomial_zero'] at hm
    exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  simp [hm']

variable {Ω : Type} [Field Ω]

theorem chart_form (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : Ω}
    (ht : t ∈ Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ (d : K → ℕ) (G : MRing J), IsMultiHomog G d ∧
      MvPolynomial.eval₂ (Int.castRingHom Ω) (fun p => y p / y ⟨p.1, c p.1⟩) G = t := by
  have hone : ∀ k, (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) ⟨k, c k⟩ = 1 := fun k => div_self (hc k)
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨fun _ => 1, chartMonomial j fun _ => 1, chartMonomial_homog j _, ?_⟩
    simp [chartMonomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X, Finset.prod_div_distrib]
  | algebraMap r =>
    exact ⟨0, MvPolynomial.C r, C_homog r, by rw [MvPolynomial.eval₂_C]; simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨d₁, G₁, h₁, rfl⟩ := ha
    obtain ⟨d₂, G₂, h₂, rfl⟩ := hb
    refine ⟨d₁ + d₂, G₁ * chartMonomial c d₂ + G₂ * chartMonomial c d₁,
      GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_add
        (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul h₁ (chartMonomial_homog c d₂)) ?_, ?_⟩
    · rw [add_comm d₁ d₂]
      exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul h₂ (chartMonomial_homog c d₁)
    · rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
        eval_chartMonomial _ c _ hone, eval_chartMonomial _ c _ hone, _root_.mul_one, _root_.mul_one]
  | mul a b _ _ ha hb =>
    obtain ⟨d₁, G₁, h₁, rfl⟩ := ha
    obtain ⟨d₂, G₂, h₂, rfl⟩ := hb
    exact ⟨d₁ + d₂, G₁ * G₂, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul h₁ h₂,
      MvPolynomial.eval₂_mul _ _⟩

end Forms

end GlobalTheory.CompanionTheory.Ar.TieValue

namespace GlobalTheory.CompanionTheory.Ar

open TieValue in

theorem valAt_iff_isValueAt_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), genPt ξ ⤳ centre z → CoordsAt ξ y z w → ∀ (a : Ω) (v : ℂ), ValAt ξ z a v ↔ GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y a w v := by
  intro X Ω _ ξ K _ J _ y tie z w hgen hw a v
  classical
  have hinj := tie.gen.inj
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  let u : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  let e : (Σ k, J k) → ℂ := fun p => w p / w ⟨p.1, c p.1⟩
  have hu1 : ∀ k, u ⟨k, c k⟩ = 1 := fun k => div_self (hy k)
  have he1 : ∀ k, e ⟨k, c k⟩ = 1 := fun k => div_self (hwc k)
  have hue : ∀ p, ValAt ξ z (u p) (e p) := by
    rintro ⟨k, i⟩
    obtain ⟨r, hr, hwr⟩ := (hw.2 k (c k) (hc k)).2 i
    have hre : e ⟨k, i⟩ = r := by
      show w ⟨k, i⟩ / w ⟨k, c k⟩ = r
      rw [hwr, mul_div_assoc, div_self (hwc k), _root_.mul_one]
    rw [hre]
    exact hr
  have scaleY : ∀ {G : ReciprocityTheory.ChartRestriction.G.Geo.MRing J} {d : K → ℕ}, IsMultiHomog G d →
      MvPolynomial.aeval y G = (∏ k, y ⟨k, c k⟩ ^ d k) * MvPolynomial.eval₂ (Int.castRingHom Ω) u G := by
    intro G d hG
    rw [← eval_scale u (fun k => y ⟨k, c k⟩) hG, MvPolynomial.aeval_def, algebraMap_int_eq]
    congr 1
    funext p
    exact (mul_div_cancel₀ _ (hy p.1)).symm
  have scaleW : ∀ {G : ReciprocityTheory.ChartRestriction.G.Geo.MRing J} {d : K → ℕ}, IsMultiHomog G d →
      MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) G) =
        (∏ k, w ⟨k, c k⟩ ^ d k) * MvPolynomial.eval₂ (Int.castRingHom ℂ) e G := by
    intro G d hG
    rw [← eval_scale e (fun k => w ⟨k, c k⟩) hG, MvPolynomial.eval_map]
    congr 1
    funext p
    exact (mul_div_cancel₀ _ (hwc p.1)).symm
  have hM : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy k)
  have hMw : ∀ d : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hwc k)
  have hval := fun G => val_eval hgen hue G
  constructor
  · intro hv
    let p : Cpt ξ := ⟨centre z, hgen⟩
    have hchart : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
      refine ⟨Finset.prod_ne_zero_iff.mpr fun k _ => hy k, fun c' => ?_⟩
      have h1 : (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ =
          MvPolynomial.eval₂ (Int.castRingHom Ω) u (chartMonomial c' fun _ => 1) := by
        simp [chartMonomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X, Finset.prod_div_distrib, u]
      show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ regAt ξ p
      rw [h1]
      obtain ⟨_, s, hs, _⟩ := hval (chartMonomial c' fun _ => 1)
      exact ⟨s, hs⟩
    have ha : a ∈ regAt ξ p := by
      obtain ⟨_, s, hs, _⟩ := hv
      exact ⟨s, hs⟩
    obtain ⟨s, hs, hunit, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ tie c p hchart a).mp ha
    obtain ⟨ds, Gs, hGs, hsG⟩ := chart_form y c hy hs
    obtain ⟨dt, Gt, hGt, htG⟩ := chart_form y c hy hsa
    have hVs : ValAt ξ z s (MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gs) := by
      have := hval Gs
      rwa [show MvPolynomial.eval₂ (Int.castRingHom Ω) u Gs = s from hsG] at this
    have hVt : ValAt ξ z (s * a) (MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gt) := by
      have := hval Gt
      rwa [show MvPolynomial.eval₂ (Int.castRingHom Ω) u Gt = s * a from htG] at this
    have hr : MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gs ≠ 0 := by
      intro h0
      obtain ⟨q, hq⟩ := hunit.2.2
      have hV' : ValAt ξ z s⁻¹ ((Scheme.stalkClosedPointTo z).hom q) := ⟨hgen, q, hq, rfl⟩
      have h1 := val_mul hVs hV'
      rw [mul_inv_cancel₀ hunit.1, h0, zero_mul] at h1
      have h2 : ValAt ξ z (1 : Ω) (1 : ℂ) := by simpa using val_int (ξ := ξ) (z := z) hgen 1
      exact zero_ne_one (val_unique hinj h1 h2)
    have hre : MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gt =
        MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gs * v := val_unique hinj hVt (val_mul hVs hv)
    have hg : IsMultiHomog (Gt * chartMonomial c ds) (dt + ds) :=
      GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hGt (chartMonomial_homog c ds)
    have hh : IsMultiHomog (Gs * chartMonomial c dt) (dt + ds) := by
      rw [add_comm dt ds]
      exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hGs (chartMonomial_homog c dt)
    have ug : MvPolynomial.eval₂ (Int.castRingHom Ω) u (Gt * chartMonomial c ds) = s * a := by
      rw [MvPolynomial.eval₂_mul, eval_chartMonomial u c ds hu1, _root_.mul_one]
      exact htG
    have uh : MvPolynomial.eval₂ (Int.castRingHom Ω) u (Gs * chartMonomial c dt) = s := by
      rw [MvPolynomial.eval₂_mul, eval_chartMonomial u c dt hu1, _root_.mul_one]
      exact hsG
    have eg : MvPolynomial.eval₂ (Int.castRingHom ℂ) e (Gt * chartMonomial c ds) =
        MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gs * v := by
      rw [MvPolynomial.eval₂_mul, eval_chartMonomial e c ds he1, _root_.mul_one, hre]
    have eh : MvPolynomial.eval₂ (Int.castRingHom ℂ) e (Gs * chartMonomial c dt) =
        MvPolynomial.eval₂ (Int.castRingHom ℂ) e Gs := by
      rw [MvPolynomial.eval₂_mul, eval_chartMonomial e c dt he1, _root_.mul_one]
    refine ⟨dt + ds, Gt * chartMonomial c ds, Gs * chartMonomial c dt, hg, hh, ?_, ?_, ?_, ?_⟩
    · rw [scaleY hh, uh]
      exact mul_ne_zero (hM _) hunit.1
    · rw [scaleY hg, scaleY hh, ug, uh]
      ring
    · rw [scaleW hh, eh]
      exact mul_ne_zero (hMw _) hr
    · rw [scaleW hg, scaleW hh, eg, eh, mul_div_mul_left _ _ (hMw _), mul_div_cancel_left₀ _ hr]
  · rintro ⟨d, g, h, hg, hh, hyh, hgh, hwh, rfl⟩
    have hu : MvPolynomial.eval₂ (Int.castRingHom Ω) u h ≠ 0 := by
      intro h0
      exact hyh (by rw [scaleY hh, h0, mul_zero])
    have he : MvPolynomial.eval₂ (Int.castRingHom ℂ) e h ≠ 0 := by
      intro h0
      exact hwh (by rw [scaleW hh, h0, mul_zero])
    have ha : a = MvPolynomial.eval₂ (Int.castRingHom Ω) u g *
        (MvPolynomial.eval₂ (Int.castRingHom Ω) u h)⁻¹ := by
      rw [scaleY hg, scaleY hh] at hgh
      have h1 : MvPolynomial.eval₂ (Int.castRingHom Ω) u g =
          a * MvPolynomial.eval₂ (Int.castRingHom Ω) u h :=
        mul_left_cancel₀ (hM d) (by rw [hgh]; ring)
      rw [h1, _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.mul_one]
    have hv : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) /
        MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) =
        MvPolynomial.eval₂ (Int.castRingHom ℂ) e g * (MvPolynomial.eval₂ (Int.castRingHom ℂ) e h)⁻¹ := by
      rw [scaleW hg, scaleW hh, mul_div_mul_left _ _ (hMw _), div_eq_mul_inv]
    rw [hv, ha]
    exact val_mul (hval g) (val_inv (hval h) he)

end GlobalTheory.CompanionTheory.Ar
