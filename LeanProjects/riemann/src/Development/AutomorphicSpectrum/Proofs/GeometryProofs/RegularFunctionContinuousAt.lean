import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

section Frac

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem stalk_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ f g : Γ(X, U), IsUnit (X.presheaf.germ U p hp g) ∧
      s * X.presheaf.germ U p hp g = X.presheaf.germ U p hp f := by
  let : Algebra Γ(X, U) (X.presheaf.stalk p) := (X.presheaf.germ U p hp).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨f, g⟩, h⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl (S := X.presheaf.stalk p) s
  exact ⟨f, g, IsLocalization.map_units (X.presheaf.stalk p) g, h⟩

theorem genMap_germ_indep {U : X.Opens} {p q : Cpt ξ} (hp : p.1 ∈ U) (hq : q.1 ∈ U) (f : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp f) = genMap ξ q (X.presheaf.germ U q.1 hq f) := by
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  have key : ∀ r : Cpt ξ, ∀ hr : r.1 ∈ U, genMap ξ r (X.presheaf.germ U r.1 hr f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg f) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 f)
  rw [key p hp, key q hq]

theorem exists_frac {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) :
    ∃ (P Q : MvPolynomial κ ℤ) (t : X.presheaf.stalk p.1), IsUnit t ∧
      genMap ξ p t = MvPolynomial.aeval (fun j => x j / x c) Q ∧
      a * MvPolynomial.aeval (fun j => x j / x c) Q = MvPolynomial.aeval (fun j => x j / x c) P := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hp.1
  have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨f, g, hg, e⟩ := stalk_frac hU hpU s
  have hA : ∀ f : Γ(X, U), ∃ P : MvPolynomial κ ℤ, MvPolynomial.aeval (fun j => x j / x c) P =
      genMap ξ p (X.presheaf.germ U p.1 hpU f) := by
    intro f
    have hm : genMap ξ p (X.presheaf.germ U p.1 hpU f) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hp.1 _).2 fun q hq => ?_
      have hqU : q.1 ∈ U := (hmem q.1).2 ⟨q.2, hq⟩
      rw [genMap_germ_indep hpU hqU]
      exact ⟨_, rfl⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hm
    obtain ⟨P, hP⟩ := hm
    exact ⟨P, hP⟩
  obtain ⟨P, hP⟩ := hA f
  obtain ⟨Q, hQ⟩ := hA g
  refine ⟨P, Q, X.presheaf.germ U p.1 hpU g, hg, hQ.symm, ?_⟩
  rw [hP, hQ, ← map_mul, e]

end Frac

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}

theorem val_intCast (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_finsetProd (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (a : I → Ω) (r : I → ℂ)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def ratioAt (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) (c' : (k : K) → J k) : ℂ :=
  ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_ratio {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (ratioAt c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_finsetProd hz _ _ _ fun k _ => ?_
  obtain ⟨-, h2⟩ := hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  obtain ⟨r, hr, e⟩ := h2 (c' k)
  rw [e, mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem val_ratioPoly {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ValAt ξ z (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P)
      (MvPolynomial.aeval (ratioAt c w) P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_intCast hz n
  | add p q hp hq => simpa only [map_add] using val_add hp hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (val_ratio hz hw hc i)

theorem continuousAt_ratioAt {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (c' : (k : K) → J k) : ContinuousAt (fun w => ratioAt c w c') w₀ :=
  tendsto_finset_prod _ fun k _ =>
    ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_ratioPoly {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (ratioAt c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_ratioAt hc i)

end Values

theorem val_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  intro X Ω _ ξ K _ J _ y hall hT z₀ w₀ h₀ a hw ha
  choose c hc using hw.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hch := in_chart h₀ hw hc'
  obtain ⟨P, Q, t, ht, hQ, hPQ⟩ := exists_frac hT hch ha
  have hvQ := val_ratioPoly (hall _) hw hc' Q
  have hvt : ValAt ξ z₀ (MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)
      ((Scheme.stalkClosedPointTo z₀).hom t) := ⟨h₀, t, hQ, rfl⟩
  have hne : MvPolynomial.aeval (ratioAt c w₀) Q ≠ 0 := by
    rw [val_unique hT.gen hvQ hvt]
    exact (ht.map (Scheme.stalkClosedPointTo z₀).hom).ne_zero
  have hQa : MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q ≠ (0 : Ω) := by
    rw [← hQ]
    exact (ht.map (genMap ξ _)).ne_zero
  have haeq : a = MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P *
      (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)⁻¹ := by
    rw [← hPQ, mul_inv_cancel_right₀ hQa]
  refine ⟨fun w => MvPolynomial.aeval (ratioAt c w) P / MvPolynomial.aeval (ratioAt c w) Q,
    (continuousAt_ratioPoly hc' P).div (continuousAt_ratioPoly hc' Q) hne,
    {w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (ratioAt c w) Q ≠ 0}, ?_, ?_⟩
  · have e1 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 w₀, ∀ k, w ⟨k, c k⟩ ≠ 0 :=
      eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
    exact e1.and ((continuousAt_ratioPoly hc' Q).eventually_ne hne)
  · rintro z w ⟨h1, h2⟩ hwz
    rw [haeq]
    show ValAt ξ z _ (_ / _)
    rw [div_eq_mul_inv]
    exact val_mul (val_ratioPoly (hall _) hwz h1 P) (val_inv₀ h2 (val_ratioPoly (hall _) hwz h1 Q))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
