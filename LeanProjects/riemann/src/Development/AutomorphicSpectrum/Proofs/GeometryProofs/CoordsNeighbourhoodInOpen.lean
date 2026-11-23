import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

namespace OpenNear

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {T : Type} (s : Finset T) {a : T → Ω} {r : T → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem val_aeval {κ : Type} {a : κ → Ω} {r : κ → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i, ValAt ξ z (a i) (r i)) (P : MvPolynomial κ ℤ) :
    ValAt ξ z (MvPolynomial.aeval a P) (MvPolynomial.aeval r P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_int hz n
  | add p q hp hq => simpa only [map_add] using val_add hp hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (h i)

theorem genMap_germ {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) (p : Cpt ξ) (hp : p.1 ∈ W) :
    genMap ξ p (X.presheaf.germ W p.1 hp Q) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
  have h2 : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ W p.1 hp Q) =
      X.presheaf.germ W (genPt ξ) hW Q := by
    rw [← h]; rfl
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem isUnit_germ_iff (hξ : IsCptGen ξ) {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) {z : Sp ℂ ⟶ X}
    (hz : centre z ∈ W) {v : ℂ}
    (hv : ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q)) v) :
    IsUnit (X.presheaf.germ W (centre z) hz Q) ↔ v ≠ 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  have hs' : s = X.presheaf.germ W (centre z) hz Q :=
    hξ.inj ⟨centre z, h⟩ (hs.trans (genMap_germ hW Q ⟨centre z, h⟩ hz).symm)
  subst hs'
  have := Scheme.isLocalHom_stalkClosedPointTo' z
  constructor
  · exact fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero
  · exact fun hv => (isUnit_map_iff (Scheme.stalkClosedPointTo z).hom _).1 (isUnit_iff_ne_zero.2 hv)

def segreRatio {K : Type} [Fintype K] {J : K → Type} (c : (k : K) → J k) (w : (Σ k, J k) → ℂ)
    (c' : (k : K) → J k) : ℂ := ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_segreRatio {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X}
    {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_prod _ hz fun k _ => ?_
  obtain ⟨r, hr, hr'⟩ := (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).2 (c' k)
  rw [hr', mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem continuousAt_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ContinuousAt (fun w => segreRatio c w c') w₀ := by
  refine tendsto_finsetProd _ fun k _ => ?_
  exact ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_aeval_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (segreRatio c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_segreRatio hc i)

end OpenNear

open OpenNear in

theorem open_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (U : X.Opens), CoordsAt ξ y z₀ w₀ → centre z₀ ∈ U →
      ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → centre z ∈ U := by
  intro X Ω _ ξ K _ J _ y hgen ht z₀ w₀ U hw₀ hU
  choose c hc using hw₀.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hin₀ := in_chart (hgen (centre z₀)) hw₀ hc'
  obtain ⟨W, hWa, hW⟩ := ht.affine c hin₀.1
  have hz₀W : centre z₀ ∈ W := (hW _).2 ⟨hgen _, hin₀⟩
  obtain ⟨Q, hQU, hQ₀⟩ := hWa.exists_basicOpen_le (V := U) ⟨centre z₀, hU⟩ hz₀W
  have hgW : genPt ξ ∈ W := (hgen _).mem_open W.isOpen hz₀W
  have hreg : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q) ∈
      Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    rw [ht.ring c hin₀.1]
    intro p hp
    exact ⟨X.presheaf.germ W p.1 ((hW _).2 ⟨p.2, hp⟩) Q, genMap_germ hgW Q p _⟩
  rw [Algebra.adjoin_range_eq_range_aeval] at hreg
  obtain ⟨P, hP⟩ := hreg
  have hval : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → (∀ k, w ⟨k, c k⟩ ≠ 0) →
      ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q))
        (MvPolynomial.aeval (segreRatio c w) P) := by
    intro z w hw hcw
    rw [← hP]
    exact val_aeval (hgen _) (val_segreRatio (hgen _) hw hcw) P
  have hne₀ : MvPolynomial.aeval (segreRatio c w₀) P ≠ 0 :=
    (isUnit_germ_iff ht.gen hgW Q hz₀W (hval z₀ w₀ hw₀ hc')).1
      ((Scheme.mem_basicOpen X Q _ hz₀W).1 hQ₀)
  refine ⟨{w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (segreRatio c w) P ≠ 0}, ?_, ?_⟩
  · refine Filter.Eventually.and ?_ ((continuousAt_aeval_segreRatio hc' P).eventually_ne hne₀)
    exact Filter.eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
  · rintro z w ⟨hcw, hne⟩ hw
    have hzW : centre z ∈ W := (hW _).2 ⟨hgen _, in_chart (hgen _) hw hcw⟩
    exact hQU ((Scheme.mem_basicOpen X Q _ hzW).2
      ((isUnit_germ_iff ht.gen hgW Q hzW (hval z w hw hcw)).2 hne))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
