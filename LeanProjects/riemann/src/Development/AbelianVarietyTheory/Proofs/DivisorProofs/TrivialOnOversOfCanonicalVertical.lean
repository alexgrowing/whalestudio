import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionLogNormPrimeStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.StepG

theorem unitAt_of_cong {X : Scheme.{0}} [IsIntegral X] {x : X} {e f : X.functionField} (he0 : e ≠ 0) (he : ZeroAt x e)
    (h : RegAt x ((f - 1) / e)) : UnitAt x f := by
  obtain ⟨a, ha, ha'⟩ := he.mul h
  refine ⟨1 + a, ?_, ?_⟩
  · refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right fun hu => ha ?_
    rwa [sub_add_cancel_left, IsUnit.neg_iff] at hu
  · rw [map_add, map_one, ha']
    field_simp
    ring

theorem bil_eq_zero_of_trivOn : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num → ∀ (G : Fin n → HermLB q) (p : ℕ), p.Prime → ∀ (M B : HermLB q) (E : CartierDiv X) (e b : X → X.functionFieldˣ), Can M E → Vert p E → (∀ x, Ov p x → E.IsEqn x (e x) ∧ RegAt x (e x : X.functionField)) → Rep p B b → TrivOn p (fun x => (e x : X.functionField)) (fun x => (b x : X.functionField)) → bil num (fun j => cl (G j)) (cl M) (cl B) = 0 := by
  intro hP k _ X _ q n hX num hnum _ G p hp M B E e b hM hV he hB hT
  haveI : IsLocallyNoetherian X := hX.isLocallyNoetherian
  obtain ⟨r, hr, rfl, hnorm⟩ := hM
  obtain ⟨ρ, hρ, hb⟩ := hB
  obtain ⟨t, ht⟩ := hT
  have hq (i : M.B.ι) (x : X) (hx : x ∈ M.B.U i) : (M.div hr).IsEqn x (r i) := (presents_divOfRatSec _ hr).isEqn i x hx
  have hq' (j : B.B.ι) (x : X) (hx : x ∈ B.B.U j) : (B.div hρ).IsEqn x (ρ j) := (presents_divOfRatSec _ hρ).isEqn j x hx
  have hoff (i : M.B.ι) (x : X) (hx : x ∈ M.B.U i) (h : ¬ Ov p x) : UnitAt x (r i : X.functionField) := by
    simpa using (hV x h).iff_unitAt.1 (hq i x hx)
  have hon (i : M.B.ι) (x : X) (hx : x ∈ M.B.U i) (h : Ov p x) : UnitAt x ((r i : X.functionField) / e x) :=
    (he x h).1.iff_unitAt.1 (hq i x hx)
  choose U hU hUo hUa using fun a : {x : X // Ov p x} => eventually_nhds_iff.1 (ht a.1 a.2).2
  rw [bil_apply]
  refine GlobalTheory.T.rational_section_log_norm_prime hP k X q n hX num hnum M r hr (fun σ y _ => (hnorm σ y).2) p hp (fun i x hx => ⟨?_, fun hu => ?_⟩)
    B ρ hρ {x : X // Ov p x} (fun a => ⟨U a, hUo a⟩) (fun a => t a.1) (fun i x hx hn => ?_) G
  · by_cases h : Ov p x
    · have := (hon i x hx h).regAt.mul (he x h).2
      rwa [div_mul_cancel₀ _ (e x).ne_zero] at this
    · exact (hoff i x hx h).regAt
  · exact hoff i x hx (not_not.2 hu)
  · have h : Ov p x := by_contra fun h => hn (hoff i x hx h)
    have hne : ¬ UnitAt x (e x : X.functionField) := fun hu => hn (by
      have := (hon i x hx h).mul hu
      rwa [div_mul_cancel₀ _ (e x).ne_zero] at this)
    have hz : ZeroAt x (e x : X.functionField) := zeroAt_iff.2 ⟨(he x h).2, hne⟩
    have hunit (a : {x : X // Ov p x}) (ha : x ∈ U a) : UnitAt x ((t a.1 : X.functionField) / t x) :=
      unitAt_of_cong (e x).ne_zero hz (hU a x ha h hne)
    refine ⟨⟨⟨x, h⟩, hUa _⟩, fun a j ha hj => ?_, fun a c ha hc => ?_⟩
    · have := ((hunit a ha).mul ((ht x h).1 hne)).mul ((hb x h).iff_unitAt.1 (hq' j x hj))
      convert this using 1
      have := (t x).ne_zero
      have := (b x).ne_zero
      field_simp
    · have hneg : RegAt x (-1 : X.functionField) := ⟨-1, by simp⟩
      have := (((hU a x ha h hne).add (hneg.mul (hU c x hc h hne))).mul (hunit c hc).inv.regAt).mul
        (hon i x hx h).inv.regAt
      convert this using 1
      have := (t x).ne_zero
      have := (t c.1).ne_zero
      have := (e x).ne_zero
      have := (r i).ne_zero
      rw [Units.val_div_eq_div_val]
      field_simp
      ring

end GlobalTheory.LatChain.StepG
