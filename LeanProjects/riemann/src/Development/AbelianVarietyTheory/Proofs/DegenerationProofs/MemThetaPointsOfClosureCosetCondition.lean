import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPointStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ClosurePoint

theorem exists_full_of_closure_of_cosets :
    HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y K _ _ _ n j ρ z v hn hodd hj hc hvan hcos
  have hm : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  have hm3 : 3 ≤ n ^ j := hn3.trans (Nat.le_self_pow (by omega) n)
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hcos 0
    exact hx (by rw [h]; rfl)
  obtain ⟨C, _, _, _, _, _, S, κ, _, _, res, i, o, M, v', r', z', hnorm, hS, hres, hth, hv', hr', hρ,
    hz', hz⟩ := GlobalTheory.T.exists_trait_specialisation_of_mem_closure_thetaPoints h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K (n ^ j) ρ z v hm hc hv0 hvan
  have hunit : ∀ x, v x ≠ 0 → ‖(v' x : C)‖ = 1 := by
    intro x hx
    have hle : ‖(v' x : C)‖ ≤ 1 := (hS _).1 (v' x).2
    by_contra hne
    have h0 := hres (v' x) (lt_of_le_of_ne hle hne)
    rw [hv' x] at h0
    exact hx (i.injective (by rw [h0, map_zero]))
  have hprop : IsProper M.t.G.hom :=
    GlobalTheory.T.isProper_of_theta_unit_in_every_coset h1 h2 h3 h4 h5 h6 h7 E H D C o M n j hn hodd (hnorm n hn.pos) hj
      (fun x => v' x) hth (fun x => (hS _).1 (v' x).2)
      (fun x => (hcos x).imp fun h hh => hunit _ hh)
  obtain ⟨o', hρ', hζ', hth'⟩ := GlobalTheory.T.exists_specialisation_with_thetaPoint h1 h2 h3 h4 h5 h6 h7 E H D C hnorm o M hprop S hS κ res
    hres (n ^ j) v' hm hm3 hth (by
      obtain ⟨x, hx⟩ := hcos 0
      exact ⟨_, by rw [hv']; exact (map_ne_zero i).2 hx⟩)
  refine GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K κ i (n ^ j) ρ z v o' hm hc
    ((hρ' r' hr').trans hρ) ((hζ' _ (by positivity) z' hz').trans hz) ?_
  have : (fun x => res (v' x)) = fun x => i (v x) := funext hv'
  rwa [this] at hth'

end GlobalTheory.Ex.ClosurePoint
