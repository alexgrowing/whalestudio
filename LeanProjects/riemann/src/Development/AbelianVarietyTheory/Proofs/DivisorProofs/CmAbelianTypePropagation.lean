import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivisibleGroupTorsionTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleHeightEqSignatureDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateMapEquivariantIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TatePointSurjectiveOnFiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationWeilPairingEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapsEqOfEqualPairingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingFormulaAllPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationUniqueOfPairingInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationUniqueAmongDualMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperPolarizationFromPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaTrivialOfPUnitStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

theorem exists_isPropG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ)
    [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsOfType Dw t →
      ∃ GG act pol θ ε τ, IsPropG (p := p) Dw t GG act pol θ ε τ := by
  intro E _ _ _ H Dw p _ k _ _ t ht
  haveI : CharZero k := ht.charZero
  obtain ⟨hP, -, -, ⟨I⟩⟩ := ht
  obtain ⟨GG, ⟨tw⟩⟩ := GlobalTheory.T.exists_p_divisible_group_torsion_tower t p hP
  obtain ⟨pol, hpol⟩ := GlobalTheory.T.exists_polarization_weil_pairing_eq tw I
  have hext := GlobalTheory.T.dual_maps_eq_of_equal_pairings tw I
  have hp : IsUnit (p : k) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
  obtain ⟨hsub, hom⟩ := GlobalTheory.T.omega_trivial_of_p_unit (TorsionMap.ofTower tw) hp
  refine ⟨GG, tw.act t.act, pol, TorsionMap.ofTower tw, eps p I, tau tw I, ?_⟩
  exact
    { height := GlobalTheory.T.p_divisible_height_eq_signature_degree tw I
      equivariant := fun a => by
        haveI := t.act.hom a
        rw [TorsionTower.act_apply]
        exact TorsionMap.ofTower_intertwines tw _
      interior := TorsionMap.ofTower_isIsoOver tw _
      nearZero := TorsionMap.ofTower_isOpenNearZero tw
      omega := ⟨0, hom, fun _ _ _ _ => Subsingleton.elim _ _⟩
      adj := GlobalTheory.T.polarization_unique_of_pairing_injective tw I pol.hom hext hpol
      skew := GlobalTheory.T.dualHom_bidual_comp_eq_neg_of_weil_pairing tw I pol.hom hext hpol
      prim := fun n => by rw [muRoot_eps]; exact zeta_prim p I n
      lin := GlobalTheory.T.tate_map_equivariant_integers tw I
      pair := GlobalTheory.T.weil_pairing_formula_all_points tw I pol.hom hpol
      onto := fun n K _ _ _ φ => GlobalTheory.T.tate_point_surjective_on_finite_level tw I n K φ
      weil := fun n K _ _ _ _ _ x x' y u h1 h2 => GlobalTheory.T.proper_polarization_from_pairing tw I hP pol.hom hpol n K x x' y u h1 h2 }

end GlobalTheory.GroupBplus.Closed
