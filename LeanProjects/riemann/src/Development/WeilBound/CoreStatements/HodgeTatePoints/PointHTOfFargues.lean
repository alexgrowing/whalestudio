import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedDivisibleGroupExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionTwoStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.ValuationRingOfIntegers
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFourStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Ge.Fargues
open GlobalTheory.CompanionTheory

theorem lie_free_finite (S : Scheme.{0}) (G : Over S) [GrpObj G] (hG : Smooth G.hom) (R : Type) [CommRing R]
    [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : Module.Free R E ∧ Module.Finite R E := by
  obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring S G hG R x E M
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

def ordTower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L]
    (M : LieModel G y L) : OrdTower p O La L :=
  haveI : IsLocalRing O := (GlobalTheory.T.complete_integers_properties p C v O hv hp hO).2.1.toIsLocalRing
  have h3 := GlobalTheory.T.semiabelian_adic_torsion_one p C v O hv hp hO S G hG y La X
  have h4 := GlobalTheory.T.semiabelian_adic_torsion_two p C v O hv hp hO S G hG y La X
  have h5 := TwDer.der_main p C v O hv hp hO S G hG y La X L M
  have h6 := (GlobalTheory.T.semiabelian_adic_torsion_four p C v O hv hp hO S G hG y La X L M).1
  { A := fun n => (X.Γ n).btOrder ⊤
    hopf := by
      obtain ⟨U, H, -, -, -, h, -⟩ := h3
      exact h
    res_iff := fun n => (h4 n).1
    ker_res := fun n => (h4 n).2
    der := X.IsDer M
    der_ex := fun n => (h5 n).1
    der_unique := fun n => (h5 n).2.1
    der_onto := fun n => (h5 n).2.2.1
    der_add := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).1
    der_mul := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).2
    der_const := fun n => (h5 n).2.2.2.2.1
    der_zero := fun n => (h5 n).2.2.2.2.2
    der_res := h6 }

theorem pointHT (hF : FarguesHodgeTate) : PointHT := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c hc S _ G _ _ hG y La _ _ EF N u hu X L _ _ M act ρL hmon hact hind
    hrank ζ hζ hζp hpair κ hκ
  haveI : Module.Free ℤ La := hu.free
  haveI : Module.Finite ℤ La := hu.finite
  haveI : IsLocalRing O := (GlobalTheory.T.complete_integers_properties p C v O hv hp hO).2.1.toIsLocalRing
  obtain ⟨hLf, hLfin⟩ := lie_free_finite S G hG.smooth O y L M
  let T := ordTower p C v O hv hp hO S G hG y La X L M
  have hacts : ∀ a : 𝓞 E, T.Acts (DistribMulAction.toAddMonoidHom La a) (ρL a) := by
    intro a n f g hfg
    haveI := hmon a
    exact (GlobalTheory.T.semiabelian_adic_torsion_four p C v O hv hp hO S G hG y La X L M).2 (act a) _ (ρL a) (hind a) (hact a) n f g hfg
  have hpe : T.PairingExtends EF ζ := fun n =>
    GlobalTheory.T.exists_prodSpan_torsion_pairing_eq_zeta_pow p C v O hv hp hO S G hG y La X EF ζ (fun n => (hζ n).pow_eq_one) hpair n
  exact GlobalTheory.T.polarised_divisible_group_exists hF p C v O hv hp hO E c hc La EF N u hu L T ρL ζ κ hacts hrank hζ hζp hpe hκ

end PositivityTheory.HtPt.Ge.Fargues

theorem PositivityTheory.HtPt.Ge.pointHT_of_fargues : FarguesHodgeTate → PointHT := PositivityTheory.HtPt.Ge.Fargues.pointHT
