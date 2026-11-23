import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTer

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ∀ (hg : LabSGeo C3 ι Y lab), ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) →
    ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ie hie k Y hY _ Orb _ d _ lab ha hg hdisc _ hr _ o Hc
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  have hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) := by
    rwa [NumberField.discr_eq_discr E (Module.Free.chooseBasis ℤ (𝓞 E))]
  obtain ⟨T', φ, t', hi, hf, hG⟩ := GlobalTheory.IntegralChartCover.cover E H Dw lv Xo c hstar T io y C3
  have hp : ¬ IsUnit ((V.l : ℕ) : T.V) :=
    UpFBr.not_isUnit_l (ie.comp (algebraMap T.V T.Fr)) fun t => embIntSt_holds T C V ie hie t
  have hp' : ¬ IsUnit ((V.l : ℕ) : T'.V) := fun h => by
    letI := φ.toAlgebra
    haveI : Algebra.IsIntegral T.V T'.V := ⟨hf.to_isIntegral⟩
    haveI : FaithfulSMul T.V T'.V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
    exact hp (isUnit_of_map_unit (algebraMap T.V T'.V) _ (by rwa [map_natCast]))
  have hL := GlobalTheory.UpperBoundDescent.desc V.l T T' φ hi hf hp _ _ _ _
    (UpFBr.upFLaw_of_geoJ (hup V.l) Y.l_odd T'.V hp' t'.G _ _ _ hG hd)
  exact UpFBr.chStSelf_of_upChar Y (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) Hc
    (UpFBr.upCharS_chartL hL hie hd hY ha hg hr o Hc)
