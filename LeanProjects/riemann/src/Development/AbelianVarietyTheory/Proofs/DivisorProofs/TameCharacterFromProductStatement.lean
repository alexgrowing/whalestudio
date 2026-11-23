import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_from_product : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), (∀ x : (AE D)ˣ, cA D (x : AE D) = (x : AE D) → μ x = 1) → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) → LatticeBasisLifts.IsInvTame σ Pg μ χ := by
  first | exact @GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half | exact GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half | (intros; apply GlobalTheory.GeoActCompare.TameConj.isInvTame_of_half <;> assumption)
