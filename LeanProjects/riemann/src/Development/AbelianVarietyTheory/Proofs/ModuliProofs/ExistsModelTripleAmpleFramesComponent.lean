import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenSetOfTTEqBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFramesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAmpFramesExponents
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
