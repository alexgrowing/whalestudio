import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTower
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentChartBaseChangeFormalGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumFormalGroupCharactersStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolarisedAbelianSchemeBaseChangeRingActionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem exists_htd_characters_base : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (T : Type) [CommRing T] [IsNoetherianRing T] (io : T →+* O) (P : Out.PolAV (Spec (CommRingCat.of T))) (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw T g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS T 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (fun j => MvPowerSeries.map io (α a j)) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh (F.mapF io) u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ T _ _ io P g hg OE _ _ o F X hX α hα
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · subst h0
    obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C v O hv
    have hs := hodgeTateSetting_ainfTower_of_isPrimitiveRoot p O hv ε hε OE
    obtain ⟨H⟩ := htd_dim_zero p C v O hv OE (show O from (Ainf.ainfTowerL p O hv ε hε).c)
    exact ⟨_, hs, H, 1, Subsingleton.elim _ _, Subsingleton.elim _ _, isUnit_one,
      fun _ => Subsingleton.elim _ _, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨P', φ, hφ, hL, hg', hact⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_baseChange_ringAction T O io P
    obtain ⟨o', ho'⟩ := hact OE o
    obtain ⟨X', hX', hR⟩ := GlobalTheory.T.nilpotentChart_baseChange_formalGroup T O io P.A P'.A φ hφ g F.F X hX
    obtain ⟨F', hF'⟩ := (GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff T O io).1 g F
    have hX'' : NilChart P'.A F'.F X' := by rw [hF']; exact hX'
    have h := GlobalTheory.T.exists_hodgeTateDatum_formalGroupCharacters p C v O hv T P io P' φ hφ hL hg' (by omega) g (hg'.trans hg) OE o' F' X'
      hX'' (fun a j => MvPowerSeries.map io (α a j))
      (fun a => hR (o.act a) (o'.act a) (α a) (ho' a) (hα a))
    rw [hF'] at h
    exact h

end GlobalTheory.ChF
