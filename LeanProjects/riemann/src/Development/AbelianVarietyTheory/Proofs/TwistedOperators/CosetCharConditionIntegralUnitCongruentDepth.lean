import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAlStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

theorem ann_depLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
    ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi e he y hy h u hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have h1 := h (e • u) (hu.2 e he)
  rw [smul_smul, hee, symplO_smul_half _ _ e u y hy] at h1
  exact h1

set_option maxHeartbeats 1000000 in

theorem cosDual : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hyp x hx
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨X, hXdef⟩ : ∃ X : WO (G.pS (.core i)) (G.pT (.core i)), X = e • x₀.map (incA D) := ⟨_, rfl⟩
  have hXh : IsHalf e X := fun a b => by
    simp only [hXdef, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨Z, hZdef⟩ : ∃ Z : WO (G.pS (.core i)) (G.pT (.core i)), Z = X - actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := ⟨_, rfl⟩
  have hZ : IsHalf e Z := fun a b => by
    simp only [hZdef, Matrix.sub_apply, mul_sub, hXh a b, half_actO _ _ e g X hXh a b]
  have key : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1 := by
    intro y hy h1 h2
    have hy' : IsHalf (cA D e) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g⁻¹ y) := half_actO _ _ _ _ _ hy
    have hA := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he y hy h1
    have hB := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he _ hy' (fun v hv => by
      have h3 := h2 v hv
      rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g (e • v) (actO _ _ 1 g⁻¹ y), actO_inv]
      exact h3)
    have H := hyp y hy hA hB
    rw [← hXdef] at H
    rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g X (actO _ _ 1 g⁻¹ y), actO_inv] at H
    have hsum : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by
      rw [hZdef]; abel
    have hs : symplO (G.pS (.core i)) (G.pT (.core i)) X y =
        symplO (G.pS (.core i)) (G.pT (.core i)) Z y +
          symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y := by
      conv_lhs => rw [hsum]
      exact GlobalTheory.LatVac.symplO_add_left _ _ _ _ _
    rw [hs, AddChar.map_add_eq_mul] at H
    generalize hcdef : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c at H
    have hc : c ≠ 0 := by
      intro h0
      have h5 : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) *
          W.ψ (-(symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y)) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      rw [show W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c from hcdef,
        h0, zero_mul] at h5
      exact zero_ne_one h5
    have H' : (W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) - 1) * c = 0 := by
      rw [sub_mul, H, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 H').resolve_right hc)
  obtain ⟨a, ha, b, hb, hZeq⟩ := GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator D hq T L μ0 hL sc G W M hM i hi e he g Z hZ key
  have heq : e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - a) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - -b)) := by
    rw [smul_sub, sub_neg_eq_add, smul_add, actO_add, ← hXdef]
    have h6 : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by rw [hZdef]; abel
    rw [hZeq] at h6
    conv_lhs => rw [h6]
    abel
  obtain ⟨a₁, h1, a₂, h2, heq2⟩ := GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g a ha (-b) (neg_mem hb) heq
  exact GlobalTheory.T.gridCoreNode_unitReading_integral_congruent D hq T L μ0 hL sc G W M hM i hi e he g a₁ h1 a₂ h2 heq2 x hx

end GlobalTheory.CosDual
