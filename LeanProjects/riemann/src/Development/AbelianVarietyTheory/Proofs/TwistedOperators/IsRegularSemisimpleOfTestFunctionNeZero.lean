import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer

open GlobalTheory.Orb

namespace GlobalTheory.RegSupp

theorem mem_iwahori_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    {g : GL (Fin n) (Fv F v)} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n) → g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.iwahori (Fv F v) n := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  intro hg
  haveI hc : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he : (ValuativeRel.valuation (Fv F v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hle : (ValuativeRel.valuation (Fv F v)).integer ≤ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.Int (Fv F v) :=
    fun x hx => he.le_one_iff_le_one.1 hx
  refine Subgroup.mem_map.2 ⟨Matrix.GeneralLinearGroup.map (Subring.inclusion hle) h, ?_, ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff]
    intro i j hij
    have hb := (Subgroup.mem_comap.1 hh) (i := i) (j := j) (by
      rw [show i = (GlobalTheory.SmGL.points (Fin n)) ⟨i, ()⟩ from rfl, show j = (GlobalTheory.SmGL.points (Fin n)) ⟨j, ()⟩ from rfl,
        GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
      exact hij)
    change IsLocalRing.residue _ (h.1 i j) = 0 at hb
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers _).isUnit_iff_valuation_eq_one] at hb
    have h1 : ValuativeRel.valuation (Fv F v) ((h.1 i j : _) : Fv F v) < 1 :=
      lt_of_le_of_ne (h.1 i j).2 hb
    exact he.lt_one_iff_lt_one.1 h1
  · ext i j
    rfl

end GlobalTheory.RegSupp

namespace GlobalTheory.RegSupp

theorem isRegSS_of_tensor_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  intro hI D V T U μf ff hT fa δ x h
  obtain ⟨-, -, ⟨t, ht, hfu⟩, -, hcof⟩ := hT
  have hfin : (Function.mulSupport fun v =>
      ff v (proj D.sp.cm.sig V.gram v (x⁻¹ * rat V δ * x))).Finite :=
    Filter.eventually_cofinite.1 ((hcof.and (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V)
      (x⁻¹ * rat V δ * x))).mono fun v hv => by
        show ff v _ = 1
        rw [hv.1, unitLoc, Set.indicator_of_mem hv.2, Pi.one_apply])
  have hne : ff U.u (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) ≠ 0 := by
    intro h0
    apply h
    show (∏ w, fa w (projArch D.sp.cm.sig V.gram w _)) * ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v _) = 0
    rw [finprod_eq_zero _ U.u h0 hfin, mul_zero]
  rw [hfu] at hne
  have hmem := Set.mem_of_indicator_ne_zero hne
  obtain ⟨A, hA, rfl⟩ := ht
  obtain ⟨a, ha, b, hb, e⟩ := U.frame.mem_iwahoriCoset.1 hmem
  have key := (hI _ (U.ϖ : Fv _ U.u) U.unif _ A hA
    (U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x))).1
    ⟨a, mem_iwahori_valued U.u ha, b, mem_iwahori_valued U.u hb, by
      rw [e, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT]
      congr 2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.diagPow
      congr 1
      funext i
      exact Units.val_zpow_eq_zpow_val _ _⟩).2
  have e1 : U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) =
      (U.frame.equiv (proj D.sp.cm.sig V.gram U.u x))⁻¹ * U.frame.equiv (proj D.sp.cm.sig V.gram U.u (rat V δ)) *
        U.frame.equiv (proj D.sp.cm.sig V.gram U.u x) := by
    simp only [map_mul, map_inv]
  rw [e1, charpoly_conj_GL] at key
  change (splitEquivIn _ _ U.frame.emb U.frame.basis _).1.charpoly.Separable at key
  rw [splitEquivIn_apply, charpoly_conj_GL, splitHom_val, rat, proj_ratEmb,
    show (matHom _ D.sp.cm.sig V.gram (ratLoc D.sp.cm.sig V.gram U.u δ)).1 = δ.1.1.map (inclR _) from rfl,
    Matrix.map_map, show (splitProj U.frame.emb) ∘ (inclR (Fv _ U.u)) = (U.frame.emb : _ →+* Fv _ U.u) from
      funext (splitProj_inclR _), Matrix.charpoly_map] at key
  exact (Polynomial.separable_map _).1 key

end GlobalTheory.RegSupp
