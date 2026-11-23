import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDiff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameFactorG

open IsDedekindDomain ValuativeRel

variable {D : D7}

theorem exists_diff_not_mem (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ m : 𝓞 D.host.F, m ∈ differentIdeal ℤ (𝓞 D.host.F) ∧ m ∉ (below D P).asIdeal := by
  have h := Formalism.L2.SG.Pf.LatEx.ddG_of D Formalism.L2.SG.Pf.LatEx.splitDiff_holds P hP
  rw [Ideal.map_le_iff_le_comap] at h
  obtain ⟨m, hm, hmP⟩ := Set.not_subset.1 h
  exact ⟨m, hm, hmP⟩

theorem coe_algebraMap_int (m : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (m : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E m).symm

theorem iota_mem_of_inv_pow (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (k : ℕ) (y : D.host.E) (hy : y ∈ (ddS D)⁻¹ ^ k) :
    (D.s.atP (below D P)).ιE y ∈ (D.s.atP (below D P)).O := by
  obtain ⟨m, hm, hmP⟩ := exists_diff_not_mem P hP
  set c : D.host.E := ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) with hc
  have hmE : c ∈ ddS D := by
    unfold ddS
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mem_map_of_mem _ hm, rfl⟩
  have hpow : c ^ k ∈ ddS D ^ k := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
    exact Submodule.pow_mem_pow _ (FractionalIdeal.mem_coe.2 hmE) k
  have h1 : y * c ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hy hpow
    rwa [← mul_pow, inv_mul_cancel₀ GlobalTheory.FrameFactorUnit.ddS_ne_zero, one_pow] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hu := Formalism.L2.SG.Pf.LocalDenominators.iF_unit (D.s.atP (below D P)) hmP
  set t := (D.s.atP (below D P)).ιF (m : D.host.F) with ht
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have htinv : t⁻¹ ∈ 𝒪[(D.s.atP (below D P)).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hu, inv_one]
  have hcE : (D.s.atP (below D P)).ιE c = algebraMap _ (D.s.atP (below D P)).Ep t := by
    rw [hc, coe_algebraMap_int, (D.s.atP (below D P)).compat]
  have e : (D.s.atP (below D P)).ιE y =
      (D.s.atP (below D P)).ιE (o : D.host.E) *
        (algebraMap _ (D.s.atP (below D P)).Ep t⁻¹) ^ k := by
    have h2 := congrArg (D.s.atP (below D P)).ιE ho
    have h3 : (D.s.atP (below D P)).ιE (algebraMap (𝓞 D.host.E) D.host.E o) =
        (D.s.atP (below D P)).ιE (o : D.host.E) := rfl
    rw [h3, map_mul, map_pow, hcE] at h2
    rw [h2, mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_pow, mul_one]
  rw [e]
  exact mul_mem (Formalism.L2.SG.Pf.LocalDenominators.iE_int _ (RingOfIntegers.isIntegral_coe o))
    (pow_mem (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O _ htinv) _)

end GlobalTheory.FrameFactorG

open GlobalTheory.FrameFactorG in

theorem GlobalTheory.FrameFactorG.frFac_unit_at_g : ∀ (D : D7) (Tn T'n : ℕ) (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP Tn T'n F F' → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g : GV D, Adapt g (lf D F0) F → IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, frFac Z.δ (below D P) a ∈ (Z.M (below D P)).L.O ∧ Ring.inverse (frFac Z.δ (below D P) a) ∈ (Z.M (below D P)).L.O := by
  intro D Tn T'n F0 F F' Z FP _ Λ y _ g _ _ P hP a
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z (below D P)
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z (below D P) a
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -((D.R.rS - a.val : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : a.val ≤ D.R.rS)]
  have hpw : (ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) = (ddS D)⁻¹ ^ (D.R.rS - a.val) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hexp, hpw] at hD
  constructor
  · have h : frFac Z.δ (below D P) a ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)) := by
      rw [hD]; exact Submodule.mem_span_singleton_self _
    suffices key : ∀ x ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)), x ∈ (Z.M (below D P)).L.O from
      key _ h
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hO]; exact iota_mem_of_inv_pow P hP _ w hw
    | zero => exact zero_mem _
    | add x w _ _ hx hw => exact add_mem hx hw
    | smul o x _ hx => rw [Subring.smul_def]; exact mul_mem o.2 hx
  · have h1 : (1 : (D.s.atP (below D P)).Ep) ∈ Submodule.span (Z.M (below D P)).L.O {frFac Z.δ (below D P) a} := by
      rw [← hD]
      exact Submodule.subset_span ⟨1, GlobalTheory.FrameFactorUnit.one_mem_inv_pow _, map_one _⟩
    obtain ⟨o1, ho1⟩ := Submodule.mem_span_singleton.1 h1
    have ho1' : (o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a = 1 := by
      simpa [Subring.smul_def, smul_eq_mul] using ho1
    have hu : IsUnit (frFac Z.δ (below D P) a) :=
      ⟨⟨frFac Z.δ (below D P) a, o1, by rw [mul_comm]; exact ho1', ho1'⟩, rfl⟩
    have hinv : Ring.inverse (frFac Z.δ (below D P) a) = o1 := by
      calc Ring.inverse (frFac Z.δ (below D P) a)
          = ((o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a) * Ring.inverse (frFac Z.δ (below D P) a) := by
            rw [ho1', one_mul]
        _ = o1 := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
    rw [hinv]; exact o1.2

end
