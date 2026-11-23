import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw

abbrev conjR (D : D7) : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv

def conjFI (D : D7) : FI D ≃+* FI D :=
  FractionalIdeal.ringEquivOfRingEquiv D.host.E D.host.E (NumberField.RingOfIntegers.mapRingEquiv (conjR D))

theorem conj_conj_host (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← bridge_star_holds D.R D.host, ← bridge_star_holds D.R D.host, star_star]

theorem fracEquiv_conj (D : D7) (x : D.host.E) :
    IsFractionRing.ringEquivOfRingEquiv (K := D.host.E) (L := D.host.E)
      (NumberField.RingOfIntegers.mapRingEquiv (conjR D)) x = D.host.conj x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_div₀]
  rfl

theorem mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : x ∈ conjFI D 𝔞 ↔ D.host.conj x ∈ 𝔞 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg D.host.conj (fracEquiv_conj D y)).trans (conj_conj_host D y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨D.host.conj x, h, (fracEquiv_conj D _).trans (conj_conj_host D x)⟩

theorem conj_mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : D.host.conj x ∈ conjFI D 𝔞 ↔ x ∈ 𝔞 := by
  rw [mem_conjFI, conj_conj_host]

theorem conjFI_AA (D : D7) : conjFI D D.host.AA = D.host.AAbar := by
  ext x
  rw [mem_conjFI]
  refine ⟨fun h => ?_, fun h => Formalism.L2.Pj.conj_mem_AA D h⟩
  simpa only [conj_conj_host] using Formalism.L2.Pj.conj_mem_AAbar D h

theorem conjFI_AA_zpow (D : D7) (n : ℤ) : conjFI D (D.host.AA ^ n) = D.host.AAbar ^ n := by
  rw [map_zpow₀, conjFI_AA]

theorem cA_tmul (D : D7) (α : AF D.host.F) (a : D.host.E) :
    cA D (α ⊗ₜ[D.host.F] a) = α ⊗ₜ[D.host.F] D.host.conj a := by
  change α ⊗ₜ[D.host.F] star a = _
  rw [bridge_star_holds D.R D.host]

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => rw [cA_tmul, cA_tmul, conj_conj_host]

theorem cA_mem_idV {D : D7} {𝔞 : FI D} {v : Pl D} {s : AE D} (hs : s ∈ idV 𝔞 v) :
    cA D s ∈ idV (conjFI D 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (conjFI D 𝔞) v).comap (cA D).toAddMonoidHom := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hv, a, ha, rfl⟩
    show cA D _ ∈ idV (conjFI D 𝔞) v
    rw [cA_tmul]
    exact AddSubgroup.subset_closure ⟨α, hα, hv, D.host.conj a, conj_mem_conjFI.2 ha, rfl⟩
  exact hle hs

theorem idV_cA_iff (D : D7) (v : Pl D) (𝔞 : FI D) (s : AE D) :
    s ∈ idV 𝔞 v ↔ cA D s ∈ idV (conjFI D 𝔞) v := by
  refine ⟨cA_mem_idV, fun h => ?_⟩
  have h2 := cA_mem_idV h
  rwa [cA_cA, show conjFI D (conjFI D 𝔞) = 𝔞 from by ext x; rw [mem_conjFI, conj_mem_conjFI]] at h2

theorem idV_AA_zpow_conj : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D),
    s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  intro D v n s
  rw [idV_cA_iff D v, conjFI_AA_zpow]

end GlobalTheory.SeeSaw
