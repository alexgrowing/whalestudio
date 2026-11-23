import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.SplitGen

theorem exists_places {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hc : p % (H.QS * H.q * H.d) = 1)
    (ι : Type) [Fintype ι] (hι : Fintype.card ι = R.f) :
    ∃ φ : ι → HeightOneSpectrum (𝓞 H.F), Function.Injective φ ∧ ∀ v, (p : 𝓞 H.F) ∈ (φ v).asIdeal := by
  have h1 := Formalism.MainNotions.Gaps.LevGap.split_F H p hp (GlobalTheory.HostSplit.split_of_one_mod R H p hp hc).1
  have hpos : 0 < Module.finrank ℚ H.F := Module.finrank_pos
  have hfin : {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [h1]; exact hpos)
  haveI := hfin.to_subtype
  have h2 : Nat.card ι = Nat.card {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal} := by
    rw [Nat.card_coe_set_eq, h1, Formalism.MainNotions.Gaps.LevGap.finrank_F, Nat.card_eq_fintype_card, hι]
  obtain ⟨e⟩ := Finite.card_eq.1 h2
  exact ⟨fun v => (e v).1, Subtype.val_injective.comp e.injective, fun v => (e v).2⟩

theorem nonempty_errX : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧
    (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  intro X h
  choose pG hG1 hG2 using h
  choose pT hT1 hT2 hT3 using X.toD7.T_norm
  have hv : ∀ u, ∃ φ : (X.toD7.mem u).A.vT → HeightOneSpectrum (𝓞 X.toD7.host.F), Function.Injective φ ∧
      ∀ v, ((X.toD7.mem u).A.T : 𝓞 X.toD7.host.F) ∈ (φ v).asIdeal := by
    intro u
    letI := (X.toD7.mem u).A.vTFin
    refine exists_places X.toD7.host (X.toD7.mem u).A.T_prime ?_ _ (X.toD7.mem u).A.card_vT
    have h1 : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [h1]
    exact X.B.T_cond u
  choose φ hφ1 hφ2 using hv
  exact ⟨⟨pG, hG1, hG2, pT, hT1, hT2, hT3, φ, hφ1, hφ2⟩⟩

end GlobalTheory.SplitGen
