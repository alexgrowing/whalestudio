import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMemberStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    GlobalTheory.T.fock_minimal_KType_second_member p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
