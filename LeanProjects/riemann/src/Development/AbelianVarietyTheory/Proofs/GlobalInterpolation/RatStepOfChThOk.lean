import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
