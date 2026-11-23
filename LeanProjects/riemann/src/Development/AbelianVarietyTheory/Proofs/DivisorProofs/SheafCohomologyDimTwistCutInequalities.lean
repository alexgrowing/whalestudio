import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

private theorem finiteCohTwists_of_isProjOver' (k : Type) [Field k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) (F : X.Modules) [IsFiniteQC F] : FiniteCohTwists k F := by
  have hp' := hp
  unfold IsProjOver at hp'
  obtain ⟨N, i, hi, hcomp⟩ := hp'
  have hA : IsAmpleLB (ProjSpace.O1 k N) := isAmple_projective_O_one k N
  have hA' : IsAmpleLB ((ProjSpace.O1 k N).pull i) := IsAmpleLB.pull_of_isClosedImmersion hA i
  have hpr : IsProper (strHom k X) := by
    rw [← hcomp]
    have := isProper_str k N
    infer_instance
  exact IsAmpleLB.finiteCohTwists (f := strHom k X) (fun r => algebraMap_eq_strHom k X r) F hA'

theorem hdim_twist_cut_inequalities :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  intro k _ _ X _ hp F _ B M M' hB hM hM' s hmono hcls
  have hS : (cutComplex F hB s).ShortExact := shortExact_cutComplex F hB s
  have := Twist.preservesFiniteLimits_twistFunctor hM
  have := Twist.preservesFiniteColimits_twistFunctor hM
  have hT := hS.map_of_exact (twistFunctor M)
  have hF : FiniteCohTwists k F := finiteCohTwists_of_isProjOver' k X hp F
  have hC : FiniteCohTwists k (cut F hB s) := FiniteCohTwists.cut (hL := hB) (s := s) (h := hF)
  have hBi : (lbZPow B (-1)).IsLB := isLB_lbZPow hB (-1)
  have hcls' : cls M' hM' = cls (lbZPow B (-1)) hBi + cls M hM := by
    rw [cls_lbZPow hB (-1) hBi, hcls]
    abel
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hM hM' hcls'
  have f1 : ∀ n, Module.Finite k (coh (twist (twist F (lbZPow B (-1))) M) n) :=
    fun n => ((hF.twist hBi) M hM).finite n
  have f2 : ∀ n, Module.Finite k (coh (twist F M) n) := fun n => (hF M hM).finite n
  have f3 : ∀ n, Module.Finite k (coh (twist (cut F hB s) M) n) := fun n => (hC M hM).finite n
  have he : ∀ n, hdim k (twist (twist F (lbZPow B (-1))) M) n = hdim k (twist F M') n :=
    fun n => hdim_congr (k := k) (n := n) e
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h : hdim k (twist F M) i ≤ hdim k (twist (twist F (lbZPow B (-1))) M) i +
        hdim k (twist (cut F hB s) M) i := hdim₂_le k hT i (f1 i) (f3 i)
    rw [he i] at h
    exact h
  · have h : hdim k (twist (twist F (lbZPow B (-1))) M) (i + 1) ≤ hdim k (twist (cut F hB s) M) i +
        hdim k (twist F M) (i + 1) := hdim₁_le k hT i (f3 i) (f2 (i + 1))
    rw [he (i + 1)] at h
    exact h
  · have h0 := hdim₁_zero_le k hT (f2 0)
    have h : hdim k (twist (twist F (lbZPow B (-1))) M) 0 ≤ hdim k (twist F M) 0 := h0
    rw [he 0] at h
    exact h

end GlobalTheory
