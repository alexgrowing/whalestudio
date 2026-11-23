import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
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

namespace GlobalTheory.SiuChain

theorem hdim_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)]
    (hX : IsProjOver (strHom k X)) (G : X.Modules) [IsFiniteQC G] (B M : LB X) (hB : B.IsLB)
    (hM : M.IsLB) (t : B.Sec) (ht : Mono (cutHom G hB t)) (j : ℕ) :
    ∀ (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist G M') 0 ≤ hdim k (twist G M) 0 := by
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G hM hM' h
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h2 := ih _ (isLB_tens hM' hB) (by rw [h1, h, succ_nsmul']; abel)
    exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX G B _ M' hB _ hM' t ht h1).2.2).trans h2

theorem hdim_le_add_mul_hdim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  intro k _ _ X _ hX F _ B M hB hM s t hs ht j
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' h
    rw [hdim_congr k 0 e]
    omega
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h0 : cls M hM = cls (tens M' B) (isLB_tens hM' hB) + j • cls B hB := by
      rw [h1, h, succ_nsmul']; abel
    have h2 := ih _ (isLB_tens hM' hB) h0
    have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B _ M' hB _ hM' s hs h1).1 0
    have h4 := hdim_le_of_cls_eq_add_nsmul k X hX (cut F hB s) B M hB hM t ht j _
      (isLB_tens hM' hB) h0
    rw [Nat.succ_mul]
    omega

end GlobalTheory.SiuChain
