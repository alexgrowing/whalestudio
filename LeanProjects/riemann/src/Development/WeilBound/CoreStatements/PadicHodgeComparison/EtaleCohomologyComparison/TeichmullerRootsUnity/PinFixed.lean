import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.TeichDvd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.IsMuMmG
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PhiAIter
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuNu
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.MapFrobW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.NormLLtOne

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem PinP.pin_of (r : Res l K) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) (F : Pb.Fac r N) (M : Model l K) (j : ℕ)
    (hβ : ∀ (y : Pb.LW r M j) n, levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n = Pb.Mid.mu r M n j hT (Pb.bW r M n j (y.1 n))) :
    Pin F M j := fun n =>
  ⟨PinP.mm r M n hT, PinP.isMu_mmG r M n hT, fun y => (hβ y n).trans (PinP.mm_pull r M n j hT (y.1 n)).symm⟩

theorem PinP.pin_lev (r : Res l K) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) (F : Pb.Fac r N) (hF : Pb.Pinned r hT F)
    (M : Model l K) (hM : M.Sm) (j : ℕ) (y : Pb.LW r M j) (n : ℕ) :
    levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n = Pb.Mid.mu r M n j hT (Pb.bW r M n j (y.1 n)) := by
  refine (congrArg (fun w => levH w n) ((hF M hM j).2 ((1 : Pb.AW r) ⊗ₜ y))).trans ?_
  change Pb.Mid.mu r M n j hT ((1 : Pb.AW r) • Pb.bW r M n j (y.1 n)) = _
  exact congrArg (Pb.Mid.mu r M n j hT) (one_smul _ _)

theorem PinP.pin_fixed (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N ∧ ∃ F : Pb.Fac r N, ∀ M : Model l K, M.Sm → ∀ j, Pin F M j := by
  obtain ⟨N, hfN, hT⟩ := PinP.teich_dvd r f hf
  obtain ⟨F, hF⟩ := Pb.fac_ex r hT (fun M n j x => Pb.Mid.mu_nu r N hT M n j x) (Pb.G3.w_phi r) (fun g w => Pb.G3.w_fix r g w)
  exact ⟨N, hfN, hT, F, fun M hM j => PinP.pin_of r hT F M j fun y n => PinP.pin_lev r hT F hF M hM j y n⟩

theorem pinEx : PinEx := fun _ _ _ _ r f hf => PinP.pin_fixed r f hf

end CrystallineSemistableComparison.crystallineComparison
