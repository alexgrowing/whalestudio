import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FV
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlobPush

theorem push_kc : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  intro K _ X Y q p u hu U W τ hτ a
  have key : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)) (α : U.ι),
      CrystallineSemistableComparison.Pb.InU (U.U α) T → CrystallineSemistableComparison.Pb.InU (W.U (τ α)) ((pullM u hu a).G.obj T) := by
    intro T α h
    have h0 : U.U α ≤ u ⁻¹ᵁ W.U (τ α) := by
      have h1 := hτ 0 (fun _ => α)
      simpa [CrystallineSemistableComparison.Pb.capO] using h1
    unfold CrystallineSemistableComparison.Pb.InU at h ⊢
    change ⊤ ≤ (TopologicalSpace.Opens.map (pt T ≫ u).base).obj (W.U (τ α))
    exact h.trans ((TopologicalSpace.Opens.map (pt T).base).monotone h0)
  have ktf : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)),
      CrystallineSemistableComparison.Pb.TF 1 (a + 1) T → CrystallineSemistableComparison.Pb.TF 1 (a + 1) ((pullM u hu a).G.obj T) := by
    intro T h
    exact h
  refine ⟨fun T hT => ?_, fun α T hT => ?_⟩
  · obtain ⟨hTF, V, ⟨α, rfl⟩, hV⟩ := hT
    exact ⟨ktf T hTF, W.U (τ α), ⟨τ α, rfl⟩, key T α hV⟩
  · exact key T.obj α hT

end GlobalTheory.CompanionTheory.OmGlobPush
