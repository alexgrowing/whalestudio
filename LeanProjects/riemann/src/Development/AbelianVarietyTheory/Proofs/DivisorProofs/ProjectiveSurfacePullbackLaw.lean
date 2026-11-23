import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRochHomDualAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePushforwardEulerCharTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardTwistHomDualIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDegreeOfEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenRankPushforwardAmpleTwistStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.PullCh

theorem pullbackLaw : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T],
    IsProjSurface k T → PullbackLaw k T := by
  intro k _ T _ _ hT T' _ _ hT' ρ d hc hd E r hE
  obtain ⟨-, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hT'.isProjOver
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.DualPull.exists_dual_pullback T T' ρ
  have := hθ E r hE
  have hG := hE.pullback ρ
  have hD := hE.dual.pullback ρ
  refine GlobalTheory.T.second_chern_degree_of_euler_char k T' hT' _ _ r hG ⟨asIso (θ E)⟩ L hL.isLB _ ?_
  have e₁ := GlobalTheory.T.finite_pushforward_euler_char_twist k T T' hT hT' ρ hc L hL _ hG.isFiniteQC
  have e₂ := GlobalTheory.T.finite_pushforward_euler_char_twist k T T' hT hT' ρ hc L hL _ hD.isFiniteQC
  have e₃ := GlobalTheory.T.finite_pushforward_euler_char_twist k T T' hT hT' ρ hc L hL _ (isVB_structureModule T').isFiniteQC
  filter_upwards [e₁, e₂, e₃] with n h₁ h₂ h₃
  have hM := isLB_lbPow hL.isLB n
  obtain ⟨⟨φ₁⟩, ⟨φ₂⟩⟩ := GlobalTheory.T.pushforward_twist_hom_dual_iso T T' ρ E r hE _ hM
  have hA := GlobalTheory.T.riemann_roch_hom_dual_average k T hT E r hE _ h₃.1
  rw [GlobalTheory.T.gen_rank_pushforward_ample_twist k T T' hT hT' ρ hc d hd _ hM] at hA
  rw [← h₁.2, ← h₂.2, ← h₃.2, chi_congr k φ₁, chi_congr k φ₂, hA]

end GlobalTheory.PullCh
