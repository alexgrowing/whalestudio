import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.RamSum
section Norms
variable {F : Type} [Field F] [NumberField F]
end Norms
end GlobalTheory.BigTop.Fun.RamSum
namespace GlobalTheory.BigTop.Fun
open RamSum
theorem ramified_sums_seventh_bound_alt : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound' := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ _ => ?_⟩⟩⟩
  refine ⟨42, fun C hC => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ d _ => ?_⟩
  obtain ⟨-, -, hg, h1, h2, -⟩ := hF.1.2.2.2.2.2.2.2.2 x hx i
  have h3 := hF.2.2.1 x hx i
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine leaves_of_sum d.O C p.Z.b (Real.log_nonneg hb) (d.G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) (fun v _ => isPrimePow_absNorm v)
    (ramifiedPlaces_sum_log_absNorm_le d.G.pl (Fm.L x i).sc hg h1 h2 h3) (fun v _ => ?_)
    (le_PPF d.O hC hb ?_ ?_ ((Fm.D x i).host.g_prime 0).pos ((Fm.D x i).host.g_prime 1).pos (Fm.D x i).host.pde_prime.pos
      (Fm.D x i).host.pde'_prime.pos (discr_ne_zero _))
  · unfold FunIn.O FunIn.data
    dsimp only
    split_ifs <;> omega
  · have := (Fm.D x i).R.m_le_f
    have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.f
    unfold Ranks.f Ranks.n
    omega
  · have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.k + (Fm.D x i).R.m
    omega
end GlobalTheory.BigTop.Fun
end
end
