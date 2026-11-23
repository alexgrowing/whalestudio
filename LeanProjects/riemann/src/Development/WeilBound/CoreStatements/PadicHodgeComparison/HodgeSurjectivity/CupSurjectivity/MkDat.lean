import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.StepA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.GenPb

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem mkDat (hC : CupLaws) (hK : HodgeKill) (hD : DiagEt3) (P : HTPre l K) [FiniteDimensional ℚ_[l] K] {M : Model l K}
    {d : ℕ} (hd : 1 ≤ d) (hM : M.Sm) (hs : SmoothOfRelativeDimension (d + 1) M.p) (S : Sq M (d + 1)) (hEt : Etale S.D.f) :
    Nonempty (Dat hC P M d) := by
  obtain ⟨r⟩ := GlobalTheory.CompanionTheory.RootsC.rootsEx l
  obtain ⟨v, hv⟩ := (P.first_chern_class_exists S.Y S.smY S.D hEt S.loc).1 r
  obtain ⟨e, he, -⟩ := (P.first_chern_class_exists S.Y S.smY S.D hEt S.loc).2
  obtain ⟨c, w, z, m₀, a₀, b₀, ab₀, m, i, j, hij, a, b, ab, one, N, hz, hcz, hcup₀, hcup, hjne, hdec, hone, hN, hli,
    hsum₀⟩ := hD l K M d hd hM hs S hEt r v hv
  have := (sm_gen S.smP).1
  have := (sm_gen S.smP).2
  have := proper_genMap S.π S.hπ S.smY S.smP
  refine ⟨⟨S, c, m₀, a₀, b₀, ab₀, m, i, j, hij, a, b, ab, one, N, hcup₀, hcup, hjne, hdec, hone, hN, hli, hsum₀, ?_⟩⟩
  intro A a' n' y hy Θ
  apply stepA hC P S hEt r v hv e he c w z hz hcz A
  intro C hCd
  rw [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply,
    killR hK (↥K) M.gen S.P.gen S.Y.gen S.P.q (Model.genMap S.Δ S.hΔ) (Model.genMap S.π S.hπ) S.Y.q
      (Model.genMap_q S.π S.hπ) M.q (Model.genMap_q S.Δ S.hΔ) (genD S.D) (d + 1) (by omega) S.blow e he A (2 + 2 * d)
      a' n' C y hCd hy, map_zero]

end CrystallineSemistableComparison.Onto

end
