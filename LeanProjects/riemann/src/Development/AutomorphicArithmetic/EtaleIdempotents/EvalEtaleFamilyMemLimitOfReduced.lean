import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimAlg
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.evalEtaleFamily_mem_limit_of_reduced :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Red → ∀ (M : Model l K) (j : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (fun n => evE e M j n v c) ∈ (M.MS j).lim := by
  intro l _ K e he M j ι _ v c n
  have h2 : ∀ k, GlobalTheory.EtC.red (l ^ (n + 1)) (l ^ n) M.spc (j : ℤ) 0 ((v k).lev (n + 1)) = (v k).lev n :=
    fun k => (show GlobalTheory.EtC.Hl l M.spc j 0 from v k).2 n
  have h3 : ∀ k, (M.MS j).r n (e M (n + 1) j ((v k).lev (n + 1))) = e M n j ((v k).lev n) :=
    fun k => (he M n j ((v k).lev (n + 1))).trans (congrArg (e M n j) (h2 k))
  have hk : ∀ k, (M.MS j).r n (c k • e M (n + 1) j ((v k).lev (n + 1))) = c k • e M n j ((v k).lev n) := by
    intro k
    exact (LinearMap.map_smul ((M.MS j).r n) (c k) _).trans (congrArg (fun y => c k • y) (h3 k))
  exact (map_sum ((M.MS j).r n) _ _).trans (Finset.sum_congr rfl fun k _ => hk k)
