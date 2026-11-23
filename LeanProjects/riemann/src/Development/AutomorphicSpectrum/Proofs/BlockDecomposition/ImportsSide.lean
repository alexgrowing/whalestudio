import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRankOne

theorem weakFEPair_Λ₀_of_smul (P Q : WeakFEPair ℂ) (c : ℂ) (hf : Q.f = c • P.f)
    (hg : Q.g = c • P.g) (hk : Q.k = P.k) (hε : Q.ε = P.ε) (hf₀ : Q.f₀ = c • P.f₀)
    (hg₀ : Q.g₀ = c • P.g₀) : Q.Λ₀ = c • P.Λ₀ := by
  have hmod : Q.f_modif = c • P.f_modif := by
    funext x
    simp only [WeakFEPair.f_modif, Pi.add_apply, Pi.smul_apply, Set.indicator_apply, hf, hf₀, hg₀, hk, hε,
      smul_eq_mul]
    split_ifs <;> ring
  funext s
  simp only [WeakFEPair.Λ₀, hmod, Pi.smul_apply]
  exact mellin_const_smul P.f_modif s c

end GlobalTheory.CompanionTheory.EisRankOne
