import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_epsilon_power : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : ((base l).cont ℤ_[l]).A,
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
  Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | exact GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | (intros; apply GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta <;> assumption)
