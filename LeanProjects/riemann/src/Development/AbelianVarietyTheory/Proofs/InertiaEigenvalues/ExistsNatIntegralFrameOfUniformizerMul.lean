import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FlatLift

theorem kmul_int : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  intro D S T βS βT ϖ hϖ
  let I : Ideal (𝓞 D.host.E) := Ideal.span {ϖ}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hϖ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem I)
  refine ⟨Ideal.absNorm I, Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)), fun u hu => ?_⟩
  have hk : ((Ideal.absNorm I : ℕ) : D.host.E) = (c : D.host.E) * (ϖ : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simpa using this.symm
  have hm : (((Ideal.absNorm I) • u : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (Formalism.IndefR.Datum.toEAf D) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) •
        ((u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map
          (Formalism.IndefR.Datum.toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, nsmul_eq_mul]
    rw [map_natCast]
    have h1 : Formalism.IndefR.Datum.toEAf D (incA D (ϖ : D.host.E)) = Formalism.IndefR.Datum.eToEAf D (ϖ : D.host.E) := rfl
    rw [h1, ← mul_assoc, ← map_mul, ← hk, map_natCast]
  intro i j
  have he : frMapO S T βS βT ((Ideal.absNorm I) • u) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) • frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w) := by
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul]
  rw [he, Matrix.smul_apply, smul_eq_mul]
  exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem (Subring.subset_closure (Or.inl ⟨⟨((c : 𝓞 D.host.E) : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)) (hu i j)

end GlobalTheory.FlatLift
