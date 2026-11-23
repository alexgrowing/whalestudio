import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.EfNear

variable {D : D7} (X : HidaSetting D)

theorem nat_smul_mL (k : ℕ) {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) :
    (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem dvd_smul_mL {d M : ℕ} (hd : d ∣ M) {x : VA X.B.I}
    (hx : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g) :
    (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), mul_smul]
  exact nat_smul_mL X k hx

theorem term_near {v0 w0 v w y : VA X.B.I} (hw0 : w0 ∈ X.B.I.Lf) (hy : y ∈ X.B.I.Lf) {c1 c2 c3 : ℕ}
    (h1 : (c1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v0 - v) ∈ mL X.B.I X.B.g)
    (h2 : (c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w) ∈ mL X.B.I X.B.g)
    (h3 : (c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v ∈ X.B.I.Lf) :
    ((c1 * c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I w y • v - hA X.B.I w0 y • v0) ∈
      mL X.B.I X.B.g := by
  have e : hA X.B.I w y • v - hA X.B.I w0 y • v0 =
      -(hA X.B.I w0 y • (v0 - v)) - hA X.B.I (w0 - w) y • v := by
    rw [GlobalTheory.St.G.FrameClose.hA_sub_left, smul_sub, sub_smul]; abel
  rw [e, smul_sub]
  refine sub_mem ?_ ?_
  · refine dvd_smul_mL X (dvd_mul_of_dvd_left (dvd_mul_right c1 c2) c3) ?_
    rw [smul_neg, smul_comm]
    refine neg_mem ?_
    have := (mL X.B.I X.B.g).smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int hw0 hy⟩ : IntAf X.B.I.F X.B.I.E) h1
    rwa [Subring.smul_def] at this
  · refine dvd_smul_mL X (d := c2 * c3) ⟨c1, by ring⟩ ?_
    have e2 : ((c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (w0 - w) y • v) =
        hA X.B.I ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w)) y •
          ((c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) := by
      rw [GlobalTheory.St.G.FrameClose.hA_nat_left, smul_smul, smul_smul, Nat.cast_mul]
      congr 1; ring
    rw [e2]
    exact Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X (GlobalTheory.St.G.FrameClose.zmod_of_mL h2 hy) h3

end GlobalTheory.ScalW.EfNear

namespace GlobalTheory.ScalW

open GlobalTheory.ScalW.EfNear in

theorem ef_near_ref : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  intro D X
  choose c1 hc1 h1 using fun a => (X.basisApprox a).1
  choose c2 hc2 h2 using fun a => (X.basisApprox a).2
  choose c3 hc3 h3 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).1 (X.basisApprox a).1
  choose c4 hc4 h4 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).2 (X.basisApprox a).2
  refine ⟨∏ a, c1 a * c2 a * c3 a * c4 a,
    Nat.Coprime.prod_left fun a _ => (((hc1 a).mul (hc2 a)).mul (hc3 a)).mul (hc4 a), ?_⟩
  intro y hy a
  have hdvd : c1 a * c2 a * c3 a * c4 a ∣ ∏ b, c1 b * c2 b * c3 b * c4 b :=
    Finset.dvd_prod_of_mem (fun b => c1 b * c2 b * c3 b * c4 b) (Finset.mem_univ a)
  constructor
  · refine dvd_smul_mL X (d := c1 a * c2 a * c3 a) (dvd_trans ⟨c4 a, rfl⟩ hdvd) ?_
    exact term_near X (v0 := X.e0 a) (w0 := X.f0 a) (v := eV X a) (w := fV X a) (X.vectorsInLattice.1 a).2 hy (h1 a) (h2 a) (h3 a)
  · refine dvd_smul_mL X (d := c2 a * c1 a * c4 a) (dvd_trans ⟨c3 a, by ring⟩ hdvd) ?_
    exact term_near X (v0 := X.f0 a) (w0 := X.e0 a) (v := fV X a) (w := eV X a) (X.vectorsInLattice.1 a).1 hy (h2 a) (h1 a) (h4 a)

end GlobalTheory.ScalW
