import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsGroupFixesAdelicLatticeIffColumnsLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columns_group_fixes_adelic_lattice_iff_columns_lattice : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ((h : X.B.I.Gf) ∈ X.B.I.Kset ↔ ((∀ x, x ∈ hat D.host.F (Mq wt) ↔ y.1.1 *ᵥ x ∈ hat D.host.F (Mq wt)) ∧ ∀ x, (∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈ OAd D.host.F D.host.E) → (y.1.1 - 1) *ᵥ x ∈ hat D.host.F (Mq wt))) := by
  first | exact @GlobalTheory.St.G.stabK_iff | exact GlobalTheory.St.G.stabK_iff | (intros; apply GlobalTheory.St.G.stabK_iff <;> assumption)
