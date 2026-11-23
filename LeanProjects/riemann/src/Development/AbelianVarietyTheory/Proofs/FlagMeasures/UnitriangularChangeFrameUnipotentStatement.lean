import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeFrameUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_change_frame_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, Uni A → (∀ a b, A a b ∈ M.L.O) → ∃ n ∈ Fr.N, (∀ c : Fin r, n (Fr.f c.castSucc) = ∑ a, A a c.castSucc • Fr.f a) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  first | exact @GlobalTheory.LocOver.UnipLevi.levi_integral | exact GlobalTheory.LocOver.UnipLevi.levi_integral | (intros; apply GlobalTheory.LocOver.UnipLevi.levi_integral <;> assumption)
