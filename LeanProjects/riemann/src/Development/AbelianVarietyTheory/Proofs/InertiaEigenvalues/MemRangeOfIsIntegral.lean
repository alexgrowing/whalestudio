import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
open scoped Formalism.Per

namespace GlobalTheory.ExpImage.EmbFil

theorem mem_range_of_isIntegral {F Ω L B : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    [CommRing L] [Algebra F L] [CommRing B] [IsDomain B] [Algebra F B] [Algebra Ω B]
    [IsScalarTower F Ω B] (ι : L →ₐ[F] B) {x : L} (hx : IsIntegral F x) :
    ∃ a : Ω, algebraMap Ω B a = ι x :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := integralClosure Ω B) |>.2
    ⟨ι x, (hx.map ι).tower_top⟩ |>.imp fun _ h => congrArg Subtype.val h

theorem algebraMap_mem_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (T : LocTied l P AI) (a : Om l) : algebraMap (Om l) P.R.BdR a ∈ GlobalTheory.ExpImage.FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om a
  obtain ⟨-, hone, -⟩ := GlobalTheory.MemLoc.filD_laws l
  refine (T.fil _ 0 _).2 ?_
  have := Submodule.smul_mem _ y hone
  rwa [Algebra.smul_def, mul_one, ← h1] at this

theorem emb_mem_fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (LL : FinExt l) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥LL.1),
      ι x ∈ GlobalTheory.ExpImage.FilB P 0 := by
  intro l _ P AI T LL ι x
  have := (GlobalTheory.Per.TiedField.tied_field l P AI T).1.isDomain
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨a, ha⟩ := mem_range_of_isIntegral (Ω := Om l) ι (IsIntegral.of_finite ℚ_[l] x)
  rw [← ha]
  exact algebraMap_mem_zero T a

end GlobalTheory.ExpImage.EmbFil
