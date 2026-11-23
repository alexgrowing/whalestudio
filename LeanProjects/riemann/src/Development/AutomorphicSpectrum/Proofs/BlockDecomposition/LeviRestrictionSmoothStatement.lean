import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ), F ∈ Sm E (r + s) → (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | exact GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice <;> assumption)
