import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalY

private theorem witt_padicInt_hom_ext (l : ℕ) [Fact l.Prime] {k : Type} [CommRing k] [CharP k l]
    (f g : ℤ_[l] →+* WittVector l k) : f = g := by
  refine RingHom.ext fun x => sub_eq_zero.1 (WittVector.ext fun n => ?_)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have h : f x - g x = (f y - g y) * (l : WittVector l k) ^ (n + 1) := by
    rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.zero_coeff]
  exact WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self n)

theorem inclW_zA (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) : inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := by
  exact RingHom.congr_fun
    (witt_padicInt_hom_ext l ((inclW l).comp (Per.zA l)) (algebraMap ℤ_[l] (WCb l))) z

end GlobalTheory.BKLim.GalY

open GlobalTheory.BKLim.GalY in

theorem GlobalTheory.BKLim.gal_tauPow_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  intro l _ K bk τ N d ρ F Y hY g
  apply Matrix.map_injective (f := inclW l) (GlobalTheory.Prism.inclW_injective)
  have hsm : ∀ {m n : Type} (c : Ainf l) (M : Matrix m n (Ainf l)), (c • M).map (inclW l) = inclW l c • M.map (inclW l) :=
    fun c M => Matrix.ext fun i j => by simp
  have hz : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) :=
    Matrix.ext fun i j => inclW_zA l _
  have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) :=
    Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
  have hgal := F.gal g
  show Matrix.map _ (inclW l) = Matrix.map _ (inclW l)
  have hsg : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)),
      (c • M).map (galW l (g : GQ l)) = galW l (g : GQ l) c • M.map (galW l (g : GQ l)) :=
    fun c M => Matrix.ext fun i j => by simp
  rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hz, hg', hY, hsg, map_pow, map_pow, map_pow, GlobalTheory.Prism.galW_inclW,
    Matrix.mul_smul, hgal, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
