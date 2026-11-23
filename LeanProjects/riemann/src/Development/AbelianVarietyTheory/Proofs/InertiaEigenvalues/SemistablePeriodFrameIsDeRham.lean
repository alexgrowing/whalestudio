import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodCocycleFrobeniusRelationOnDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameFrobeniusIsUnitDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WDR

theorem frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  intro l hl K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ hκ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨hmap, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i, hi⟩ := hmap _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := hmap _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0 (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := hmap _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ l h0
    (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  set V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z with hV
  have hVi : V.map i = s.X.map bk.iS * Z.map i := by
    rw [hV, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  set H := s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ with hH
  have hHu : IsUnit H := GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc l K bk τ d ρ s Ψ Z hΨ hZ
  intro m
  exact GlobalTheory.T.exists_beta_of_disc_cocycle_alt l K bk d s.N s.κ (fun g => (F.ε g).map WittVector.frobenius) H i hi hHu s.log
    (fun g G hG => GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc l K bk τ d ρ s g G Φ i Ψ V (F.ε g) hG hΦ hi hΨ
      (GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc l K bk τ hτ d ρ hρ s g G Φ hG hΦ) (by rw [hVi]; exact hκ g G i hG hi)) m

end GlobalTheory.BKLim.WDR
