import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mreal_hom_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f _ Y hY
  set L := bk.evW with hL
  set Φ : WCb l →+* WCb l := (frobW l).toRingHom with hΦ
  have hc : ∀ x, L (frobS l bk.a x) = Φ (L x) := by
    intro x
    simp only [hL, hΦ, BK.evW, RingHom.comp_apply, bk.ev_frob, AlgHom.coe_toRingHom]
    exact (frobW_inclW _).symm
  have hsm : ∀ {m n : Type} (c : bk.S) (M : Matrix m n bk.S), (c • M).map L = L c • M.map L := by
    intro m n c M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply]
  have hTΦ : ∀ {m n : Type} (M : Matrix m n (WCb l)), M.map (frobW l) = M.map Φ := fun _ => rfl
  have hz : (zW f).map Φ = zW f := by
    ext i j; simp [zW, hΦ, Matrix.map_apply]
  have hYΦ : (Y.map (frobS l bk.a)).map L = (Y.map L).map Φ := by
    refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply]; exact hc _
  have φT := hT.φ
  have φT' := hT'.φ
  rw [hTΦ] at φT φT'
  have hYf : T'.map Φ * (Y.map L).map Φ = zW f * T.map Φ := by
    rw [← Matrix.map_mul, hY, Matrix.map_mul, hz]
  have key : T' * (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L =
      T' * (bk.E ^ S'.a • (Y * S.A)).map L := by
    rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hYΦ, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← φT', map_pow, map_pow, Matrix.smul_mul, smul_smul, hYf, hY, Matrix.mul_assoc,
      ← φT, Matrix.mul_smul, smul_smul, mul_comm]
  obtain ⟨u, hu⟩ := hT'.unit
  have key2 : (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L = (bk.E ^ S'.a • (Y * S.A)).map L := by
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) key
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    exact this
  have hinj := (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.1
  refine Matrix.ext fun i j => ?_
  exact hinj (congrFun (congrFun key2 i) j)

end GlobalTheory.BSP
