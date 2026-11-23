import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem strat_homGal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY g
  let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
  have hG : ∀ z : ℤ_[l], G (algebraMap ℤ_[l] (WCb l) z) = algebraMap ℤ_[l] (WCb l) z :=
    fun z => (galW l (g : GQ l)).commutes z
  have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M := by
    intro m n M; exact Matrix.ext fun i j => hG _
  have hYG : (Y.map bk.evW).map G = (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := by
    exact Matrix.ext fun i j => galW_inclW (g : GQ l) (bk.ev (Y i j))
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  have h1 := congrArg (fun M => M.map G) hY
  simp only [Matrix.map_mul, hzG, hYG] at h1

  have e1 : T' * ((S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) *
      (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) =
      T' * ((Y.map (BK.hf bk.ι)).map (inclW l) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) := by
    have a1 := hT'.gal g
    have a2 := hT.gal g
    have a3 : T'.map (galW l (g : GQ l)) = T'.map G := rfl
    have a4 : T.map (galW l (g : GQ l)) = T.map G := rfl
    have a5 : (Y.map (BK.hf bk.ι)).map (inclW l) = Y.map bk.evW := Matrix.map_map
    rw [a3] at a1
    rw [a4] at a2
    rw [a5]
    calc _ = (T' * (S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) *
          (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := (Matrix.mul_assoc _ _ _).symm
      _ = zW (ρ' g) * (T'.map G * (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) := by
          rw [← a1, Matrix.mul_assoc]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = (T' * Y.map bk.evW) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) := by
          rw [a2, hY, Matrix.mul_assoc]
      _ = _ := Matrix.mul_assoc _ _ _
  obtain ⟨u, hu⟩ := hT'.unit
  rw [← hu] at e1
  have e2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) e1
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e2
  apply Matrix.map_injective (f := inclW l) inclW_injective
  exact (Matrix.map_mul (f := inclW l)).trans (e2.trans (Matrix.map_mul (f := inclW l)).symm)

end GlobalTheory
