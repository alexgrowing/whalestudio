import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRedX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) : TupV (E := E) v n (a + 1) :=
  Fin.snoc (α := fun _ => Fin n → Fv F v ⊗[F] E) X w

theorem augT_castSucc {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (i : Fin a) :
    augT v X w i.castSucc = X i := by
  simp [augT]

def IsoExt (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w : Fin n → Fv F v ⊗[F] E, IsPrim v Λ (augT v X w) ∧ gramR (Fv F v) σ J (augT v X w) = T

theorem extP_of (a : ℕ) (Y : TupV (E := E) v n a) (hn : a + 1 ≤ n) (hI : IsoExt σ J ψ v Λ a Y) :
    ExtP σ J ψ v Λ a Y := by
  intro h hG
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hU : UnitV σ J ψ v Λ :=
    unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  obtain ⟨T, hTu, hext⟩ := hI hG
  obtain ⟨hS, hL, hSD, hUn, -, hP⟩ := hG
  obtain ⟨wY, hPY, hgY⟩ := hext Y hP rfl
  have hGY : GoodY σ J ψ v Λ (a + 1) (augT v Y wY) := ⟨hS, hL, hSD, hUn, hn, hPY, by rw [hgY]; exact hTu⟩
  have hE := extOrth_of σ J ψ v Λ (a + 1) (augT v Y wY) (oSub (E := E) v) (oSmul v Λ)
    (orthoB_of σ J ψ v Λ (a + 1) (augT v Y wY) hU)
  have hT : IsUnit (gramR (Fv F v) σ J (augT v Y wY)).det := by
    obtain ⟨u, -, -, hu⟩ := hTu
    rw [hgY]
    exact ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  refine ⟨gT v hn (gramR (Fv F v) σ J (augT v Y wY)), fun X hX hXY => ?_⟩
  obtain ⟨wX, hPX, hgX⟩ := hext X hX hXY
  obtain ⟨Z, hZb, hZe, hZg⟩ := hE hn hGY (augT v X wX) hPX.1 (by rw [hgX, hgY])
  refine ⟨Z, hZb, fun i => ?_, hZg, isUnit_det_colM σ J v hn _ hT Z hZg⟩
  have e1 : eSp h (Sum.inl i) = eSp hn (Sum.inl i.castSucc) := by
    apply Fin.ext
    simp [eSp]
  rw [e1, hZe i.castSucc, augT_castSucc]

end PI.OmVd
