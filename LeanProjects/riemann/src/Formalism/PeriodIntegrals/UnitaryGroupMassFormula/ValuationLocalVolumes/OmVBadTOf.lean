import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimT (a : ℕ) : Set (TupV (E := E) v n a) := {X | IsPrim v Λ X}

def prodEtaB (n a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (n - a) n, (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)))

def GoodP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ ∧ (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) ∧
  IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧ a ≤ n ∧ IsPrim v Λ Y

def OrbP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y

def FibP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (PrimT v Λ a) =
      dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def CountP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) =
      ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * prodEtaB (E := E) v n a) * dX σ J ψ v a (LamT v Λ a)

def PrimCos (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∀ X ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, X + Z ∈ PrimT v Λ a

theorem smul_prim {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  have hki : ∀ i, (k • Y) i =
      Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) (Y i) :=
    fun i => rfl
  refine ⟨fun i => ?_, fun c hc => hY.2 c ?_⟩
  · rw [hki]; exact (hk (Y i)).1 (hY.1 i)
  · have e : (∑ i, c i • (k • Y) i) =
        Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _)
          (∑ i, c i • Y i) := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_smul, hki]
    rw [e] at hc
    exact (hk _).2 hc

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def OmVdEx : Prop := ∀ v : PlX X, StdHyp X.B.I.cm.sig X.B.I.J ψ →
  (∃ μ, SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) μ) ∧
    ∃ ν, SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) ν

def OmVdUniq : Prop := ∀ v : PlX X, OmUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

def OmVdOrb : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  OrbP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdFib : Prop := ∀ v : PlX X, FibP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdCnt : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  CountP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdSdW : Prop := ∀ v : PlX X, SdVolW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)

def OmVdSdH : Prop := ∀ v : PlX X, SdVolH X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem a_le_n' : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem omVBadT_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hEx : OmVdEx X ψ) (hUq : OmVdUniq X ψ) (hOrb : OmVdOrb X u' ψ) (hFib : OmVdFib X u' ψ)
    (hCnt : OmVdCnt X u' ψ) (hW : OmVdSdW X ψ) (hH : OmVdSdH X ψ) : OmVBadT X u' ψ := by
  intro hC hS v hv hSD hUn hP
  have hS' := hStd hC hS
  have hG : GoodP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) :=
    ⟨hS', hLat, hSD, hUn, a_le_n' X, hP⟩
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨hWe, hHe⟩ := hEx v hS'
  rw [← hGram v]
  set T := gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) with hTdef
  set ω := omAt X.B.I.cm.sig X.B.I.J ψ v T with hω
  set O := {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} with hO
  have hsub : O ⊆ PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) := by
    rintro Z ⟨k, hk, rfl⟩
    exact smul_prim X.B.I.cm.sig X.B.I.J v (abelian₂ X) k hk _ hP
  have hsup : PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) ⊆
      O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := by
    intro Z hZ
    by_cases hg : gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T
    · exact Or.inl (hOrb v hv hG Z hZ hg)
    · exact Or.inr hg
  have hEq : ω O = ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS)) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
        ≤ ω (O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero X.B.I.cm.sig X.B.I.J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, hFib v hG hWe hHe (hUq v hS').1 ϖ hϖ, hCnt v hv hG hWe ϖ hϖ, hW v hS' hLat hSD hUn hWe,
    hH v hS' hUn hHe ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) -
      ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ)) /
        absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEtaB
  have : (0 : ℝ) < qv v ^ (-(((D.R.rS + 1 + D.R.rS : ℕ) : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end Loc

end PI.OmVd
