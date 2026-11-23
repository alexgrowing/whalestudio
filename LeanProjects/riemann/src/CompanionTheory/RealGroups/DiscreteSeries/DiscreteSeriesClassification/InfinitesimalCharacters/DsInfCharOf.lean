import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.RgDsInf

def EigenNewton : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v

def AdjSum : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), ∑ a, ∑ b, (Matrix.adjugate ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) + (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z))) a b = ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) - ∏ s, (Polynomial.X + Polynomial.C (l s))

def GelfRec : Prop :=
  ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N

def CapToGelf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E → (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) → ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v

def GlRelUnit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ), Formalism.REAL.GlRel (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b)

def MapQdet : Prop :=
  ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (n : ℕ) (X : Fin n → Fin n → A) (u : ℂ) (k : ℕ), φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u ∧ φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k

def CoefWord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ

def CycEtr : Prop :=
  ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B), ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod = Formalism.REAL.etr X (m + 1)

def SmoothKFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ

def DSIff : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ

def CoefSmooth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H), Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ)

theorem dsInfChar_of (hC : CapToGelf) (hG : GlRelUnit) (hM : MapQdet) (hW : CoefWord) (hY : CycEtr)
    (hS : SmoothKFin) (hD : DSIff) (hF : CoefSmooth) (hcap : PI.DSInfCharCap.DSInfCharCap) :
    GlobalTheory.Dec.DSInfChar := by
  intro n ε lam H _ _ σ hlam hds v w hv _
  obtain ⟨hvs, hvs'⟩ := hS n ε lam H σ hlam hds v hv
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := hds.2.2.1
  let sv : GlobalTheory.SmoothVecMod.smoothVec ε σ := ⟨v, hvs⟩
  refine ⟨hF n ε H σ sv w, fun m g hg => ?_⟩
  have hgelf : GlobalTheory.Dec.gelf ε m (fun g => ⟪w, σ g v⟫_ℂ) g =
      ⟪w, σ g ((Formalism.REAL.etr (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b) (m + 1) sv :
        GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
    simp only [GlobalTheory.Dec.gelf]
    rw [← hY, LinearMap.sum_apply, Submodule.coe_sum, map_sum, inner_sum]
    exact Finset.sum_congr rfl fun a _ => hW n ε H σ hσ sv w _ g hg
  rw [hgelf]
  rcases n with _ | k
  · simp [Formalism.REAL.etr, GlobalTheory.Dec.gelfVal]
  · have hφ : (fun a b => GlobalTheory.CapelliCoef.freeAct hσ (PI.DSInfCharCap.Egl (k + 1) a b)) =
        fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b := by
      funext a b
      simp [GlobalTheory.CapelliCoef.freeAct, PI.DSInfCharCap.Egl]
    have hq : ∀ Y : ℂ, Formalism.REAL.qdet (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b)
        (Y + (((k + 1 : ℕ) : ℂ) - 1) / 2) sv = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • sv := by
      intro Y
      apply Subtype.ext
      have h1 := hcap (k + 1) ε lam H σ hlam (hD _ ε lam H σ hds) v hvs' Y
      have h2 := (GlobalTheory.CapelliCoef.actU_eq hσ
        (Formalism.REAL.qdet (PI.DSInfCharCap.Egl (k + 1)) (Y + (((k + 1 : ℕ) : ℂ) - 1) / 2)) sv).symm.trans h1
      rw [(hM _ _ (GlobalTheory.CapelliCoef.freeAct hσ) _ _ _ 0).1, hφ] at h2
      simpa using h2
    rw [hC _ k _ _ sv (hG _ ε H σ hσ) hq (m + 1)]
    simp [sv]

end CompanionTheory.RgDsInf
