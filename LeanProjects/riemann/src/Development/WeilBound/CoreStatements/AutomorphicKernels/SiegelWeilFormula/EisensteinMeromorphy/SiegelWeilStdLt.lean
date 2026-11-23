import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.Khead

theorem siegelWeilStd_lt (h : SWStdLt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) r s r' s', n < m → B.IsGood σ → 1 ≤ m → 1 ≤ n →
    min r s = 0 → (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  intro F E _ _ _ _ _ σ B m n A Y r s r' s' hnm hgood hm hn hmin hsign χ hχ hres κ _ dd om S l hdbl b K a
    hfr hK ha μ D hμ hD Φ hΦ hfin
  have key := h F E σ B m n A Y r s r' s' χ κ dd om S l b K a μ D Φ
    ⟨hgood, hm, hn, hnm, hmin, hsign, hχ, hres, hdbl, hfr, hK, ha, hμ, hD, hΦ, hfin⟩
  have hEq : thetaMean om S μ D Φ =
      fun x => (if n < m then (1 : ℂ) else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
    funext x
    rw [if_pos hnm, one_mul]
    try rfl
  rw [hEq] at key
  exact key

end PositivityTheory.SiegelWeilFormula.Khead
