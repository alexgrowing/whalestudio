import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.Imports

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.tweyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (d : SD σ)

theorem actB_conj (x : d.G) (g : UA σ d.A.J) (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) = v := by
  unfold actB
  have hx : (x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp
  calc _ = (mat g * mat g⁻¹) * v * ((x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = v := by rw [mat_mul_inv, hx, Matrix.one_mul, Matrix.mul_one]

theorem comm_schr (g : UA σ d.A.J) (x : d.G) : ∀ w, ∀ φ ∈ schA F d.κ,
    (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) (schr d.B.ψ w φ) =
      schr d.B.ψ w ((d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) φ) := by
  intro w φ hφ
  obtain ⟨v, rfl⟩ := d.dd.e.surjective w
  have e1 : ∀ u, schr d.B.ψ (d.dd.e u) = d.dd.rho d.B.ψ u := fun u => rfl
  simp only [Module.End.mul_apply, e1]
  have h1 := (hS d).impl g⁻¹ v φ hφ
  have hp1 := (hS d).pres g⁻¹ φ hφ
  have h2 := (hO d).impl x (mat g⁻¹ * v) _ hp1
  have hp2 := (hO d).pres x _ hp1
  have h3 := (hS d).impl g (actB (cA σ) x (mat g⁻¹ * v)) _ hp2
  have hp3 := (hS d).pres g _ hp2
  have h4 := (hO d).impl x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) _ hp3
  beta_reduce at h1 h3
  rw [h1, h2, h3, h4, actB_conj]

theorem exists_scalar (g : UA σ d.A.J) (x : d.G) :
    ∃ c : ℂ, ∀ φ ∈ schA F d.κ, (d.S g * d.om x * d.S g⁻¹) φ = c • d.om x φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute d.B.ψ (std d) (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹)
    (fun l hl => by
      simp only [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact (hS d).adm _ _ ((hO d).adm _ _ ((hS d).adm _ _ ((hO d).adm _ _ hl))))
    (comm_schr d g x)
  refine ⟨c, fun φ hφ => ?_⟩
  have h := congrArg (d.om x) (hc φ hφ)
  rw [map_smul] at h
  rw [← h]
  simp only [Module.End.mul_apply]
  rw [← Module.End.mul_apply (d.om x) (d.om x⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end PositivityTheory.SiegelWeilFormula.tweyl
