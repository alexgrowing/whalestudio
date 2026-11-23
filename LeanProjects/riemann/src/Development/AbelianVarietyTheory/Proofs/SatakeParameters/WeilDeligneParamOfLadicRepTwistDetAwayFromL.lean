import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

namespace TwistAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem matrix_eq_zero_of_isNilpotent {K : Type*} [Field K] {M : Matrix (Fin 1) (Fin 1) K}
    (hM : IsNilpotent M) : M = 0 := by
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hM
  rw [Matrix.trace_fin_one] at h1
  ext i j
  fin_cases i; fin_cases j
  simpa using h1.eq_zero

theorem end_eq_zero_of_isNilpotent {f : Module.End ℂ (Fin 1 → ℂ)} (hf : IsNilpotent f) : f = 0 := by
  have h1 := matrix_eq_zero_of_isNilpotent (hf.map
    (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ))
  have h2 : (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) f =
      (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) 0 := by
    rw [h1, map_zero]
  exact (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ).injective h2

theorem twGL_det_val (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l))
    (g : G E Ω) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • (ρ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Algebra.smul_def]

variable {t : Ine (F := E) A →* Multiplicative ℤ_[l]}

theorem isMonodromy_zero_of_line {χ : G E Ω →* GL (Fin 1) (Qbar l)} {N : Matrix (Fin 1) (Fin 1) (Qbar l)}
    (hN : IsMonodromy t χ N) : IsMonodromy t χ 0 := by
  rwa [matrix_eq_zero_of_isNilpotent hN.1] at hN

theorem isMonodromy_twGL {ρ : G E Ω →* GL (Fin a) (Qbar l)} {χ : G E Ω →* GL (Fin 1) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} (hN : IsMonodromy t ρ N) (hχ : IsMonodromy t χ 0) :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨-, U', hU', H'⟩ := hχ
  refine ⟨h1, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [twGL_det_val, H' σ hσ.2, H σ hσ.1]
  simp

theorem wdMat_twGL {φ : Weil h} (hφ : deg φ = 1) (ρ : G E Ω →* GL (Fin a) (Qbar l))
    (χ : G E Ω →* GL (Fin 1) (Qbar l)) (N : Matrix (Fin a) (Fin a) (Qbar l)) (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N g =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • wdMat t hφ ρ N g := by
  rw [wdMat, wdMat, twGL_det_val, smul_mul_assoc]

theorem isFrobSS_tensor_line {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {N : Module.End ℂ V} {a₀ : WDRep h V}
    {ψ : Weil h → Module.End ℂ (Fin 1 → ℂ)} {b₀ : WDRep h (Fin 1 → ℂ)}
    (ha : IsFrobSS ρ N a₀) (hb : IsFrobSS ψ 0 b₀) :
    IsFrobSS (fun g => TensorProduct.map (ρ g) (ψ g)) (N.rTensor (Fin 1 → ℂ)) (a₀.tensor b₀) := by
  have hψ : ∀ g, b₀.ρ g = ψ g := fun g =>
    (sub_eq_zero.mp (end_eq_zero_of_isNilpotent (hb.2 g).2)).symm
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1, LinearMap.lTensor_zero, add_zero], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ, hψ]
    show TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, (ha.2 g).1.eq]
  · rw [WDRep.tensor_ρ, hψ]
    have e1 : TensorProduct.map (ρ g) (ψ g) - TensorProduct.map (a₀.ρ g) (ψ g) =
        (ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ) * (ψ g).lTensor V :=
      TensorProduct.ext' fun x y => by simp [TensorProduct.sub_tmul]
    rw [e1]
    have hc : Commute ((ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ)) ((ψ g).lTensor V) := by
      show _ * _ = _ * _
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    exact hc.isNilpotent_mul_right ((ha.2 g).2.map (Module.End.rTensorAlgHom ℂ V (Fin 1 → ℂ)))

def lineEquiv (V : Type) [AddCommGroup V] [Module ℂ V] : TensorProduct ℂ V (Fin 1 → ℂ) ≃ₗ[ℂ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V)

@[simp] theorem lineEquiv_tmul (V : Type) [AddCommGroup V] [Module ℂ V] (x : V) (y : Fin 1 → ℂ) :
    lineEquiv V (x ⊗ₜ y) = y 0 • x := by
  simp [lineEquiv]

end TwistAway

open TwistAway in

theorem wdOf_twGL_det : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf h hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf h hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.WeilDeligne
