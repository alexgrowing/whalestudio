import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.NewformAut0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr

namespace UpperTheory.GalN.V

theorem dual_two {Γ k : Type} [Group Γ] [Field k] (W : Γ →* GL (Fin 2) k) : DualTw W (Matrix.GeneralLinearGroup.det.comp W) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
    have hd : ((Matrix.GeneralLinearGroup.det.comp W s : kˣ) : k) = (W s).val.det := rfl
    rw [hd, Matrix.det_fin_two (W s).val]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring⟩

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

def IsModularN (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}

theorem mod0 (h : D.IsModular ι W) : ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) := h
end

def AutEnd2N {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
    OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

theorem newAdm (P : Hypotheses₂) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ)
    (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hirr : IsIrr W)
    (hf : (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W)
    (hlev : Level l M ![(e : ℤ), -(e : ℤ)] W) (hcyc : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    AdmRN ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := hf
  exact ⟨hirr, mkQ' (newformAut0 P (2 * e + 1) (by omega) f l Ω ι W _ hf) fun _ => hw, hlev, ⟨_, hcyc, dual_two W⟩,
    Or.inr fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩

end UpperTheory.GalN.V
