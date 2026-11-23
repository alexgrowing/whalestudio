import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

namespace UpperTheory.V.Z.Tf.GOne

def One {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n) (π : CuspSub E n) : Prop :=
  D.c = 1 ∧ ∀ i, ∃ e : D.N i = n, e ▸ D.V i = π.V

def CuspOrTwo : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
  ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
    (∃ P : CuspSub E N, P.V = V) ∨ ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 2 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ AscEmb V P d

def NotTwo : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a) (π : CuspSub E N), 1 ≤ a → 2 ≤ d → IsDiscrete V → AscEmb V P d →
  ¬ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (B : Multiset ℂˣ),
    IsLocCompGL V w σ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B ∧ (CG.mk π).HasSat w B

def CsdDisc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → IsDiscrete π.V

def OnePre : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → IsDiscrete π.V → ∃ D : Pre E n, One D π ∧ D.Reg

def OneSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (D : Pre E n),
  One D π → ∀ w B, (CG.mk π).HasSat w B ↔ D.Sat w B

def CsdSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B ∧
    ∀ u, ConjPl w u → (CG.mk π).HasSat u (B.map (·⁻¹))

def OnlyOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
  (D D' : Pre E n) (e : Fin D.c ≃ Fin D'.c), D.Reg → One D' π → (∀ i w, D.cls i w = D'.cls (e i) w) → One D π

end UpperTheory.V.Z.Tf.GOne

end
