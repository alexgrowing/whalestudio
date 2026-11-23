import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.eigTS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ), EigT φ w W ψ → EigS φ w W (ψ 0 / ψ 1) := by
  intro L _ _ _ V _ _ φ w W ψ h t ht
  have hd : Sig.SDom ![t, t⁻¹] := by
    intro i j hij
    have h0 : valuation (Kw w) (t : Kw w) ≠ 0 := by simp
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact ht.trans ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 ht)
  have e : Dict.expo ![ψ 0 / ψ 1, 1] ![t, t⁻¹] = Dict.expo ψ ![t, t⁻¹] := by
    simp [Dict.expo, torusChar, Fin.prod_univ_two, div_eq_mul_inv]
  rw [e]; exact h _ hd
