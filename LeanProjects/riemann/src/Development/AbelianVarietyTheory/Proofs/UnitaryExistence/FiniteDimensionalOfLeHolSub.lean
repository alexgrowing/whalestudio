import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) (k : Comp) : P k ∈ (X k).SS (la k) := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0
  induction hP using Submodule.span_induction with
  | mem P hP => exact hP k
  | zero => exact h0
  | add P Q _ _ h1 h2 => exact hadd _ h1 _ h2
  | smul a P _ h1 => exact hsmul a _ h1

theorem exists_finset_vanishing (X : Data E r) (la : Wt X.Ψ r) (hX : ∃ Y : DataX E r, Y.toData = X) :
    ∃ N : Finset (Frame X.Ψ r), ∀ P ∈ X.SS la, (∀ y ∈ N, P y = 0) → ∀ x ∈ X.dom, P x = 0 := by
  obtain ⟨Y, rfl⟩ := hX
  obtain ⟨N, -, hb⟩ := GlobalTheory.ss_finite_dimensional GlobalTheory.FlagMahler.mahler_compactness Y la
  refine ⟨N, fun P hP h0 x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hb P hP x hx
  have h1 : Y.pnorm la P y = 0 := by simp [Data.pnorm, h0 y hy]
  rw [h1, mul_zero] at hxy
  have h2 : ‖P x‖ * Y.nfac la x ≤ 0 := hxy
  have h3 := flowTermNormDecay.nfac_pos Y.toData la hx
  have h4 : ‖P x‖ ≤ 0 := by
    by_contra h
    push Not at h
    linarith [mul_pos h h3]
  exact norm_le_zero_iff.1 h4

theorem finiteDimensional_of_le_holSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r), (∀ k, ∃ Y : DataX E r, Y.toData = X k) → ∀ W : Submodule ℂ (FDSec X), W ≤ holSub X la → (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  intro E _ _ _ r Comp _ X la hX W hW hoff
  choose N hN using fun k => exists_finset_vanishing (X k) (la k) (hX k)
  let ev : W →ₗ[ℂ] ((Σ k, N k) → ℂ) :=
    { toFun := fun P p => P.1 p.1 p.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  rw [injective_iff_map_eq_zero]
  rintro ⟨P, hP⟩ h0
  refine Subtype.ext (funext fun k => funext fun x => ?_)
  by_cases hx : x ∈ (X k).dom
  · exact hN k (P k) (mem_SS_of_mem_holSub X la (hW hP) k)
      (fun y hy => congrFun h0 ⟨k, y, hy⟩) x hx
  · exact hoff P hP k x hx

end GlobalTheory.CuspSecFin
