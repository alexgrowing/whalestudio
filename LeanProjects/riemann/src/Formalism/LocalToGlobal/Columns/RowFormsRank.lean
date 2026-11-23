import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

open Classical in

def GSD.orbFun (d : S.D) (v : S.V) (x : S.D) : S.V := if hx : ∃ g : S.G, g • d = x then S.ρ hx.choose v else 0

variable {S}

theorem GSD.rho_eq_of_fixed {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) {g₁ g₂ : S.G}
    (e : g₁ • d = g₂ • d) : S.ρ g₁ v = S.ρ g₂ v := by
  have h1 : (g₂⁻¹ * g₁) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 : S.ρ g₁ = S.ρ g₂ * S.ρ (g₂⁻¹ * g₁) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h2, Module.End.mul_apply, hv _ h1]

theorem GSD.orbFun_smul {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) (g : S.G) :
    S.orbFun d v (g • d) = S.ρ g v := by
  have hx : ∃ g' : S.G, g' • d = g • d := ⟨g, rfl⟩
  unfold GSD.orbFun
  rw [dif_pos hx]
  exact GSD.rho_eq_of_fixed hv hx.choose_spec

theorem GSD.orbFun_mem {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) : S.orbFun d v ∈ S.EqFun := by
  intro g x
  by_cases hx : ∃ g' : S.G, g' • d = x
  · obtain ⟨g', rfl⟩ := hx
    rw [← mul_smul, GSD.orbFun_smul hv, GSD.orbFun_smul hv, map_mul, Module.End.mul_apply]
  · have hx' : ¬ ∃ g' : S.G, g' • d = g • x := by
      rintro ⟨g', e⟩
      exact hx ⟨g⁻¹ * g', by rw [mul_smul, e, inv_smul_smul]⟩
    unfold GSD.orbFun
    rw [dif_neg hx, dif_neg hx', map_zero]

theorem GSD.finrank_pos_iff (h : S.Ok) :
    0 < finrank K S.EqFun ↔ ∃ (d : S.D) (v : S.V), v ≠ 0 ∧ ∀ g : S.G, g • d = d → S.ρ g v = v := by
  have := S.finiteDimensional_EqFun h
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨φ, hφ⟩
    have : ∃ d, (φ : S.D → S.V) d ≠ 0 := by
      by_contra hc
      exact hφ (Subtype.ext (funext fun d => by
        by_contra hd
        exact hc ⟨d, hd⟩))
    obtain ⟨d, hd⟩ := this
    refine ⟨d, _, hd, fun g hg => ?_⟩
    have := φ.2 g d
    rw [hg] at this
    exact this.symm
  · rintro ⟨d, v, hv0, hv⟩
    refine ⟨⟨S.orbFun d v, GSD.orbFun_mem hv⟩, fun e => hv0 ?_⟩
    have h1 : S.orbFun d v ((1 : S.G) • d) = 0 := congrFun (congrArg Subtype.val e) ((1 : S.G) • d)
    rw [GSD.orbFun_smul hv, map_one] at h1
    exact h1

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def RowsNonzero (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  0 < finrank X.K (MtildeV W Ch sel mu P) ∧ ∀ j, 1 ≤ j → j ≤ R.m → 0 < finrank X.K (MtV W Ch sel mu P j)

end Rows

end Formalism.L2.Col
