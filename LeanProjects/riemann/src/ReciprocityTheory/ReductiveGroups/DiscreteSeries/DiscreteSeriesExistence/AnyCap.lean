import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyAdj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyCapA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem anyCap (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (v : smD ε σ) :
    Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  classical
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨V, hV, hV0, hVK, hc, htop⟩ := cf_datum_of_copies hDS hgap
    (fun V hV hVK => casOnDatum_of_isDS hDS hgap hD hV hVK)

  have hM : ∀ x ∈ genSub (smE ε σ) V, Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) x =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x :=
    fun x hx => capelli_data hgap hσ hD hV hc hVK hV0 hP hcap Y x hx

  obtain ⟨C, hCM, hC⟩ := anyCap_adj hU V (Y + ((n : ℂ) - 1) / 2)
  have hCv : ∀ x ∈ genSub (smE ε σ) V,
      C x = starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x := by
    intro x hx
    have hmem : C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x ∈ genSub (smE ε σ) V :=
      sub_mem (hCM x hx) (Submodule.smul_mem _ _ hx)
    have h0 : inner ℂ (C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x)
        (C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x) = 0 := by
      rw [inner_sub_left, ← hC, hM _ hmem, inner_smul_right, inner_smul_left, starRingEnd_self_apply, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

  rw [← sub_eq_zero]
  have hperp : ((Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) v -
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v : smD ε σ) : H) ∈
      ((genSub (smE ε σ) V).map (smD ε σ).subtype)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
    rw [Submodule.subtype_apply, ← Submodule.coe_inner, inner_sub_right, hC, hCv x hx, inner_smul_left,
      inner_smul_right, starRingEnd_self_apply, sub_self]
  have htop' : ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure = ⊤ := htop
  rw [Submodule.topologicalClosure_eq_top_iff.1 htop'] at hperp
  exact Subtype.ext ((Submodule.mem_bot ℂ).1 hperp)

end ReciprocityTheory.ChartRestriction.DS
