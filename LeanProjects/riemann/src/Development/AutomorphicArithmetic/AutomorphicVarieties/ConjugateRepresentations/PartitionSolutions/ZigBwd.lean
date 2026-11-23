import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.InclFacts

open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem van_dOm {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (C : I → S → Set V) (F : S → Set V) (hC : ∀ i s, IsOpen (C i s))
    (hF : ∀ s, IsOpen (F s)) {q : ℕ} (k : ℕ) (b : List I → G.Om q) (hb : Van G C F k b) :
    Van G C F k (fun x => G.dOm q (b x)) := by
  intro x hx s p hp hxC
  beta_reduce
  by_cases hY : p ∈ G.Y
  · rw [G.dOm_apply (b x) s hY]
    have hW : IsOpen (F s ∩ ⋂ i ∈ {i | i ∈ x}, C i s) :=
      (hF s).inter ((List.finite_toSet x).isOpen_biInter (fun i _ => hC i s))
    have hev : ((b x : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hW.mem_nhds ⟨hp, Set.mem_iInter₂.mpr hxC⟩] with y hy
      exact hb x hx s y hy.1 (fun i hi => Set.mem_iInter₂.mp hy.2 i hi)
    rw [extDeriv, hev.fderiv_eq, fderiv_const_apply]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  · exact ((G.dOm q (b x)).2 s).2 p hY

theorem UpperTheory.V.Cj.A.zigBwd :
    ZigBwd := by
  intro Γ V S I _ _ _ _ _ d G hY hne φ hφ C F hC hF hφC n c hc hdc hvc q
  obtain ⟨-, -, -, hhom, -, -⟩ := hdFacts
  obtain ⟨hi1, -, hi3⟩ := inclFacts Γ V S d G hY hne
  induction q with
  | zero =>
    intro k hk
    obtain rfl : k = n := by omega
    refine ⟨fun x => G.incl (c x), fun x _ => rfl, fun γ x hx => ?_, fun x _ => hi3.apply_apply_eq_zero _,
      fun x hx => ?_, fun x hx s p _ hp => ?_⟩
    · beta_reduce
      rw [hc γ x hx, hi1]
    · refine (hhom I _ _ G.incl.toAddMonoidHom c x).trans ?_
      rw [hdc x hx, map_zero]
    · by_cases hpY : p ∈ G.Y
      · ext1 v
        rw [G.incl_apply _ _ hpY, hvc x hx s p hp]
        rfl
      · exact ((G.incl (c x)).2 s).2 p hpY
  | succ q ih =>
    intro k hk
    obtain ⟨u, hz, hu, hdu, hhu, hvu⟩ := ih (k + 1) (by omega)
    obtain ⟨b, hb, hhb, hvb⟩ := bwdStep Γ V S I d G φ hφ C F hφC q k u hu hhu hvu
    refine ⟨fun x => G.dOm q (b x), ⟨b, hb, fun _ _ => rfl, ?_⟩, fun γ x hx => ?_,
      fun x _ => (dExact Γ V S d G hY q).apply_apply_eq_zero _, fun x hx => ?_,
      van_dOm G C F hC.isOpen hF k b hvb⟩
    · exact (zigFormal Γ V S I d G).1 q (k + 1) u (hd b) c (fun x hx => (hhb x hx).symm) hz
    · beta_reduce
      rw [hb γ x hx, dEquiv]
    · refine (hhom I _ _ (G.dOm q).toAddMonoidHom b x).trans ?_
      rw [hhb x hx]
      exact hdu x hx
