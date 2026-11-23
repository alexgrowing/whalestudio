import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bnd_of {A Fr Γ Γ' : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (t : A) (φ : Γ' → A) (hφ : AdicCont (Ideal.span {t}) φ) (p : Γ → Γ') (hp : Continuous p) :
    BndF t fun g => algebraMap A Fr (φ (p g)) :=
  ⟨0, fun g => φ (p g), fun N => (hφ N).comp_continuous hp, fun g => by simp⟩

theorem UpperTheory.V.Pa.bndRho :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g)) ∧ BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g⁻¹)) ∧ ∀ j, BndM x.t (kapF h k j) := by
  intro l _ L G G0 h n x k
  have hp : Continuous (h.p₀ : G.G₀ → G0.G₀) := by
    apply Continuous.subtype_mk
    exact h.cont.comp continuous_subtype_val
  have hpi : Continuous (fun g : G.G₀ => h.p₀ g⁻¹) := hp.comp continuous_inv
  have hρ : ∀ i j, AdicCont (Ideal.span {x.t}) (fun g : G0.G₀ => (mat x.ρ) g i j) := by
    intro i j
    have := x.cont i j
    rwa [PowerSeries.maximalIdeal_eq_span_X] at this
  refine ⟨fun i j => bnd_of x.t _ (hρ i j) _ hp, fun i j => bnd_of x.t _ (hρ i j) _ hpi, ?_⟩
  intro j i i'
  have hk := ((k.mem j).2.1 i i')
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hk
  exact bnd_of x.t _ hk _ hp
