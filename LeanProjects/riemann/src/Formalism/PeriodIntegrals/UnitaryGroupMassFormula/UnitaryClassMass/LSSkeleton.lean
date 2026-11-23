import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LSLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ Submodule.IsLattice E N

def LSOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) 1 = crdOf b L0

def LSLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (p : Ideal (𝓞 E)), p.IsMaximal →
      ∃ γ : GamG σ (gramOf h b), ∀ x : Fin M → E,
        (∃ s ∈ hcompl (K := E) p, (algebraMap (𝓞 E) E s) • x ∈
            PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g) ↔
        (∃ s ∈ hcompl (K := E) p, (algebraMap (𝓞 E) E s) • x ∈
            PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (γ : HA (AF F) σ (gramOf h b)))

section Glue

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem equivFun_osmul {M : ℕ} (b : Module.Basis (Fin M) E V) (s : 𝓞 E) (v : V) :
    b.equivFun (s • v) = (algebraMap (𝓞 E) E s) • b.equivFun v := by
  rw [← algebraMap_smul E s v, LinearEquiv.map_smul]

theorem mem_iff_crdOf {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (v : V) :
    v ∈ L0 ↔ b.equivFun v ∈ crdOf b L0 := by
  unfold crdOf
  show v ∈ L0 ↔ ∑ i, b.equivFun v i • b i ∈ L0
  rw [b.sum_equivFun]

end Glue

theorem latStep_of_parts (s1 : LSLat) (s2 : LSOne) (s3 : LSLoc) : LatStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g
  obtain ⟨N, hN, hNL⟩ := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g
  refine ⟨N, hN, hNL, fun p hp => ?_⟩
  obtain ⟨γ, hγ⟩ := s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g p hp
  refine ⟨iotaG σ (gramOf h b) b γ, isomStep F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig γ, ?_⟩
  set ι := iotaG σ (gramOf h b) b γ with hι
  have hE := equivStep F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig 1 γ 1
  rw [mul_one, OneMemClass.coe_one, mul_one] at hE
  have h1 : latSet σ (gramOf h b) b L0 1 = (L0 : Set V) := by
    ext v
    show b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) 1 ↔ v ∈ L0
    rw [s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig, mem_iff_crdOf b L0]
  rw [h1] at hE
  have hcomm : ∀ (s : 𝓞 E) (w : V), ι (s • w) = s • ι w := fun s w => by
    rw [← algebraMap_smul E s w, LinearEquiv.map_smul, algebraMap_smul]
  ext v
  have key : (∃ s ∈ hcompl (K := E) p, s • v ∈ N) ↔ (∃ s ∈ hcompl (K := E) p, s • v ∈ ι '' (L0 : Set V)) := by
    rw [← hE]
    have := hγ (b.equivFun v)
    simp only [← equivFun_osmul] at this
    constructor
    · rintro ⟨s, hs, hv⟩
      have hv' : s • v ∈ (N : Set V) := hv
      rw [hN] at hv'
      obtain ⟨t, ht, htv⟩ := this.1 ⟨s, hs, hv'⟩
      exact ⟨t, ht, htv⟩
    · rintro ⟨s, hs, hv⟩
      obtain ⟨t, ht, htv⟩ := this.2 ⟨s, hs, hv⟩
      refine ⟨t, ht, ?_⟩
      show t • v ∈ (N : Set V)
      rw [hN]; exact htv
  show v ∈ ((locS (hcompl (K := E) p) L0).map ((ι : V →ₗ[E] V).restrictScalars (𝓞 E))) ↔
    v ∈ locS (hcompl (K := E) p) N
  rw [Submodule.mem_map]
  change (∃ w, (∃ s ∈ hcompl (K := E) p, s • w ∈ L0) ∧ ι w = v) ↔ ∃ s ∈ hcompl (K := E) p, s • v ∈ N
  rw [key]
  constructor
  · rintro ⟨w, ⟨s, hs, hw⟩, rfl⟩
    exact ⟨s, hs, s • w, hw, hcomm s w⟩
  · rintro ⟨s, hs, l, hl, hlv⟩
    refine ⟨ι.symm v, ⟨s, hs, ?_⟩, ι.apply_symm_apply v⟩
    have e : s • ι.symm v = l := by
      apply ι.injective
      rw [hcomm, ι.apply_symm_apply, hlv]
    rw [e]; exact hl

end PI.UnitaryGroupMassFormula.UJClassMass
