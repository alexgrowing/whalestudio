import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Reduce
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Development
import Formalism.PeriodIntegrals.UJClassMassAlt

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Concrete

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

def latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (g : HA (AF F) σ J) : Set V :=
  {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g}

def ratMat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) : GL (Fin M) E :=
  Classical.choose (Subgroup.mem_map.mp
    (Subgroup.mem_subgroupOf.mp (γ.2 : (γ.1 : HR (AF F) σ J) ∈ HFinIn (AF F) σ J)))

def linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) : V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (Matrix.toLin b b (u : Matrix (Fin M) (Fin M) E))
    (Matrix.toLin b b ((u⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E))
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin_one])

def iotaG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (γ : GamG σ J) : V ≃ₗ[E] V :=
  linOf b (ratMat σ J γ)

end Concrete

theorem coe_gmap {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (u : V ≃ₗ[K] V) (N : Submodule (𝓞 K) V) :
    (gmap u N : Set V) = u '' N := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe]
  rfl

def LatStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ N ∈ genus h L0

def IsomStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ γ : GamG σ (gramOf h b), iotaG σ (gramOf h b) b γ ∈ isom h

def EquivStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)),
      latSet σ (gramOf h b) b L0 ((γ : HA (AF F) σ (gramOf h b)) * g * k) = iotaG σ (gramOf h b) b γ '' latSet σ (gramOf h b) b L0 g

def InjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g g' : HA (AF F) σ (gramOf h b)) (u : V ≃ₗ[E] V), u ∈ isom h →
      u '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g →
      ∃ (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)), g = (γ : HA (AF F) σ (gramOf h b)) * g' * k

def SurjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ N ∈ genus h L0, ∃ g : HA (AF F) σ (gramOf h b), latSet σ (gramOf h b) b L0 g = N

def CardStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b),
      Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g) =
        Nat.card {u : V ≃ₗ[E] V // u ∈ isom h ∧ u '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g}

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∃ (Λ : HA (AF F) σ (gramOf h b) → Submodule (𝓞 E) V) (ι : GamG σ (gramOf h b) → V ≃ₗ[E] V),
      IsDict (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) h L0 Λ ι

theorem uJClassMass_of_dict (hD : Dict) : PI.UJClassMass2.UJClassMass := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig n g hcov hdisj
  obtain ⟨Λ, ι, D⟩ := hD F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  exact sum_eq_mass D n g hcov hdisj

theorem dict_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep) (s4 : SurjStep)
    (s5 : CardStep) : Dict := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  have S1 := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  choose Λ hΛ using S1
  refine ⟨Λ, iotaG σ (gramOf h b) b, ⟨fun g => (hΛ g).2, si F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig,
    ?_, ?_, ?_, ?_⟩⟩
  · intro g γ k
    apply SetLike.coe_injective
    rw [coe_gmap, (hΛ g).1, (hΛ _).1]
    exact s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g γ k
  · intro g g' u hu hgm
    apply s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g g' u hu
    have e := congrArg (fun N : Submodule (𝓞 E) V => (N : Set V)) hgm
    simp only [coe_gmap] at e
    rwa [(hΛ g).1, (hΛ g').1] at e
  · intro N hN
    obtain ⟨g, hg⟩ := s4 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig N hN
    exact ⟨g, SetLike.coe_injective ((hΛ g).1.trans hg)⟩
  · intro g
    rw [s5 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    show _ ∧ _ ↔ _ ∧ _
    rw [← (hΛ g).1, ← coe_gmap]
    exact and_congr Iff.rfl ⟨fun e => SetLike.coe_injective e, fun e => by rw [e]⟩

theorem uJClassMass_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep)
    (s4 : SurjStep) (s5 : CardStep) : PI.UJClassMass2.UJClassMass := by
  exact uJClassMass_of_dict (dict_of s1 si s2 s3 s4 s5)

end PI.UnitaryGroupMassFormula.UJClassMass

end
