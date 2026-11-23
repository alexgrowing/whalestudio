import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSSkeleton

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def Floc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
    [AddCommGroup V] [Module (𝓞 E) V] (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) : Set V :=
  {x | ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ X}

def PatchF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsLattice E L0 →
    (∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) → y ∈ crdOf b L0) →
    ∀ (γ : UJ (σ : E →+* E) J) (T : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ g : HA (AF F) σ J, latSet σ J b L0 g =
        {x | (∀ v ∈ T, x ∈ Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0)) ∧ (∀ v ∉ T, x ∈ Floc v L0)}

def SemiApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    ∀ N ∈ genus h L0, ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ γ : UJ (σ : E →+* E) (gramOf h b), ∀ v ∈ T,
        Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0) = Floc v N

section Cheap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_Floc_self (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) {x : V} (hx : x ∈ X) :
    x ∈ Floc v X :=
  ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem floc_le (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) : Floc v L ⊆ Floc v N := by
  rintro x ⟨s, hs, hsx⟩
  refine ⟨(D : 𝓞 F) * s, fun h => (v.isPrime.mem_or_mem h).elim hD hs, ?_⟩
  rw [map_mul, map_intCast, mul_smul]
  exact hLN _ hsx

theorem flocEq (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) (hNL : ∀ x ∈ N, (D : 𝓞 E) • x ∈ L) :
    Floc v L = Floc v N :=
  Set.Subset.antisymm (floc_le v L N D hD hLN) (floc_le v N L D hD hNL)

omit [NumberField E] in
theorem finF (D : ℤ) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((D : 𝓞 F)) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((D : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD
  apply (Ideal.finite_factors hI).subset
  intro v hv
  show v.asIdeal ∣ Ideal.span {((D : 𝓞 F))}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem interLocStd [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ p : Ideal (𝓞 E), p.IsMaximal → ∃ t : 𝓞 E, t ∉ p ∧ t • x ∈ N) : x ∈ N := by
  classical
  have hfull : PI.LatLocGlob.IsFullLat E N := ⟨hN.fg, hN.span_eq_top⟩
  let N' : Submodule (𝓞 E) V := N ⊔ Submodule.span (𝓞 E) {x}
  have hfull' : PI.LatLocGlob.IsFullLat E N' := by
    refine ⟨hN.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    apply eq_top_iff.2
    rw [← hN.span_eq_top]
    exact Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hloc : ∀ p : Ideal (𝓞 E), p.IsMaximal → PI.LatLocGlob.loc p N' = PI.LatLocGlob.loc p N := by
    intro p hp
    haveI := hp.isPrime
    ext y
    constructor
    · rintro ⟨s, hs, hsy⟩
      obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.1 hsy
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
      obtain ⟨t, ht, htx⟩ := hx p hp
      refine ⟨t * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hs, ?_⟩
      rw [mul_smul, ← haz, smul_add, smul_comm t r x]
      exact N.add_mem (N.smul_mem t ha) (N.smul_mem r htx)
    · rintro ⟨s, hs, hsy⟩
      exact ⟨s, hs, Submodule.mem_sup_left hsy⟩
  obtain ⟨L, _, huniq⟩ := latLocGlob (𝓞 E) E V N hfull (fun p => PI.LatLocGlob.loc p N)
    (fun p _ => ⟨N, hfull, rfl⟩) (Set.finite_empty.subset (fun p hp => hp.2 rfl))
  have e1 : N = L := huniq N ⟨hfull, fun p _ => rfl⟩
  have e2 : N' = L := huniq N' ⟨hfull', hloc⟩
  have : x ∈ N' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  rwa [e2, ← e1] at this

theorem interLocF [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), x ∈ Floc v N) : x ∈ N := by
  apply interLocStd N hN x
  intro p hp
  have hne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hcb : p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 F) a)
  haveI := hp.isPrime
  let v : HeightOneSpectrum (𝓞 F) := ⟨p.comap (algebraMap (𝓞 F) (𝓞 E)), Ideal.comap_isPrime _ _, hcb⟩
  obtain ⟨s, hs, hsx⟩ := hx v
  exact ⟨algebraMap (𝓞 F) (𝓞 E) s, hs, hsx⟩

end Cheap

theorem surjStep_of_F (hP : PatchF) (hS : SemiApprox) (hO : LSOne) : SurjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hL hsig N hN
  classical
  obtain ⟨D, hD0, hDL, hDN⟩ := cofinStep E V L0 N hL hN.1
  set T := (finF (F := F) D hD0).toFinset with hT
  have hTm : ∀ v, v ∉ T → ((D : 𝓞 F)) ∉ v.asIdeal := by
    intro v hv hDv
    exact hv ((Set.Finite.mem_toFinset _).2 hDv)
  obtain ⟨γ, hγ⟩ := hS F E σ V h M b L0 hσ hθ hsymm hnd hL N hN T
  have hsat : ∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) →
      y ∈ crdOf b L0 := by
    intro y hy
    rw [← hO F E σ V h M b L0 hσ hθ hτ hsymm hnd hL hsig]
    show (finMat σ (gramOf h b) (1 : HA (AF F) σ (gramOf h b))⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y) ∈
      latHat F E (crdOf b L0)
    rw [inv_one, finMat_one, Matrix.one_mulVec]
    exact hy
  obtain ⟨g, hg⟩ := hP F E σ V M (gramOf h b) b L0 hL hsat γ T
  refine ⟨g, ?_⟩
  rw [hg]
  ext x
  rw [Set.mem_setOf_eq]
  have hout : ∀ v, v ∉ T → Floc v L0 = Floc v N := fun v hv => flocEq v L0 N D (hTm v hv) hDL hDN
  constructor
  · rintro ⟨h1, h2⟩
    apply interLocF (F := F) N hN.1 x
    intro v
    by_cases hv : v ∈ T
    · rw [← hγ v hv]
      exact h1 v hv
    · rw [← hout v hv]
      exact h2 v hv
  · intro hx
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hγ v hv]
      exact mem_Floc_self v N hx
    · rw [hout v hv]
      exact mem_Floc_self v N hx

end PI.UnitaryGroupMassFormula.UJClassMass

end
