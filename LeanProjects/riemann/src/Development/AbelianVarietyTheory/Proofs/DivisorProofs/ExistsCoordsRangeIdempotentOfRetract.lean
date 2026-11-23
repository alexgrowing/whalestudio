import Mathlib
universe u

namespace GlobalTheory

theorem idem_retract_coords : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  intro C _ _ I hI W _ _ m s r hrs p hp
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hrs' : ∀ w, r (s w) = w := fun w => by simpa using LinearMap.congr_fun hrs w
  have hp' : ∀ w, p (p w) = p w := fun w => by simpa [Module.End.mul_apply] using LinearMap.congr_fun hp w
  let q0 : (Fin m → C ⧸ I) →ₗ[C] (Fin m → C ⧸ I) := s ∘ₗ p ∘ₗ r
  let q : (Fin m → C ⧸ I) →ₗ[C ⧸ I] (Fin m → C ⧸ I) :=
    q0.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hq : ∀ x, q x = s (p (r x)) := fun x => rfl
  have hqq : ∀ x, q (q x) = q x := by
    intro x; simp only [hq, hrs', hp']
  let P := LinearMap.range q
  let π : (Fin m → C ⧸ I) →ₗ[C ⧸ I] P :=
    LinearMap.codRestrict P q (fun x => LinearMap.mem_range_self q x)
  have hπι : π ∘ₗ P.subtype = LinearMap.id := by
    ext ⟨x, y, rfl⟩
    simp [π, hqq]
  haveI : Module.Projective (C ⧸ I) P := Module.Projective.of_split P.subtype π hπι
  haveI : Module.Finite (C ⧸ I) P := Module.Finite.of_surjective π (by
    intro y; exact ⟨y, by simpa using LinearMap.congr_fun hπι y⟩)
  haveI : Module.FinitePresentation (C ⧸ I) P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (C ⧸ I) P := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis (C ⧸ I) P
  have mem : ∀ w, s (p w) ∈ P := fun w => ⟨s w, by simp [hq, hrs']⟩
  let f : Fin (Module.finrank (C ⧸ I) P) → W →ₗ[C] C ⧸ I := fun k =>
    { toFun := fun w => β.coord k ⟨s (p w), mem w⟩
      map_add' := by
        intro a c
        rw [← map_add]; congr 1; ext1; simp
      map_smul' := by
        intro c w
        have e : (⟨s (p (c • w)), mem _⟩ : P) = (Ideal.Quotient.mk I c) • ⟨s (p w), mem w⟩ := by
          ext1
          funext i
          simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        show β.coord k ⟨s (p (c • w)), mem _⟩ = _
        rw [e, map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq] }
  have hf : ∀ k w, f k w = β.coord k ⟨s (p w), mem w⟩ := fun _ _ => rfl
  refine ⟨_, fun k => r (β k), f, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := (β k).2
    refine ⟨r x, ?_⟩
    show p (r x) = r ((β k : P) : Fin m → C ⧸ I)
    rw [← hx, hq, hrs']
  · intro k w
    rw [hf, hf]
    congr 1
    ext1
    simp [hp']
  · intro j k
    rw [hf]
    have e : (⟨s (p (r (β k))), mem _⟩ : P) = β k := by
      ext1
      show s (p (r ((β k : P) : Fin m → C ⧸ I))) = ((β k : P) : Fin m → C ⧸ I)
      obtain ⟨x, hx⟩ := (β k).2
      rw [← hq, ← hx, hqq]
    rw [e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  · rintro w ⟨y, rfl⟩ h0
    have e : (⟨s (p (p y)), mem _⟩ : P) = 0 := by
      apply β.forall_coord_eq_zero_iff.mp
      intro k; rw [← hf]; exact h0 k
    have e2 : s (p (p y)) = 0 := congrArg Subtype.val e
    rw [← hrs' (p y), ← hp' y, e2, map_zero]

end GlobalTheory
