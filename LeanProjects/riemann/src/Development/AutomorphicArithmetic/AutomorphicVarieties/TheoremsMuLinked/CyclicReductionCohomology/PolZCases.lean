import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c, (Int.units_eq_one_or (F.η γ)).resolve_left h]
  simp

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  have := g.2
  rw [MonoidHom.mem_ker] at this ⊢
  rw [map_mul, F.η_c, this]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  classical
  refine ⟨fun γ => ⟨if γ ∈ F.η.ker then γ else γ * F.c, ?_⟩, ?_, ?_, ?_⟩
  · split_ifs with h
    · exact h
    · exact polZ_mem F h
  · refine Continuous.subtype_mk ?_ _
    refine Continuous.if ?_ continuous_id (continuous_id.mul continuous_const)
    have hc : IsClopen (F.η.ker : Set F.Γ) := ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
    intro a ha
    have : frontier {x | x ∈ F.η.ker} = ∅ := hc.frontier_eq
    rw [this] at ha
    exact ha.elim
  · intro g
    exact Subtype.ext (if_pos g.2)
  · intro g
    refine Subtype.ext ((if_neg (polZ_nmem F g)).trans ?_)
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_cases {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, polZ_mem F h⟩, ?_⟩
    show γ = γ * F.c * F.c
    rw [mul_assoc, F.c_sq, mul_one]

private theorem polZ_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) :
    (F.conj g : F.Γ) = F.c * g * F.c := by
  show F.c * g * F.c⁻¹ = _
  rw [inv_eq_of_mul_eq_one_right F.c_sq]

private theorem polZ_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (rep : Representation A F.Γ M) (Z : F.G₀ → M) (hl : IsLocallyConstant Z)
    (hm : ∀ g h, Z (g * h) = Z g + rep g (Z h)) (hc : ∀ g, Z (F.conj g) = rep F.c (Z g)) :
    ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = Z g := by
  obtain ⟨p, pc, p1, p2⟩ := polZ_proj F
  have h1 : Z 1 = 0 := by
    have := hm 1 1
    simpa using this
  have cc : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, F.c_sq, mul_one]
  refine ⟨Z ∘ p, ⟨hl.comp_continuous pc, fun a b => ?_⟩, ?_, fun g => by simp [p1]⟩
  · simp only [Function.comp]
    rcases polZ_cases F a with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;> rcases polZ_cases F b with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul, p1, p1, p1, hm]
    · rw [← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, hm]
    · have : (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c := by
        rw [Subgroup.coe_mul, polZ_conj, ← mul_assoc, ← mul_assoc, cc]
      rw [this, p2, p2, p1, hm, hc, map_mul]
      rfl
    · have : (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) := by
        rw [Subgroup.coe_mul, polZ_conj]
        simp only [mul_assoc]
      rw [this, p2, p2, p1, hm, hc, map_mul]
      rfl
  · have := p2 1
    rw [OneMemClass.coe_one, one_mul] at this
    simp [this, h1]

theorem UpperTheory.V.Th.polP :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (rep : Representation A F.Γ (Matrix (Fin n) (Fin n) R)), IsUnit P → IsAdP F ρ P χ rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, IsLocallyConstant z → (∀ g g', z (g * g') = z g + χ g • (ρ g * z g' * ρ g⁻¹)) → (∀ g, P * z (F.conj g) = -(χ F.c • ((z g)ᵀ * P))) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, y g = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, P * y (F.conj g) = -(χ F.c • ((y g)ᵀ * P))) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ P χ rep hP ⟨a1, a2⟩
  refine ⟨fun z hl hm hc => ?_, fun y ⟨_, hy⟩ hc => ⟨fun g => ?_, fun h0 => ?_⟩⟩
  · exact polZ_ext F rep z hl (fun g h => by rw [a1]; exact hm g h)
      (fun g => hP.mul_left_cancel (by rw [a2]; exact hc g))
  · rw [← a2, polZ_conj, hy, hc, map_zero, add_zero, hy, hc, zero_add]
  · funext γ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact h0 g
    · rw [hy, h0, hc, map_zero, add_zero]
      rfl
