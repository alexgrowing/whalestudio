import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem polZ_mem {l : ℕ} [Fact l.Prime] (F : GFrame l) {γ : F.Γ} (h : γ ∉ F.η.ker) : γ * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at h ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η γ) with h1 | h1
  · exact absurd h1 h
  · rw [h1]
    decide

private theorem polZ_nmem {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : (g : F.Γ) * F.c ∉ F.η.ker := by
  rw [MonoidHom.mem_ker, map_mul, MonoidHom.mem_ker.mp g.2, F.η_c, one_mul]
  decide

private theorem polZ_proj {l : ℕ} [Fact l.Prime] (F : GFrame l) :
    ∃ p : F.Γ → F.G₀, Continuous p ∧ (∀ g : F.G₀, p g = g) ∧ ∀ g : F.G₀, p (g * F.c) = g := by
  have hK : IsClopen (F.η.ker : Set F.Γ) :=
    ⟨Subgroup.isClosed_of_isOpen _ F.η_open, F.η_open⟩
  have hfr : frontier {a : F.Γ | a ∈ F.η.ker} = ∅ := hK.frontier_eq
  have hf : Continuous fun γ : F.Γ => if γ ∈ F.η.ker then (1 : F.Γ) else F.c := by
    refine continuous_if ?_ continuousOn_const continuousOn_const
    intro a ha
    rw [hfr] at ha
    exact ha.elim
  refine ⟨fun γ => ⟨γ * (if γ ∈ F.η.ker then 1 else F.c), by
    split_ifs with hγ
    · simpa using hγ
    · exact polZ_mem F hγ⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_id.mul hf) _
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * (if (g : F.Γ) ∈ F.η.ker then 1 else F.c) = g
    rw [if_pos g.2, mul_one]
  · intro g
    apply Subtype.ext
    show (g : F.Γ) * F.c * (if (g : F.Γ) * F.c ∈ F.η.ker then 1 else F.c) = g
    rw [if_neg (polZ_nmem F g), mul_assoc, F.c_sq, mul_one]

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
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := polZ_proj F
  have hZ1 : Z 1 = 0 := by
    have h1 := hm 1 1
    simpa using h1
  have hpc : p F.c = 1 := by
    have h2 := hp2 1
    simpa using h2
  have hmem : (fun γ => Z (p γ)) ∈ Zl rep := by
    show IsLocallyConstant (fun γ => Z (p γ)) ∧
      ∀ g h : F.Γ, Z (p (g * h)) = Z (p g) + rep g (Z (p h))
    refine ⟨hl.comp_continuous hp, ?_⟩
    intro γ δ
    rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
      rcases polZ_cases F δ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [← Subgroup.coe_mul]
      simp only [hp1]
      exact hm g h
    · rw [show (g : F.Γ) * (h * F.c) = ((g * h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, mul_assoc]]
      simp only [hp1, hp2]
      exact hm g h
    · rw [show (g : F.Γ) * F.c * h = ((g * F.conj h : F.G₀) : F.Γ) * F.c by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc, F.c_sq, mul_one]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
    · rw [show (g : F.Γ) * F.c * (h * F.c) = ((g * F.conj h : F.G₀) : F.Γ) by
        simp only [Subgroup.coe_mul, polZ_conj, mul_assoc]]
      simp only [hp1, hp2]
      rw [hm, hc, map_mul, Module.End.mul_apply]
  refine ⟨fun γ => Z (p γ), hmem, ?_, fun g => ?_⟩
  · show Z (p F.c) = 0
    rw [hpc, hZ1]
  · show Z (p g) = Z g
    rw [hp1]

theorem UpperTheory.V.Pa.polZ :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (rep : Representation A F.Γ V), IsAd F ρ χ V rep → (∀ z : F.G₀ → Matrix (Fin n) (Fin n) R, (∀ g, z g ∈ V) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹)) → (∀ g, z (F.conj g) = -(χ F.c • (z g)ᵀ)) → ∃ y ∈ Zl rep, y F.c = 0 ∧ ∀ g : F.G₀, (y g : Matrix (Fin n) (Fin n) R) = z g) ∧ (∀ y ∈ Zl rep, y F.c = 0 → (∀ g : F.G₀, (y (F.conj g) : Matrix (Fin n) (Fin n) R) = -(χ F.c • (y g : Matrix (Fin n) (Fin n) R)ᵀ)) ∧ ((∀ g : F.G₀, y g = 0) → y = 0)) := by
  intro l _ F A R _ _ _ n ρ χ V rep hAd
  obtain ⟨hA1, hA2⟩ := hAd
  refine ⟨fun z hz hzl hzm hzc => ?_, fun y hy hyc => ?_⟩
  · obtain ⟨y, hy, hyc, hyg⟩ := polZ_ext F rep (fun g => (⟨z g, hz g⟩ : V))
      (IsLocallyConstant.desc _ Subtype.val hzl Subtype.val_injective)
      (fun g h => Subtype.ext (by simp only [Submodule.coe_add, hA1]; exact hzm g h))
      (fun g => Subtype.ext (by rw [hA2]; exact hzc g))
    exact ⟨y, hy, hyc, fun g => by rw [hyg g]⟩
  · obtain ⟨-, hyc'⟩ := hy
    refine ⟨fun g => ?_, fun h0 => ?_⟩
    · rw [polZ_conj, hyc', hyc', hyc, map_zero, add_zero, zero_add, hA2]
    · funext γ
      rcases polZ_cases F γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · exact h0 g
      · rw [Pi.zero_apply, hyc', h0 g, hyc, map_zero, add_zero]
