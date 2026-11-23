import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteFieldEnoughRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem gEx_rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

private theorem gEx_rt_add {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) (w w' : ℤ × ℤ) :
    Φ.rt (w + w') g = Φ.rt w g * Φ.rt w' g := by
  simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_add, Prod.snd_add, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

private theorem gEx_rt_zero {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) : Φ.rt 0 g = 1 := by
  simp [Fr.rt]

private theorem gEx_abs {O Γ Δ k : Type} [CommRing O] [Group Γ] [Group Δ] [Field k] [Finite k] (Φ : Fr O Γ)
    (h : ∀ g, Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (a : O →+* k) (φ : Δ →* Γ) (ω : Γ →* Oˣ)
    (hω : ∀ w, ∃ g, a (Φ.rt w (φ g)) ≠ a (ω (φ g))) :
    ∃ g, (∀ i j, a (Φ.χ i (φ g)) = a (Φ.χ j (φ g))) ∧ a (ω (φ g)) ≠ 1 := by
  classical
  let κ : Fin 4 → Δ →* kˣ := fun i => (Units.map a.toMonoidHom).comp ((Φ.χ i).comp φ)
  let ω' : Δ →* kˣ := (Units.map a.toMonoidHom).comp (ω.comp φ)
  have hmain : ω' ∉ Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) := by
    intro hmem
    let S : Subgroup (Δ →* kˣ) :=
      { carrier := {ψ | ∃ w : ℤ × ℤ, ∀ g, ψ g = Units.map a.toMonoidHom (Φ.rt w (φ g))}
        mul_mem' := by
          rintro ψ₁ ψ₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
          exact ⟨w₁ + w₂, fun g => by simp [h₁, h₂, gEx_rt_add]⟩
        one_mem' := ⟨0, fun g => by simp [gEx_rt_zero]⟩
        inv_mem' := by
          rintro ψ ⟨w, hw⟩
          refine ⟨-w, fun g => ?_⟩
          have hinv : Φ.rt (-w) (φ g) = (Φ.rt w (φ g))⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← gEx_rt_add]
            simp [gEx_rt_zero]
          simp [hw, hinv] }
    have hle : Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨p, q⟩, rfl⟩
      refine ⟨wt p q, fun g => ?_⟩
      have hpq := gEx_rt_wt Φ (φ g) (h _) p q
      simp only [κ, MonoidHom.div_apply, MonoidHom.comp_apply, ← hpq, map_mul]
      exact mul_div_cancel_right _ _
    obtain ⟨w, hw⟩ := hle hmem
    obtain ⟨g, hg⟩ := hω w
    apply hg
    have := congrArg Units.val (hw g)
    simpa [ω'] using this.symm
  obtain ⟨g, hg1, hg2⟩ := (Loc.v0e κ ω').2 hmain
  refine ⟨g, fun i j => ?_, ?_⟩
  · have := congrArg Units.val (hg1 i j)
    simpa [κ] using this
  · intro h1
    apply hg2
    ext
    simpa [ω'] using h1

theorem UpperTheory.V.Ws.Lk.gEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), T.Ok → ∃ g : G T.L Ω, (∀ i j, Raw.bar (chi D T.pr i) (resQ T.L g) = Raw.bar (chi D T.pr j) (resQ T.L g)) ∧ Raw.bar D.om (resQ T.L g) ≠ 1 := by
  intro Ω _ _ _ l _ c D T hT
  haveI := c.dvr
  haveI := c.fin
  haveI : Finite (ResidueField c.O) :=
    IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
  have hrel : ∀ x, (T.fr ∅).χ 0 x * (T.fr ∅).χ 3 x = (T.fr ∅).χ 1 x * (T.fr ∅).χ 2 x := by
    intro x
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have hω : ∀ w, ∃ g, residue c.O ((T.fr ∅).rt w (resLe T.F_le g) : c.O) ≠
      residue c.O ((D.om.comp (resQ T.F)) (resLe T.F_le g) : c.O) := by
    intro w
    obtain ⟨g, hgL, hg⟩ := hT.g2 w
    obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
    exact ⟨g', hg⟩
  obtain ⟨g, hg1, hg2⟩ :=
    gEx_abs (T.fr ∅) hrel (residue c.O) (resLe T.F_le) (D.om.comp (resQ T.F)) hω
  exact ⟨g, fun i j => hg1 i j, hg2⟩
