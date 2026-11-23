import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add, map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
