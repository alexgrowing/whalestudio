import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem choice_col {R : Type} [CommRing R] (I : Ideal R) (X u : M4 R) (d : Fin 4 → R) (t : R)
    (hX : Cg I X (Matrix.diagonal d)) (hu : IsGSp 1 u) (hUp : IsUp (adj u * X * u))
    (ht : (adj u * X * u : M4 R) 0 0 - t ∈ I) (h2 : IsUnit (u 2 0)) : d 2 - t ∈ I := by
  set Y := adj u * X * u with hYdef
  have hY : u * Y = X * u := by
    rw [hYdef, ← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]
  have e1 : (X * u) 2 0 = u 2 0 * Y 0 0 := by
    rw [← hY, Matrix.mul_apply, Fin.sum_univ_four, hUp 1 0 (by decide), hUp 2 0 (by decide),
      hUp 3 0 (by decide)]
    ring
  have e2 : (X * u) 2 0 - d 2 * u 2 0 ∈ I := by
    have h : (X * u) 2 0 - d 2 * u 2 0 = ∑ k, (X 2 k - Matrix.diagonal d 2 k) * u k 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
      ring
    rw [h]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hX 2 k)
  have e3 : u 2 0 * (d 2 - t) ∈ I := by
    have h : u 2 0 * (d 2 - t) = -((X * u) 2 0 - d 2 * u 2 0) + u 2 0 * (Y 0 0 - t) := by
      rw [e1]
      ring
    rw [h]
    exact I.add_mem (I.neg_mem_iff.mpr e2) (I.mul_mem_left _ ht)
  have h4 : d 2 - t = (h2.unit⁻¹ : Rˣ) * (u 2 0 * (d 2 - t)) := by
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [h4]
  exact I.mul_mem_left _ e3

theorem UpperTheory.V.Ws.Lab.choice :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u →
      ∃ pr, LabOk D pr ∧ IsUnit ((adj (wM 𝔞.V pr) * u : M4 𝔞.V) 0 0) := by
  intro Ω _ _ _ l _ c D hD 𝔞 r u hK
  obtain ⟨hs, hsep⟩ := sg_sep hD 𝔞 false
  obtain ⟨-, -, -, -, -, hrev, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hredg : ∀ g, Cg (maximalIdeal 𝔞.V) (r g)
      (Matrix.diagonal fun i => 𝔞.a c ((D.ps i g : (c.O)ˣ) : c.O)) := by
    intro g i j
    have h := hK.red g i j
    convert h using 3
    simp only [Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hsep' : ∀ i j, lamW i ≠ lamW j →
      IsUnit (𝔞.a c ((D.ps i (D.sg l) : (c.O)ˣ) : c.O) - 𝔞.a c ((D.ps j (D.sg l) : (c.O)ˣ) : c.O)) := by
    intro i j h
    simpa [chi, UpperTheory.V.Ws.lab] using hsep i j h
  obtain ⟨-, -, hor, -⟩ := Lab.resFlag 𝔞.V (r (D.sg l)) u _ _ (hredg _) hK.sp (hK.flag _ hs)
    (hK.char _ hs) hsep'
  rcases hor with h0 | h2
  · refine ⟨false, fun h => absurd h (by decide), ?_⟩
    rw [wM_false_mul]
    exact h0
  · refine ⟨true, fun _ s hs' => ?_, ?_⟩
    · have hc := choice_col (maximalIdeal 𝔞.V) (r s) u (fun i => 𝔞.a c ((D.ps i s : (c.O)ˣ) : c.O))
        (𝔞.a c ((D.ps 0 s : (c.O)ˣ) : c.O)) (hredg s) hK.sp (hK.flag s hs') (hK.char s hs' 0) h2
      have hres : residue c.O ((D.ps 2 s : (c.O)ˣ) : c.O) = residue c.O ((D.ps 0 s : (c.O)ˣ) : c.O) := by
        by_contra hne
        exact (mem_maximalIdeal _).mp hc (𝔞.unit_sub hne)
      have hth : D.th s = D.Psi s * D.al s := by
        have h := congrArg (fun χ => χ s) (hrev 1)
        simpa [Raw.ps] using h.symm
      have hx : residue c.O ((D.al s : (c.O)ˣ) : c.O) ≠ 0 :=
        ((D.al s).isUnit.map (residue c.O)).ne_zero
      simp only [Raw.ps] at hres
      change residue c.O ((D.Psi s : (c.O)ˣ) : c.O) = 1
      apply mul_right_cancel₀ hx
      rw [one_mul, ← map_mul, ← Units.val_mul, ← hth]
      simpa using hres.symm
    · rw [wM_true_mul]
      exact h2
