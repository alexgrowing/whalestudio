import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompClosed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem hEl_map' (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Matrix.add_apply, Matrix.smul_apply]

private theorem mult_iff' (f : R →ₐ[c.O] R') (r : Lift c.O D.rbar R) :
    D.Mult (r.map f).hom ↔ ∀ g i j,
      f ((adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) = 0 := by
  refine forall_congr' fun g => ?_
  rw [← f.commutes]
  exact UpperTheory.V.Ws.Po.gsp_iff (f : R →+* R') _ (r.hom g)

end

theorem UpperTheory.V.Ws.Po.ptClosed :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Cond.IsClosed (rbar := D.rbar) fun _ _ _ _ ρ => D.IsPt ρ := by
  intro hP Ω _ _ _ l _ c D hD
  have hL : Cond.IsClosed (rbar := D.rbarAt l) fun _ _ _ _ r => OnComp D.condL (D.r0At l) r := by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compL D hD hP.loc
    exact onCompClosed _ _ _ _ _ _ (closedL D) U ρ hrep J hJ
  have hQ : ∀ p ∈ D.Sb,
      Cond.IsClosed (rbar := D.rbarAt p) fun _ _ _ _ r => OnComp (D.condP p) (D.r0At p) r := fun p hp => by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compP D hD hP.loc p hp
    exact onCompClosed _ _ _ _ _ _ (closedP D p) U ρ hrep J hJ
  refine closed_of_set _ fun R _ _ _ r => ?_
  obtain ⟨IL, hIL⟩ := hL R (D.loc r l)
  choose IP hIP using fun p hp => hQ p hp R (D.loc r p)
  refine ⟨{x | (∃ g i j, x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) ∨
    (∃ A : ValuationSubring Ω, Raw.Away D.T A ∧ ∃ g ∈ Ine (F := ℚ) A, D.rbar g = 1 ∧ ∃ i j, x = (r.hom g - 1) i j) ∨
    (∃ i j, lamW i ≠ lamW j ∧ x = r.hom D.ph i j) ∨ x = D.hEl r.hom 0 2 ∨ x = D.hEl r.hom 2 0 ∨
    x ∈ IL ∨ ∃ p, ∃ hp : p ∈ D.Sb, x ∈ IP p hp}, fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨g, i, j, rfl⟩ | ⟨A, hA, g, hg, hg1, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl | rfl | hx | ⟨p, hp, hx⟩ := hx
    · exact (mult_iff' D f r).1 h.mult g i j
    · exact (one_iff (f : R →+* R') (r.hom g)).1 (h.unr A hA g hg hg1) i j
    · exact h.nrm.1 i j hij
    · rw [← hEl_map']; exact h.nrm.2.1
    · rw [← hEl_map']; exact h.nrm.2.2
    · exact (hIL R' f).1 h.atL x hx
    · exact (hIP p hp R' f).1 (h.atP p hp) x hx
  · refine ⟨(mult_iff' D f r).2 fun g i j => h _ (.inl ⟨g, i, j, rfl⟩),
      fun A hA g hg hg1 => (one_iff (f : R →+* R') (r.hom g)).2 fun i j =>
        h _ (.inr (.inl ⟨A, hA, g, hg, hg1, i, j, rfl⟩)),
      ⟨fun i j hij => h _ (.inr (.inr (.inl ⟨i, j, hij, rfl⟩))), ?_, ?_⟩,
      (hIL R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inl hx)))))),
      fun p hp => (hIP p hp R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inr ⟨p, hp, hx⟩))))))⟩
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inl rfl))))
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inr (.inl rfl)))))
