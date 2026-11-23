import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TriComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem linked_iff_torus_conjugate {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g]
  simp [tconj]

private theorem torus_conjugate_corner_entry_eq {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (g : H) : r g 0 0 = r' g 0 0 := by
  rw [h g]
  simp [tconj, wv, wt]

private theorem diagonal_type_corner_cases {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hS : SoV Ω l) (hF : D.Fin0)
    (ξ : M.SS →ₐ[c.O] PadicAlgCl l) (hd : DiagType (M.rep ξ)) :
    (M.rep ξ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr (ξ.comp M.toSS)) ∨
    (M.rep ξ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr (ξ.comp M.toSS)) := by
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ
  obtain ⟨s1, s2, -⟩ := signs D hD M hF ξ
  have hd' : DiagType r := fun i j hij a b => hd i j hij ((linked_iff_torus_conjugate h i j).1 a) ((linked_iff_torus_conjugate h j i).1 b)
  have hs : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  rcases diagCases D hD hS r hr hd' with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s1 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩
  · exact Or.inr ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s2 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.m3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → M3 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF x₁ h1 hn hp _
  obtain ⟨ξ₁, rfl⟩ := ptLift D hD M x₁ h1
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ₁
  obtain ⟨-, -, s3, -, s5⟩ := signs D hD M hF ξ₁
  have n02 : ¬ Ge r 0 2 := fun e => s3 hp ((linked_iff_torus_conjugate h 0 2).1 e)
  have hd : DiagType (M.rep ξ₁) := by
    rcases tri D hD hL r hr with a | a | a
    · obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ r hr
      exact absurd ((geAlg _ r _ p1 p6).2.2.2.2.1.1 a 0 2) n02
    · exact fun i j hij u v => a i j hij ((linked_iff_torus_conjugate h i j).2 u) ((linked_iff_torus_conjugate h j i).2 v)
    · exact absurd a.1 n02
  have hne : ((D.th D.s0 : c.O) : PadicAlgCl l) ≠ ((D.al D.s0 : c.O) : PadicAlgCl l) := fun e => by
    have hinj := (facts D hD).2.2.2.2.2.2.1
    have : (0 : Fin 4) = 2 := hinj (Subtype.ext e)
    exact absurd this (by decide)
  have key : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → Same0 M.gr x (ξ₁.comp M.toSS) →
      (M.rep ξ₁ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr x) ∨
      (M.rep ξ₁ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr x) := by
    intro x hx h0
    obtain ⟨ξ, rfl⟩ := ptLift D hD M x hx
    obtain ⟨q1, q2⟩ := s5 ξ fun b hb => (h0 b hb).symm
    rw [q1]
    exact diagonal_type_corner_cases D hD M hS hF ξ (q2 hd)
  rcases diagonal_type_corner_cases D hD M hS hF ξ₁ hd with ⟨a, -⟩ | ⟨a, -⟩
  · refine Or.inr ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨-, b⟩ | ⟨b, -⟩
    · exact hnn b
    · exact hne (a.symm.trans b)
  · refine Or.inl ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨b, -⟩ | ⟨-, b⟩
    · exact hne (b.symm.trans a)
    · exact hnn b
