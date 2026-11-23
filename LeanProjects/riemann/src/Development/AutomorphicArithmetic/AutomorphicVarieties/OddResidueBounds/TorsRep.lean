import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.torsRep :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)), (l : ℤ_[l]) • x = 0 → ∃ z : Z1 (qzTw D e), x = Submodule.Quotient.mk z ∧ ∀ g, (l : ℤ_[l]) • z.1 g = 0 := by
  intro E Ω _ _ _ _ _ l hl D e x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := Submodule.mem_comap.1 hx
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  obtain ⟨m', hm'⟩ := (UpperTheory.V.Kum.qzBasic l).1 (l : ℤ_[l]) hl0 m
  have hb : d0 (qzTw D e) m' ∈ B1 (qzTw D e) := ⟨m', rfl⟩
  refine ⟨z - ⟨d0 (qzTw D e) m', coboundaries_le_cocycles _ (UpperTheory.V.LDataCardLeFinrank.contTw E Ω l D e).1 hb⟩, ?_, fun g => ?_⟩
  · rw [Submodule.Quotient.eq, sub_sub_cancel]
    exact Submodule.mem_comap.2 hb
  · have h1 : (l : ℤ_[l]) • d0 (qzTw D e) m' = (l : ℤ_[l]) • z.1 := by
      rw [← map_smul]
      exact (congrArg _ hm').trans hm
    have h2 := congrFun h1 g
    show (l : ℤ_[l]) • (z.1 g - d0 (qzTw D e) m' g) = 0
    rw [smul_sub]
    exact sub_eq_zero.2 h2.symm
