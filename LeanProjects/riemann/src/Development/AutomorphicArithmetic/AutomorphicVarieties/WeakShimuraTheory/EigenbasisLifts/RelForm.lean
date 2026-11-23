import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Eb

section
variable {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem rf_star_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.star O R n (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp only [W.GFrame.star, W.GFrame.starOp]
  rw [MonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, MonoidAlgebra.smul_single',
    smul_eq_mul]

private noncomputable def rf_dual (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) :
    F.G₀ →* Matrix (Fin n) (Fin n) K where
  toFun g := ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, map_mul, transpose_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

private theorem rf_dual_apply (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) (g : F.G₀) :
    rf_dual F O K n r g = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ := rfl

end

private theorem rf_rep_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (g : G) (b : R) : W.GDet.repAlg ρ R (MonoidAlgebra.single g b) = b • ρ g := by
  simp only [W.GDet.repAlg]
  rw [MonoidAlgebra.lift_single]
  simp

end UpperTheory.V.Ws.Eb

theorem UpperTheory.V.Ws.Eb.relForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [IsLocalRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        ∃ P : GL (Fin n) A, F.IsForm c.O n ρ P := by
  intro l _ F c n r B A _ _ _ f ρ hF hD
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  have hF' : Submodule.span A (Set.range (W.mat ρ)) = ⊤ := hF
  have key : ∀ g : F.G₀, (W.GDet.ofRep (W.mat ρ)).lam 1 (F.star c.O A n (MonoidAlgebra.single g 1)) =
      (W.GDet.ofRep (W.mat ρ)).lam 1 (MonoidAlgebra.single g 1) := by
    intro g
    have h1 := congrArg (f : B.B →+* A) (B.u.P 1 g)
    have hm := (AlgebraTools.Det.mapApi B.u.D (f : B.B →+* A)).2.1 1
    rw [← hm, ← hm] at h1
    have hs := (AlgebraTools.Det.starApi F c.O B.B n).2.2.2.2.2 A f (MonoidAlgebra.single g 1)
    rw [← hs, hD] at h1
    simpa using h1
  have trs : ∀ y, (W.GDet.ofRep (W.mat ρ)).lam 1 y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    intro y
    have h := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn y
    simpa only [W.GDet.tr] using h
  have hsingle : ∀ g, (W.mat ρ g).trace = (rf_dual F c.O A n ρ g).trace := by
    intro g
    have h := key g
    rw [trs, trs, rf_star_single, rf_rep_single, rf_rep_single] at h
    rw [rf_dual_apply, trace_smul, trace_transpose]
    simpa [trace_smul] using h.symm
  have htr : ∀ x, (W.GDet.repAlg (W.mat ρ) A x).trace = (W.GDet.repAlg (rf_dual F c.O A n ρ) A x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, rf_rep_single, one_smul]
      exact hsingle g
    | add x y hx hy => simp only [map_add, trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, trace_smul, hx]
  have hsurj : Function.Surjective (W.GDet.repAlg (W.mat ρ) A) := by
    intro M
    have hM : M ∈ Submodule.span A (Set.range (W.mat ρ)) := by
      rw [hF']
      trivial
    have hle : Submodule.span A (Set.range (W.mat ρ)) ≤ LinearMap.range (W.GDet.repAlg (W.mat ρ) A).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [rf_rep_single]⟩
    obtain ⟨x, hx⟩ := hle hM
    exact ⟨x, by simpa using hx⟩
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConjugacy.exists_conj_of_surjective (W.GDet.repAlg (W.mat ρ) A)
    (W.GDet.repAlg (rf_dual F c.O A n ρ) A) hsurj htr
  refine ⟨⟨(↑U : Matrix (Fin n) (Fin n) A)ᵀ, (↑U⁻¹ : Matrix (Fin n) (Fin n) A)ᵀ, ?_, ?_⟩, fun g => ?_⟩
  · rw [← transpose_mul, Units.inv_mul, transpose_one]
  · rw [← transpose_mul, Units.mul_inv, transpose_one]
  · show (W.mat ρ g)ᵀ * (↑U : Matrix (Fin n) (Fin n) A)ᵀ * W.mat ρ (F.conj g) = _
    have h := congrArg transpose (hU (MonoidAlgebra.single g 1))
    rw [rf_rep_single, rf_rep_single, one_smul, one_smul, rf_dual_apply, transpose_mul, transpose_mul,
      transpose_smul, transpose_transpose] at h
    rw [← h, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]
