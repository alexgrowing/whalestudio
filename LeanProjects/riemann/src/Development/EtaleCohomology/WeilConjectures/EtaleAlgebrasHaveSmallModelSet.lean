import Development.EtaleCohomology.WeilConjectures.AbsorbPf

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.EWeil.AbsorbPf3

theorem etaleAlgebras_have_small_model_set : LateralTheory.EWeil.AbsorbPf.Model := by
  intro A
  refine ⟨Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) A) // (algebraMap A (MvPolynomial (Fin n) A ⧸ I)).Etale},
    fun x => CommRingCat.of (MvPolynomial (Fin x.1) A ⧸ x.2.1),
    fun x => CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin x.1) A ⧸ x.2.1)), fun x => x.2.2, ?_⟩
  intro B g hg
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hg
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let eq : (MvPolynomial (Fin n) A ⧸ RingHom.ker f) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
  haveI : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := Algebra.Etale.of_equiv eq.symm
  have hE : (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)).Etale :=
    (RingHom.etale_algebraMap).mpr inferInstance
  refine ⟨⟨n, RingHom.ker f, hE⟩, (eq.symm.toRingEquiv).toCommRingCatIso, ?_⟩
  ext a
  exact eq.symm.commutes a

end LateralTheory.EWeil.AbsorbPf3
