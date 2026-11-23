import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

open TensorProduct in
theorem UpperTheory.V.Ws.Pp.extFg :
    ∀ {B C K : Type} [CommRing B] [CommRing C] [Field K] [IsAlgClosed K] [Algebra B C] [Algebra.FiniteType B C] (q : Ideal C) [q.IsPrime] (f : B →+* K), RingHom.ker f = q.comap (algebraMap B C) → ∃ φ : C →+* K, φ.comp (algebraMap B C) = f := by
  intro B C K _ _ _ _ _ _ q _ f hf
  letI : Algebra B K := f.toAlgebra
  let p : Ideal B := q.comap (algebraMap B C)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ {L : Type} [Field L] (g : B →+* L), RingHom.ker g = p →
      ∃ g' : p.ResidueField →+* L, g'.comp (algebraMap B p.ResidueField) = g := by
    intro L _ g hg
    have h2 : p.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid L) := by
      intro x hx
      have : g x ≠ 0 := fun h => hx (by rw [← hg]; exact h)
      exact (isUnit_iff_ne_zero.2 this)
    exact ⟨Ideal.ResidueField.lift p g hg.ge h2,
      RingHom.ext fun x => Ideal.ResidueField.lift_algebraMap p g hg.ge h2 x⟩
  obtain ⟨a, ha⟩ := hunit f hf
  obtain ⟨b, hb⟩ := hunit ((algebraMap C q.ResidueField).comp (algebraMap B C)) (by
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField])
  haveI hnt : Nontrivial (K ⊗[B] C) := by
    letI : Algebra p.ResidueField K := a.toAlgebra
    letI : Algebra p.ResidueField q.ResidueField := b.toAlgebra
    haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq' ha.symm
    let T := K ⊗[p.ResidueField] q.ResidueField
    haveI : Nontrivial T := inferInstance
    let u : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft : K →ₐ[B] T)
    let v : C →ₐ[B] T :=
      { toRingHom := ((Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) : q.ResidueField →+* T).comp (algebraMap C q.ResidueField)
        commutes' := fun x => by
          have h1 : algebraMap C q.ResidueField (algebraMap B C x) =
              algebraMap p.ResidueField q.ResidueField (algebraMap B p.ResidueField x) :=
            (RingHom.congr_fun hb x).symm
          show (Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) (algebraMap C q.ResidueField (algebraMap B C x)) = _
          rw [h1, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
    exact (Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)).toRingHom.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] C)
  letI : Field ((K ⊗[B] C) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K ((K ⊗[B] C) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have hbij : Function.Bijective (algebraMap K ((K ⊗[B] C) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : ((K ⊗[B] C) ⧸ m) →ₐ[K] K := (AlgEquiv.ofBijective (Algebra.ofId K _) hbij).symm.toAlgHom
  let χ : (K ⊗[B] C) →ₐ[K] K := ψ.comp (Ideal.Quotient.mkₐ K m)
  refine ⟨(χ : K ⊗[B] C →+* K).comp ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) : C →+* K ⊗[B] C), ?_⟩
  ext x
  show χ ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) (algebraMap B C x)) = f x
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B K (K ⊗[B] C), AlgHom.commutes]
  rfl
