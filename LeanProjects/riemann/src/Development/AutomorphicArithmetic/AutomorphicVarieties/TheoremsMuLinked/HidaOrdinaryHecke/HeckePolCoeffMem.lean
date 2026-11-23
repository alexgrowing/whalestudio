import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.frobS :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ →
    ∀ (i : ℕ) (g : H.Gq) (N : ℕ), ∃ s ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), D.lam i (MonoidAlgebra.single g 1) - s ∈ I ^ N := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ a K _ I D ψ hU i g N
  have hlc := hU.cont i N
  obtain ⟨x, ⟨w, hw, B, σ, hB, hσ, rfl⟩, hxU⟩ :=
    hAx.dense.exists_mem_open (hlc.isOpen_fiber _) ⟨g, Set.mem_singleton _⟩
  refine ⟨D.lam i (MonoidAlgebra.single (H.prj σ⁻¹) 1), ?_, ?_⟩
  · have hf := hU.frob ⟨w, hw⟩ B σ hB hσ
    set_option synthInstance.maxHeartbeats 400000 in
    generalize hR : Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)) = R
    have hgen : ∀ j, H.genW θ a K ⟨w, hw⟩ j ∈ R := by
      intro j
      subst hR
      unfold UpperTheory.V.Hi.HSet.genW
      split_ifs with h
      · exact Algebra.subset_adjoin ⟨(⟨w, hw⟩, _), rfl⟩
      · exact Subalgebra.one_mem _
    show (-1) ^ i * (D.chi _).coeff (n - i) ∈ R
    rw [hf]
    refine R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) ?_
    unfold UpperTheory.V.Hi.heckePol
    rw [Polynomial.finset_sum_coeff]
    refine R.sum_mem fun j _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact R.mul_mem (R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _)
        (R.pow_mem (R.natCast_mem _) _)) (hgen j)
    · exact R.zero_mem
  · have h1 := Set.mem_singleton_iff.mp hxU
    exact Ideal.Quotient.eq.mp h1.symm
