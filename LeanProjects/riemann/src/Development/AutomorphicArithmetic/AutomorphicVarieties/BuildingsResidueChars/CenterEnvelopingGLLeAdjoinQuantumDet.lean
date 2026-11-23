import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSubalgebraLeAdjoinRangeProdCAddXComplex

open GroundTheory.Automorphic.HarishChandra in
private theorem qdet_mem_center (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

open GroundTheory.Automorphic.HarishChandra in
private theorem hc_qdet (n : ℕ) (u : ℂ) :
    harishChandraHom (⟨_, qdet_mem_center n (u + ((n : ℂ) - 1) / 2)⟩ : Subalgebra.center ℂ (U n)) =
      ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ) := by
  rw [harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [rhoVec, Pi.neg_apply]
  ring

theorem UpperTheory.center_envelopingGL_le_adjoin_quantumDet :
    ∀ n : ℕ, Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n) ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
  intro n z hz
  open GroundTheory.Automorphic.HarishChandra in
  let A : Subalgebra ℂ (Subalgebra.center ℂ (U n)) :=
    Algebra.adjoin ℂ (Set.range fun u : ℂ => ⟨_, qdet_mem_center n u⟩)
  have hle : MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤
      A.map GroundTheory.Automorphic.HarishChandra.harishChandraHom := by
    refine (UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex n).trans (Algebra.adjoin_le ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, hc_qdet n u⟩
  obtain ⟨a, ha, hae⟩ :=
    hle (GroundTheory.Automorphic.HarishChandra.harishChandraHom_mem_symmetricSubalgebra ⟨z, hz⟩)
  have haz : a = ⟨z, hz⟩ := GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective hae
  have hval : A.map (Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n)).val =
      Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet
        (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [← hval]
  exact ⟨a, ha, by rw [haz]; rfl⟩
