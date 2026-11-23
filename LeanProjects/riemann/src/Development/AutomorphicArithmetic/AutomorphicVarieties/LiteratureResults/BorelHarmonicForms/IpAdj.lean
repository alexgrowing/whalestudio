import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipAdj :
    UpperTheory.V.Lit.Bor.IpAdj := by
  intro E _ _ _ a n e M _ _ _ _ L L' H N hadj q ω η hω hη
  have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) =
      ip e H (del L' e ω) η := fun i => by
    rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [del_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
        i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
      funext k
      refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
    have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
    rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, ← hadj _ _ (hω _) _ (hη _),
      map_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← mul_pow]
    simp
  have h0 : ip e H ω (dCo L η) = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) := by
    rw [Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [dCo_apply, map_sum]
  rw [h0, Finset.sum_congr rfl fun i _ => key i]
  simp
