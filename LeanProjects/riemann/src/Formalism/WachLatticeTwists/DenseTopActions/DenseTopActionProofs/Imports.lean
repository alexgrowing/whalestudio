import Formalism.WachLatticeTwists.DenseTopActions.DenseTopActionProofs.OneAddPowSubOne

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem free : StatFree := by
  classical
  intro O A _ _ _ S ι pr D _ _ _ _ W As _ jS κ _ e r₀ r c eq hE hmem hspan hind

  have key : ∀ (cc : Fin r → As) (i : ι),
      (∑ k, jS (cc k) • (fun i => e (eq.symm k).1 • c i (eq.symm k).2 : ι → D)) i
        = ∑ m, (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) i • c i m := by
    intro cc i
    rw [← Equiv.sum_comp eq, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_smul]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro k i
    exact (W.N i).smul_of_tower_mem _ (hmem i _)
  · intro x hx
    choose a ha using fun i => hspan i (x i) (hx i)
    choose d hd _ using fun m => hE (fun i => a i m)
    refine ⟨fun k => d (eq.symm k).2 (eq.symm k).1, ?_⟩
    funext i
    rw [key, ha i]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    have := congrFun (hd m) i
    simpa using this
  · intro cc hcc
    have h1 : ∀ m, (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) = 0 := by
      intro m
      funext i
      have := hind i (fun m => (∑ k, jS (cc (eq (k, m))) * (fun _ => algebraMap O A (e k)) : ι → A) i)
        (by rw [← key, hcc]; rfl)
      exact congrFun this m
    funext k'
    obtain ⟨d, _, hd⟩ := hE 0
    have e1 := hd (fun k => cc (eq (k, (eq.symm k').2))) (h1 _).symm
    have e2 := hd 0 (by simp)
    have := congrFun (e1.trans e2.symm) (eq.symm k').1
    simpa using this
  · intro a
    obtain ⟨d, hd, _⟩ := hE a
    refine ⟨Fintype.card κ, fun j => d ((Fintype.equivFin κ).symm j),
      fun j => e ((Fintype.equivFin κ).symm j), ?_⟩
    rw [hd]
    exact (Equiv.sum_comp (Fintype.equivFin κ).symm
      (fun k => jS (d k) * (fun _ => algebraMap O A (e k) : ι → A))).symm

end Formalism.RepresentationBoundsCohomology.JW
