import Mathlib

theorem UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A]
    {n : ℕ} (f : MvPolynomial (Fin (n + (1 : ℕ))) A) (v w : Fin (n + (1 : ℕ)) →₀ ℕ),
    (∀ (i : Fin (n + (1 : ℕ))), (v : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
      (∀ (i : Fin (n + (1 : ℕ))), (w : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
        v ≠ w →
          ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (v : Fin (n + (1 : ℕ)) → ℕ) x ≠
            ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (w : Fin (n + (1 : ℕ)) → ℕ) x := by
  intro A _ _ n f v w hv hw hne h
  apply hne
  have key : finFunctionFinEquiv (fun i => (⟨v i, hv i⟩ : Fin (2 + f.totalDegree))) =
      finFunctionFinEquiv (fun i => (⟨w i, hw i⟩ : Fin (2 + f.totalDegree))) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    simpa only [mul_comm] using h
  have hfun := finFunctionFinEquiv.injective key
  ext i
  exact congrArg Fin.val (congrFun hfun i)
