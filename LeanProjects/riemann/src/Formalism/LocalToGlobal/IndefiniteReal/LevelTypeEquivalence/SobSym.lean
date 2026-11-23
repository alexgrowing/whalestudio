import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterSymmR

namespace Formalism.IndefR.Eqv

open scoped ContDiff

section Sym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem natCast_lt_inf' (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m

theorem two_le_inf : minSmoothness ℝ 2 ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact_mod_cast (natCast_lt_inf' 2).le

theorem inf_add_nat (m : ℕ) : (∞ : WithTop ℕ∞) + (m : WithTop ℕ∞) ≤ ∞ := by
  first
    | (rw [(WithTop.coe_natCast m).symm, ← WithTop.coe_add, top_add])
    | simp
    | (norm_cast; simp)

theorem iterated_fderiv_swap_first_two {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {g : E → H} (hg : ContDiff ℝ ∞ g) (m : ℕ)
    (x : E) (v : Fin (m + 2) → E) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (m + 2) g x v := by
  have key : ∀ u : Fin (m + 2) → E, iteratedFDeriv ℝ (m + 2) g x u =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m g)) x (u 0) (u 1) (Fin.tail (Fin.tail u)) := by
    intro u
    rw [iteratedFDeriv_succ_apply_left]
    have hL : iteratedFDeriv ℝ (m + 1) g =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) H).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ m g) := by
      rw [iteratedFDeriv_succ_eq_comp_left]
    rw [hL, LinearIsometryEquiv.comp_fderiv]
    rfl
  rw [key, key]
  have hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ m g) x :=
    ((hg.iteratedFDeriv_right (m := ∞) (i := m) (inf_add_nat m)).contDiffAt).isSymmSndFDerivAt two_le_inf
  have e0 : (v ∘ Equiv.swap 0 1) 0 = v 1 := by simp
  have e1 : (v ∘ Equiv.swap 0 1) 1 = v 0 := by simp
  have e2 : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext j
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => by
      have := congrArg Fin.val h; simp at this)]
  rw [e0, e1, e2, hs (v 1) (v 0)]

theorem fderiv_inv {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H} (hΦ : Differentiable ℝ Φ) (σ : Equiv.Perm (Fin n))
    (hinv : ∀ y u, Φ y (u ∘ σ) = Φ y u) (x w : E) (u : Fin n → E) :
    fderiv ℝ Φ x w (u ∘ σ) = fderiv ℝ Φ x w u := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H →L[ℝ] H :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H (u ∘ σ) -
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H u
  have hzero : (fun y => A (Φ y)) = fun _ => 0 := by
    funext y
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply, hinv, sub_self]
  have h1 : fderiv ℝ (fun y => A (Φ y)) x = A.comp (fderiv ℝ Φ x) :=
    (A.hasFDerivAt.comp x (hΦ x).hasFDerivAt).fderiv
  rw [hzero, fderiv_const_apply] at h1
  have h2 := congrArg (fun T => T w) h1
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply, A,
    ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply] at h2
  exact (sub_eq_zero.mp h2.symm)

theorem iterSymm_succ (m : ℕ) (IH : ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (x : E) (v : Fin (m + 1) → E) (σ : Equiv.Perm (Fin (m + 1))),
      iteratedFDeriv ℝ (m + 1) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 1) g x v)
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H) (hg : ContDiff ℝ ∞ g) (x : E)
    (v : Fin (m + 2) → E) (σ : Equiv.Perm (Fin (m + 2))) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 2) g x v := by
  have hgen : σ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  revert v
  induction hgen using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    intro v
    cases i using Fin.cases with
    | zero => exact iterated_fderiv_swap_first_two hg m x v
    | succ a =>
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have hΦ : Differentiable ℝ (iteratedFDeriv ℝ (m + 1) g) :=
        hg.differentiable_iteratedFDeriv (natCast_lt_inf' (m + 1))
      have hne0 : ∀ j : Fin (m + 2), j ≠ 0 → True := fun _ _ => trivial
      have h0 : (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) 0 = v 0 := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => by have := congrArg Fin.val h; simp at this)
          (fun h => by have := congrArg Fin.val h; simp at this)]
      have ht : Fin.tail (v ∘ Equiv.swap (a.succ.castSucc) a.succ.succ) =
          Fin.tail v ∘ Equiv.swap a.castSucc a.succ := by
        funext j
        simp only [Fin.tail, Function.comp_apply]
        congr 1
        rw [show a.succ.castSucc = a.castSucc.succ from rfl]
        exact (Fin.succ_injective _).swap_apply _ _ _
      rw [h0, ht]
      exact fderiv_inv hΦ _ (fun y u => IH H g hg y u _) x (v 0) (Fin.tail v)
  | one => intro v; rfl
  | mul τ ρ _ _ hτ hρ =>
    intro v
    have e : v ∘ ⇑(τ * ρ) = (v ∘ τ) ∘ ρ := rfl
    rw [e, hρ (v ∘ τ), hτ v]

theorem iterSymmR : IterSymmR := by
  intro E H _ _ _ _ g hg n
  match n with
  | 0 =>
    intro x v σ
    have : σ = 1 := Equiv.ext fun a => a.elim0
    rw [this]; rfl
  | m + 1 =>
    induction m generalizing H g with
    | zero =>
      intro x v σ
      have : σ = 1 := Equiv.ext fun a => Fin.ext (by have := (σ a).isLt; have := a.isLt; simp)
      rw [this]; rfl
    | succ m ih => exact iterSymm_succ m (fun H _ _ g hg => ih H g hg) H g hg

end Sym

end Formalism.IndefR.Eqv
