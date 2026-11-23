import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapTorus

theorem mul_of_comm_gen {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (hu : Algebra.adjoin K.E {u} = ⊤) (f : B.A → B.A) (hadd : ∀ y z, f (y + z) = f y + f z)
    (hsmul : ∀ (c : K.E) y, f (c • y) = c • f y) (hcomm : ∀ y, f (u * y) = u * f y) :
    ∀ y, f y = f 1 * y := by
  have key : ∀ s ∈ Algebra.adjoin K.E {u}, ∀ y, f (s * y) = s * f y := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hcomm
    | algebraMap c => intro y; rw [← Algebra.smul_def, hsmul, Algebra.smul_def]
    | add x y _ _ hx hy => intro z; rw [add_mul, hadd, hx, hy, add_mul]
    | mul x y _ _ hx hy => intro z; rw [mul_assoc, hx, hy, mul_assoc]
  intro y
  have := key y (hu ▸ Algebra.mem_top) 1
  rw [mul_one] at this
  rw [this, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stdH_unitary (w : Pl E) {n : ℕ} (h : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hh : cT (cj w) h * 1 * h = 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (h *ᵥ v) (h *ᵥ v') = stdH w v v' := by
  have e1 : ∀ y y' : Fin n → w.adicCompletion E, stdH w y y' = y ⬝ᵥ (fun k => cj w (y' k)) := fun _ _ => rfl
  have hmap : (fun k => cj w ((h *ᵥ v') k)) = (h.map (cj w)) *ᵥ (fun k => cj w (v' k)) := by
    funext k
    simp [Matrix.mulVec, dotProduct, map_sum]
  have ht : hᵀ * h.map (cj w) = 1 := by
    have := congrArg Matrix.transpose hh
    simpa [cT, Matrix.transpose_mul] using this
  rw [e1, e1, hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ht,
    Matrix.one_mulVec]

theorem stdH_single (w : Pl E) {n : ℕ} (v : Fin n → w.adicCompletion E) (i : Fin n) :
    stdH w v (Pi.single i 1) = v i := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

theorem torusOf_mem_of_mem_UL_commute : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w hw K e B Q u x n γ ψ hfit hmod h hU hc
  obtain ⟨hsm, hu, hst⟩ := hmod
  have conj : ∀ g : GLw n w, g * γ = γ * g → ∀ y, ψ.symm (g.val *ᵥ ψ y) = ψ.symm (g.val *ᵥ ψ 1) * y := by
    intro g hg
    apply mul_of_comm_gen B u hfit.1 (fun y => ψ.symm (g.val *ᵥ ψ y))
    · intro y z; simp [map_add, Matrix.mulVec_add]
    · intro c y
      apply ψ.injective
      simp only [hsm, ψ.apply_symm_apply, Matrix.mulVec_smul]
    · intro y
      apply ψ.injective
      simp only [hu, ψ.apply_symm_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, ← Units.val_mul, hg]
  have hc' : h⁻¹ * γ = γ * h⁻¹ := (Commute.inv_left (show Commute h γ from hc)).eq
  set a := ψ.symm (h.val *ᵥ ψ 1) with ha_def
  set b := ψ.symm ((h⁻¹ : GLw n w).val *ᵥ ψ 1) with hb_def
  have hab : a * b = 1 := by
    rw [← conj h hc b, hb_def, ψ.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, ψ.symm_apply_apply]
  let t : B.Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  have hspec : ∀ y, ψ ((t : B.A) * y) = h.val *ᵥ ψ y := by
    intro y
    show ψ (a * y) = _
    rw [← conj h hc y, ψ.apply_symm_apply]
  have htor : torusOf w B ψ h = t := torusOf_spec w B ψ h t hspec
  rw [htor]
  refine ⟨?_, hspec⟩

  have hUJ : cT (cj w) h.val * 1 * h.val = 1 := by
    have : h ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      unfold UL at hU; rwa [if_neg hw] at hU
    exact this
  have hinv : ∀ y z, B.herm x ((t : B.A) * y) ((t : B.A) * z) = B.herm x y z := by
    intro y z
    apply e.injective
    rw [← hst, ← hst, hspec, hspec, stdH_unitary w h.val hUJ]
  have hzero : ∀ y z, B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z = 0 := by
    intro y z
    have h1 : B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z =
        B.herm x ((t : B.A) * y) ((t : B.A) * z) - B.herm x y z := by
      unfold GlobalTheory.UnitLemma.InvAlg.herm
      rw [← map_sub]
      congr 1
      rw [map_mul]; ring
    rw [h1, hinv, sub_self]
  have hnd : ∀ m : B.A, (∀ z, B.herm x m z = 0) → m = 0 := by
    intro m hm
    apply ψ.injective
    rw [map_zero]
    funext i
    have := congrArg e (hm (ψ.symm (Pi.single i 1)))
    rw [← hst, ψ.apply_symm_apply, stdH_single, map_zero] at this
    simpa using this
  have := hnd _ (hzero 1)
  rw [mul_one, sub_eq_zero] at this
  exact this

end GlobalTheory.KapTorus
