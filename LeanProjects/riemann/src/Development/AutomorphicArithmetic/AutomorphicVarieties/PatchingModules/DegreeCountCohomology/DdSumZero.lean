import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem dd_sum_zero {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (ua : u.a = 0) (va : v.a = 0)
    (ue : u.ep' = 0) (ve : v.ep' = 0) : u * v = 0 := by
  apply DD.ext
  · simp [DD.mul_a, ua]
  · funext j
    simp [DD.mul_ep, ua, va]
  · funext j
    simp [DD.mul_ep', ue, ve]
  · simp [DD.mul_eta, ua, va, ue, ve]

private theorem epM_sq {X : Type} [CommRing X] {g n : ℕ} (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z' = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun c _ => dd_sum_zero _ _ rfl rfl rfl rfl

private theorem epM_tr {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM Z)ᵀ = DD.epM fun j => (Z j)ᵀ := rfl

private theorem epM_neg {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    (DD.epM fun j => -Z j) = -DD.epM Z := by
  ext a b <;> simp [DD.epM]

theorem UpperTheory.V.Pa.rho1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, (k.ρ1 X g)ᵀ * k.ρ1 X (F.conj g) = algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD X k.g))) ∧ (∀ v, k.wi1 X v * k.w1 X v = 1 ∧ k.w1 X v * k.wi1 X v = 1) ∧ ∀ u, ∀ g ∈ F.Iu u, k.ρ1 X g = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, hmul, -, hw⟩ := Det.rho1Hom k X
  refine ⟨h1, hmul, fun g => ?_, fun v => ⟨(hw v).2, (hw v).1⟩, fun u g hg => ?_⟩
  · have hc : (fun j => (k.κ j (F.conj g)).map (algebraMap x.A X)) =
        fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ) := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      ext a b
      simp
    have hA : ((DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) : Matrix (Fin n) (Fin n) (DD X k.g))ᵀ *
        DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ)) = 0 := by
      rw [epM_neg, Matrix.mul_neg, epM_tr, epM_sq, neg_zero]
    have hρ : (x.ρX (DD X k.g) g)ᵀ * x.ρX (DD X k.g) (F.conj g) =
        algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) •
          (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
      have hf := x.form g
      simp only [Units.val_one, Matrix.mul_one] at hf
      unfold NP.ρX
      rw [← Matrix.transpose_map, ← Matrix.map_mul, hf]
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j
      · subst h
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, h]
    unfold Kap.ρ1
    rw [hc, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
    have h2 : (1 + (DD.epM fun j => (k.κ j g).map (algebraMap x.A X))ᵀ) *
        (1 + DD.epM (fun j => -(((k.κ j g).map (algebraMap x.A X))ᵀ))) = 1 := by
      rw [add_mul, one_mul, mul_add, mul_one, hA, add_zero, epM_neg, epM_tr]
      abel
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + _), h2, Matrix.one_mul, hρ]
  · have hz : ∀ j, k.κ j g = 0 := fun j => (k.mem j).2.2.2.2.1 u g hg
    have hm : (mat x.ρ) g = 1 := by simp [mat, x.ine u g hg]
    have he : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = 0 := by
      refine Matrix.ext fun a b => ?_
      ext <;> simp [hz, DD.epM]
    unfold Kap.ρ1 NP.ρX
    rw [hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, he, add_zero]
