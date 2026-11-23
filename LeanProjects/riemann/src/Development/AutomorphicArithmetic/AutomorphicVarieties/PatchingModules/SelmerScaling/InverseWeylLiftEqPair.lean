import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section P

variable {A : Type} (R : Type) [CommRing A] [CommRing R] [Algebra A R] {e n : ℕ}

private def PP (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) (DD R e) :=
  Matrix.of fun a b => ⟨algebraMap A R (M a b), fun j => algebraMap A R (Z j a b), 0, 0⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD R e) (j) : (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD R e) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem congruenceCondition_mul (M M' : Matrix (Fin n) (Fin n) A) (Z Z' : Fin e → Matrix (Fin n) (Fin n) A) :
    PP R M Z * PP R M' Z' = PP R (M * M') (fun j => M * Z' j + Z j * M') := by
  ext a b j <;> simp [PP, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta, Finset.sum_add_distrib]

private theorem pair_matrix_transpose (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (PP R M Z)ᵀ = PP R Mᵀ (fun j => (Z j)ᵀ) := rfl

private theorem PP_map (M : Matrix (Fin n) (Fin n) A) :
    M.map (algebraMap A (DD R e)) = PP R M (fun _ => 0) := by
  ext a b j
  · rfl
  · simp only [PP, Matrix.of_apply, Matrix.zero_apply, map_zero]; rfl
  · rfl
  · rfl

private theorem PP_one : PP R (1 : Matrix (Fin n) (Fin n) A) (fun _ : Fin e => 0) = 1 := by
  rw [← PP_map]; exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem PP_add (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 + DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 Z := by
  rw [← PP_one (A := A) R]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_sub (Z : Fin e → Matrix (Fin n) (Fin n) A) :
    (1 - DD.epM fun j => (Z j).map (algebraMap A R)) = PP R 1 (fun j => -Z j) := by
  rw [← PP_one (A := A) R, sub_eq_add_neg]
  ext a b j <;> simp [PP, DD.epM]

private theorem PP_apply (M : Matrix (Fin n) (Fin n) A) (Z : Fin e → Matrix (Fin n) (Fin n) A) (a b : Fin n)
    (h : ∀ j, Z j a b = 0) : PP R M Z a b = algebraMap A (DD R e) (M a b) := by
  have := congrFun (congrFun (PP_map R (e := e) M) a) b
  rw [Matrix.map_apply] at this
  rw [this]
  simp [PP, h]

private theorem od_ev {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    Z * M ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ i k).1 hk), zero_mul]
  · rw [(Submodule.mem_bot A).1 ((hM k j).2 (by tauto)), mul_zero]

private theorem ev_od {a : ℕ} {Z M : Matrix (Fin n) (Fin n) A} (hZ : Z ∈ Od A A n a) (hM : M ∈ Ev A A n a) :
    M * Z ∈ Od A A n a := by
  intro i j
  refine ⟨fun h => ?_, fun _ => trivial⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [(Submodule.mem_bot A).1 ((hZ k j).1 (by tauto)), mul_zero]
  · rw [(Submodule.mem_bot A).1 ((hM i k).2 hk), zero_mul]

private theorem tri_mul {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    ∀ i j, j < i → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (lt_of_lt_of_le hij (not_lt.1 hk)), mul_zero]

end P

section K

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (R : Type) [CommRing R] [Algebra x.A R]

private theorem ρ1_eq (g : F.G₀) : k.ρ1 R g = PP R (x.ρX x.A g) (fun j => k.κ j g * x.ρX x.A g) := by
  have : x.ρX (DD R k.g) g = PP R (x.ρX x.A g) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.ρ1, PP_add, this, congruenceCondition_mul]; simp

private theorem weyl_lift_eq_pair (v) : k.w1 R v = PP R (x.wX x.A v) (fun j => -(k.Y j v * x.wX x.A v)) := by
  have : x.wX (DD R k.g) v = PP R (x.wX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.w1, PP_sub, this, congruenceCondition_mul]; simp

private theorem inverse_weyl_lift_eq_pair (v) : k.wi1 R v = PP R (x.wiX x.A v) (fun j => x.wiX x.A v * k.Y j v) := by
  have : x.wiX (DD R k.g) v = PP R (x.wiX x.A v) (fun _ => 0) := by rw [← PP_map]; rfl
  rw [Kap.wi1, PP_add, this, congruenceCondition_mul]; simp

end K

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rho1Tri :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (R : Type) [CommRing R] [Algebra x.A R], (∀ g g', k.ρ1 R (g * g') = k.ρ1 R g * k.ρ1 R g') ∧ k.ρ1 R 1 = 1 ∧ (∀ g, (k.ρ1 R g)ᵀ * k.ρ1 R (G0.frame.conj g) = algebraMap x.A (DD R k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD R k.g))) ∧ (∀ w, ∀ g ∈ G0.frame.Iu w, k.ρ1 R g = 1) ∧ (∀ g, k.ρ1 R g ∈ W1 n x.A R k.g x.a) ∧ ∀ v, k.w1 R v * k.wi1 R v = 1 ∧ k.wi1 R v * k.w1 R v = 1 ∧ ∀ g, (∀ i j, j < i → (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i j = 0) ∧ ∀ i, (k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v) i i = algebraMap x.A (DD R k.g) (x.ψ v i g) := by
  intro l _ L G G0 h n x k R _ _
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := fun g => rfl
  have hmul : ∀ g g', x.ρX x.A (g * g') = x.ρX x.A g * x.ρX x.A g' := by
    intro g g'; simp [hρ, mat]
  have hone : x.ρX x.A 1 = 1 := by simp [hρ, mat]
  have hinv : ∀ g, x.ρX x.A g⁻¹ * x.ρX x.A g = 1 := by
    intro g; rw [← hmul, inv_mul_cancel, hone]
  have hev : ∀ g, x.ρX x.A g ∈ Ev x.A x.A n x.a := x.blk
  have hform : ∀ g, (x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g) =
      ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g
    have := x.form g
    rw [Units.val_one, Matrix.mul_one] at this
    exact this
  refine ⟨fun g g' => ?_, ?_, fun g => ?_, fun w g hg => ?_, fun g => ?_, fun v => ?_⟩
  · rw [ρ1_eq, ρ1_eq, ρ1_eq, congruenceCondition_mul, hmul]
    congr 1
    funext j
    rw [(k.mem j).2.2.1 g g', add_mul, add_comm, Matrix.mul_assoc (_ * _), ← Matrix.mul_assoc (x.ρX x.A g⁻¹), hinv]
    simp only [Matrix.mul_assoc, Matrix.one_mul]
  · rw [ρ1_eq, hone, ← PP_one (A := x.A) R]
    congr 1
    funext j
    have := (k.mem j).2.2.1 1 1
    simp only [mul_one, inv_one, hone, one_mul] at this
    rw [mul_one]
    exact left_eq_add.1 this
  · rw [ρ1_eq, ρ1_eq, pair_matrix_transpose, congruenceCondition_mul, hform]
    have : (fun j => (x.ρX x.A g)ᵀ * (k.κ j (G0.frame.conj g) * x.ρX x.A (G0.frame.conj g)) +
        (k.κ j g * x.ρX x.A g)ᵀ * x.ρX x.A (G0.frame.conj g)) = fun _ => 0 := by
      funext j
      rw [(k.mem j).2.2.2.1 g]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, ← PP_map]
    ext1 a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [ρ1_eq, ← PP_one (A := x.A) R]
    have : x.ρX x.A g = 1 := by simp [hρ, mat, x.ine w g hg]
    rw [this]
    congr 1
    funext j
    rw [(k.mem j).2.2.2.2.1 w g hg, zero_mul]
  · rw [ρ1_eq]
    intro a b
    refine ⟨fun hab => ⟨by simp, fun _ => ?_, fun _ => rfl, fun _ => rfl⟩,
      fun hab => ⟨fun _ => ?_, by simp, fun _ => rfl, fun _ => rfl⟩⟩
    · funext j
      have := (Submodule.mem_bot _).1 ((od_ev ((k.mem j).1 g) (hev g) a b).1 hab)
      simp [PP, this]
    · have := (Submodule.mem_bot _).1 ((hev g a b).2 hab)
      simp [PP, this]
  · obtain ⟨h1, h2, h3, h4, -⟩ := oddDiag l L G G0 h n x x.A v
    refine ⟨?_, ?_, fun g => ?_⟩
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h1, ← PP_one (A := x.A) R]
      congr 1
      funext j
      rw [← Matrix.mul_assoc, h1, neg_mul, Matrix.mul_assoc, h1]; simp
    · rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, congruenceCondition_mul, h2, ← PP_one (A := x.A) R]
      congr 1
      funext j
      simp [Matrix.mul_assoc]
    · set r := x.ρX x.A (G0.φ v g) with hr
      have key : k.wi1 R v * k.ρ1 R (G0.φ v g) * k.w1 R v = PP R (x.wiX x.A v * r * x.wX x.A v)
          (fun j => x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v) := by
        rw [weyl_lift_eq_pair, inverse_weyl_lift_eq_pair, ρ1_eq, congruenceCondition_mul, congruenceCondition_mul]
        congr 1
        funext j
        rw [← hr]
        noncomm_ring
      rw [key]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · rw [PP_apply, (h4 g).1 a b hab, map_zero]
        intro j
        have e : x.wiX x.A v * (k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v) * x.wX x.A v =
            (x.wiX x.A v * (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * x.wX x.A v) *
              (x.wiX x.A v * r * x.wX x.A v) := by
          have e1 : (k.κ j (G0.φ v g) - dY G0.frame (x.ρX x.A) (k.Y j v) (G0.φ v g)) * r =
              k.κ j (G0.φ v g) * r + k.Y j v * r - r * k.Y j v := by
            rw [dY, sub_mul, sub_mul, Matrix.mul_assoc _ _ r, hr, hinv, mul_one]; abel
          rw [← e1]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (x.wX x.A v), h1, one_mul]
        rw [e]
        exact tri_mul (k.loc j v g).1 (h4 g).1 a b hab
      · rw [PP_apply, (h4 g).2 a]
        · rfl
        intro j
        refine h3 _ ?_ a
        exact Submodule.sub_mem _ (Submodule.add_mem _ (od_ev ((k.mem j).1 _) (hev _)) (od_ev (k.Y_mem j v) (hev _)))
          (ev_od (k.Y_mem j v) (hev _))
