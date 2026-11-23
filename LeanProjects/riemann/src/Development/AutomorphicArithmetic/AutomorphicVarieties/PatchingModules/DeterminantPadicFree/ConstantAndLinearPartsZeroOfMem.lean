import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.W1sMem

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Comp

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

private def aM (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X := Z.map DD.a

private def epC (j : Fin g) (Z : Matrix (Fin n) (Fin n) (DD X g)) : Matrix (Fin n) (Fin n) X :=
  Z.map fun d => d.ep j

variable (P Q : Matrix (Fin n) (Fin n) (DD X g))

variable (M : Matrix (Fin n) (Fin n) A) (K : Fin g → Matrix (Fin n) (Fin n) X)

variable {N N' : Matrix (Fin n) (Fin n) X}

variable {M}

variable {P}

end Comp

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

private theorem dd_eta_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).eta = ∑ m ∈ s, (f m).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_eta]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_eta, ih]

private theorem dd_a_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).a = ∑ m ∈ s, (f m).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_a, ih]

private theorem dd_ep_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep j = ∑ m ∈ s, (f m).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep, ih]

private theorem dd_ep'_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep' j = ∑ m ∈ s, (f m).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep']
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep', ih]

private theorem matrix_map_dd_a_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.a = P.map DD.a * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, dd_a_sum, DD.mul_a]

private theorem matrix_map_dd_ep_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep j) = P.map DD.a * Q.map (fun d => d.ep j) + P.map (fun d => d.ep j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep_sum, DD.mul_ep, Finset.sum_add_distrib]

private theorem matrix_map_dd_ep'_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep' j) = P.map DD.a * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep'_sum, DD.mul_ep', Finset.sum_add_distrib]

private theorem matrix_map_dd_eta_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.eta = P.map DD.a * Q.map DD.eta + P.map DD.eta * Q.map DD.a +
      ∑ j, (P.map (fun d => d.ep j) * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map (fun d => d.ep j)) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.sum_apply, dd_eta_sum, DD.mul_eta,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 2
  exact Finset.sum_comm

private theorem mul_apply_eq_zero_of_block_parity {X : Type} [CommRing X] {n a : ℕ} (p q : Prop) (P Q : Matrix (Fin n) (Fin n) X)
    (hP : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ p) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ q) → Q i j = 0) :
    ∀ i k : Fin n, ¬(((i : ℕ) < a ↔ (k : ℕ) < a) ↔ (p ↔ q)) → (P * Q) i k = 0 := by
  intro i k h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : (((i : ℕ) < a ↔ (m : ℕ) < a) ↔ p)
  · have h2 : ¬(((m : ℕ) < a ↔ (k : ℕ) < a) ↔ q) := by tauto
    rw [hQ m k h2, mul_zero]
  · rw [hP i m h1, zero_mul]

private theorem ofPar_lemma {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (p : Prop)
    (P : Matrix (Fin n) (Fin n) X) :
    (P ∈ blkMat n a (⊤ : Submodule A X) ⊥ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) ∧
    (P ∈ blkMat n a (⊥ : Submodule A X) ⊤ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) → P ∈ blkMat n a (⊤ : Submodule A X) ⊥) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) → P ∈ blkMat n a (⊥ : Submodule A X) ⊤) := by
  refine ⟨fun h i j hij => ?_, fun h i j hij => ?_, fun h i j => ?_, fun h i j => ?_⟩
  · exact (Submodule.mem_bot A).1 ((h i j).2 (by tauto))
  · exact (Submodule.mem_bot A).1 ((h i j).1 (by tauto))
  · exact ⟨fun _ => Submodule.mem_top, fun hh => (Submodule.mem_bot A).2 (h i j (by tauto))⟩
  · exact ⟨fun hh => (Submodule.mem_bot A).2 (h i j (by tauto)), fun _ => Submodule.mem_top⟩

private theorem ev_od_graded_mul_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P Q : Matrix (Fin n) (Fin n) X) :
    (P ∈ Ev A X n a → Q ∈ Ev A X n a → P * Q ∈ Ev A X n a) ∧
    (P ∈ Ev A X n a → Q ∈ Od A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Ev A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Od A X n a → P * Q ∈ Ev A X n a) := by
  have c := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True
  refine ⟨fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_⟩
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity True True P Q ((c P).1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity True False P Q ((c P).1 hP) ((c Q).2.1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity False True P Q ((c P).2.1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity False False P Q ((c P).2.1 hP) ((c Q).2.1 hQ) i k (by tauto)

private theorem map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P : Matrix (Fin n) (Fin n) A) :
    (P ∈ Ev A A n a → P.map (algebraMap A X) ∈ Ev A X n a) ∧
    (P ∈ Od A A n a → P.map (algebraMap A X) ∈ Od A X n a) := by
  have c := ofPar_lemma (A := A) (X := A) (n := n) (a := a) True P
  have d := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True (P.map (algebraMap A X))
  refine ⟨fun hP => d.2.2.1 fun i j h => ?_, fun hP => d.2.2.2 fun i j h => ?_⟩
  · rw [Matrix.map_apply, c.1 hP i j h, map_zero]
  · rw [Matrix.map_apply, c.2.1 hP i j h, map_zero]

private theorem mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    (T : Matrix (Fin n) (Fin n) (DD X g)) (ha : T.map DD.a = 0) (he : ∀ c, T.map (fun d => d.ep c) = 0)
    (he' : ∀ c, T.map (fun d => d.ep' c) ∈ Od A X n a) (ht : T.map DD.eta ∈ Ev A X n a) :
    T ∈ pairedDualFirstOrderDualMatrixSpace n A X g a := by
  intro i j
  have h1 := (ofPar_lemma (A := A) True (T.map DD.eta)).1 ht i j
  have h2 : ∀ c, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → (T i j).ep' c = 0 := fun c =>
    (ofPar_lemma (A := A) True (T.map fun d => d.ep' c)).2.1 (he' c) i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun _ => funext fun c => h2 c (by tauto), fun hf => absurd hf (by decide)⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun hf => absurd hf (by decide), fun _ => h1 (by tauto)⟩

theorem UpperTheory.V.Pa.Det.w1sAct :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (Z : Matrix (Fin n) (Fin n) (DD X k.g)), Z ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a → ∀ g, k.ρ1 X g * Z * k.ρ1 X g⁻¹ ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a ∧ (∀ j, ep'M j (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * ep'M j Z * x.ρX X g⁻¹) ∧ etaM (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * etaM Z * x.ρX X g⁻¹ + ∑ j, ((k.κ j g).map (algebraMap x.A X) * (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) - (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) * (k.κ j g).map (algebraMap x.A X)) ∧ (Z * k.ρ1 X g).trace.eta = (etaM Z * x.ρX X g).trace + ∑ j, (ep'M j Z * (k.κ j g).map (algebraMap x.A X) * x.ρX X g).trace := by
  intro l _ F n x k X _ _ Z hZ g
  have hinv := (UpperTheory.V.Pa.Det.rho1Hom k X).2.2.1 g
  simp only [UpperTheory.V.Pa.Kap.ρ1] at *
  rw [hinv]
  clear hinv
  have hZ' : ∀ i j : Fin n, _ := hZ
  simp only [ddPart] at hZ'
  have hZa : Z.map DD.a = 0 := by
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact ((hZ' i j).1 h).1 trivial
    · exact ((hZ' i j).2 h).1 trivial
  have hZe : ∀ c : Fin k.g, Z.map (fun d => d.ep c) = 0 := by
    intro c
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact congrFun (((hZ' i j).1 h).2.1 trivial) c
    · exact congrFun (((hZ' i j).2 h).2.1 trivial) c
  clear hZ'
  have hR : ∀ h : F.G₀, x.ρX (DD X k.g) h = (x.ρX X h).map DD.C := by
    intro h
    funext i j
    simp only [NP.ρX, Matrix.map_apply, alg_eq]
  have hC : ∀ M : Matrix (Fin n) (Fin n) X, (M.map (DD.C (g := k.g))).map DD.a = M ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep c) = 0) ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep' c) = 0) ∧
      (M.map (DD.C (g := k.g))).map DD.eta = 0 := by
    intro M
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> simp [DD.C_a, DD.C_ep, DD.C_ep', DD.C_eta]
  set K : Fin k.g → Matrix (Fin n) (Fin n) X := fun j => (k.κ j g).map (algebraMap x.A X) with hKdef
  have hP : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep c) = K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a, DD.one_ep,
        DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta]
  have hM : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep c) = -K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [sub_eq_add_neg, Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a,
        DD.one_ep, DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta, DD.neg_a, DD.neg_ep,
        DD.neg_ep', DD.neg_eta]
  have htr : ∀ M : Matrix (Fin n) (Fin n) (DD X k.g), M.trace.eta = (M.map DD.eta).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, dd_eta_sum, Matrix.map_apply]
  rw [hR g, hR g⁻¹, htr]
  obtain ⟨hCa, hCe, hCe', hCt⟩ := hC (x.ρX X g)
  obtain ⟨hCa2, hCe2, hCe'2, hCt2⟩ := hC (x.ρX X g⁻¹)
  obtain ⟨hPa, hPe, hPe', hPt⟩ := hP
  obtain ⟨hMa, hMe, hMe', hMt⟩ := hM
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · have hρ : x.ρX X g ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g)
    have hρ' : x.ρX X g⁻¹ ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g⁻¹)
    have hW := (UpperTheory.V.Pa.Det.w1sMem (A := x.A) (X := X) (g := k.g) (n := n) (a := x.a)).1 Z hZ
    have hY0 : Z.map DD.eta ∈ Ev x.A X n x.a := hW.1
    have hY : ∀ c, Z.map (fun d => d.ep' c) ∈ Od x.A X n x.a := hW.2
    have hK : ∀ c, K c ∈ Od x.A X n x.a := fun c => (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).2 ((k.mem c).1 g)
    apply mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact (ev_od_graded_mul_mem _ _).2.2.1 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) hρ'
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact add_mem
        ((ev_od_graded_mul_mem _ _).1 (add_mem ((ev_od_graded_mul_mem _ _).1 hρ hY0)
          (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.2.1 (hK c) hρ) (hY c))) hρ')
        (neg_mem (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) ((ev_od_graded_mul_mem _ _).2.1 hρ' (hK c))))
  · simp only [ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.add_mul, Finset.sum_mul, Matrix.mul_assoc, Finset.sum_sub_distrib]
    abel
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.mul_assoc]
