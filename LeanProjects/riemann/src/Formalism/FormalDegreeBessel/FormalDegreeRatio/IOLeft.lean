import Formalism.FormalDegreeBessel.StatementIO

open Matrix Formalism.REAL

noncomputable section

namespace Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma ioLeft_rdV_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X h : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    RdV X (fun x => f (h * x)) = fun x => RdV X f (h * x) := by
  funext g
  simp only [RdV, mul_assoc]

lemma ioLeft_eabV_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ε : Fin n → Bool) (a b : Fin n) (h : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    EabV ε a b (fun x => f (h * x)) = fun x => EabV ε a b f (h * x) := by
  funext g
  simp only [EabV, EcV, ioLeft_rdV_left]

lemma ioLeft_eabH_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (h : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    EabH H a b (fun x => f (h * x)) = fun x => EabH H a b f (h * x) := by
  funext g
  simp only [EabH, ioLeft_rdV_left]

lemma ioLeft_foldr_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ)
    (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (List.mem_cons.2 (Or.inr hT')))]
    exact hL T (List.mem_cons.2 (Or.inl rfl)) _

private lemma qminorOp_comm_left_mul_of_Eop_comm_left_mul {n t : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E),
      Eop a b (fun x => f (h * x)) = fun x => Eop a b f (h * x))
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    qminorOp Eop a b u (fun x => f (h * x)) = fun x => qminorOp Eop a b u f (h * x) := by
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [ioLeft_foldr_left h _ ?_ f]
  intro T hT f'
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨k, rfl⟩ := hT
  funext g
  simp only [Top, hE]

theorem quantum_minor_left_holds : QMinorLeft := by
  intro n t ε E _ _ f a b u h
  exact qminorOp_comm_left_mul_of_Eop_comm_left_mul (EabV ε) h (fun a b f => ioLeft_eabV_left ε a b h f) a b u f

theorem capelli_left_holds : CapLeft := by
  intro n ε E _ _ f u h
  exact quantum_minor_left_holds n n ε E f id id u h

theorem capelli_left_conjugated : CapLeftH := by
  intro n E _ _ H f u h
  exact qminorOp_comm_left_mul_of_Eop_comm_left_mul (EabH H) h (fun a b f => ioLeft_eabH_left H a b h f) id id u f

private lemma commutator_sum_smul_eq_sum_sum_smul_commutator {A : Type*} [Ring A] [Algebra ℂ A] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (r : ι → ℂ) (x : ι → A) (s : κ → ℂ) (y : κ → A) :
    (∑ i, r i • x i) * (∑ k, s k • y k) - (∑ k, s k • y k) * (∑ i, r i • x i) =
      ∑ i, ∑ k, (r i * s k) • (x i * y k - y k * x i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by congr 1; ring

private lemma commutator_right_transform_of_commutation_relation {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ a b c d, E a b * E c d - E c d * E a b = M b c • E a d - M d a • E c b)
    (a b c d : Fin n) :
    (∑ j, Q b j • E a j) * (∑ l, Q d l • E c l) - (∑ l, Q d l • E c l) * (∑ j, Q b j • E a j) =
      (Q * M) b c • (∑ l, Q d l • E a l) - (Q * M) d a • (∑ j, Q b j • E c j) := by
  rw [commutator_sum_smul_eq_sum_sum_smul_commutator]
  simp only [hE, smul_sub, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul, Finset.sum_mul]
  congr 1
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)

private lemma commutator_left_transform_of_commutation_relation {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (M P : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ a b c d, F a b * F c d - F c d * F a b = M b c • F a d - M d a • F c b)
    (a b c d : Fin n) :
    (∑ i, P i a • F i b) * (∑ k, P k c • F k d) - (∑ k, P k c • F k d) * (∑ i, P i a • F i b) =
      (M * P) b c • (∑ i, P i a • F i d) - (M * P) d a • (∑ k, P k c • F k b) := by
  rw [commutator_sum_smul_eq_sum_sum_smul_commutator]
  simp only [hF, smul_sub, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul, Finset.sum_mul]
  congr 1
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)

theorem gl_relation_adjoint_holds : GlRelAd := by
  intro A _ _ n E P Q hE hQP
  have h1 : ∀ a b c d, E a b * E c d - E c d * E a b =
      (1 : Matrix (Fin n) (Fin n) ℂ) b c • E a d - (1 : Matrix (Fin n) (Fin n) ℂ) d a • E c b := by
    intro a b c d
    rw [hE a b c d]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
  have h3 := commutator_left_transform_of_commutation_relation (fun a b => ∑ j, Q b j • E a j) (Q * 1) P (commutator_right_transform_of_commutation_relation E 1 Q h1)
  beta_reduce at h3
  have e : ∀ a b, (∑ c, ∑ d, (P c a * Q b d) • E c d) = ∑ i, P i a • ∑ j, Q b j • E i j := by
    intro a b
    simp only [Finset.smul_sum, smul_smul]
  intro a b c d
  simp only [e]
  rw [h3 a b c d, Matrix.mul_one, hQP]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]

end Formalism.QuantumDeterminants
