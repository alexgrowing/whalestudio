import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.TyCard
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

private theorem epM_mul_epM (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z' = 0 := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta]

private theorem epM_sub (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun j => Z j - Z' j) = DD.epM Z - DD.epM Z' := by
  ext a b <;> simp [DD.epM, sub_eq_add_neg]

private theorem mul_epM (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    M.map (algebraMap A (DD X g)) * DD.epM Z = DD.epM fun j => M.map (algebraMap A X) * Z j := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem epM_mul (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * M.map (algebraMap A (DD X g)) = DD.epM fun j => Z j * M.map (algebraMap A X) := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private def Pat (s t : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) (DD X g)) : Prop :=
  ∀ i j, (Z i j).ep' = 0 ∧ (Z i j).eta = 0 ∧ (s i = t j → (Z i j).ep = 0) ∧ (s i ≠ t j → (Z i j).a = 0)

private theorem Pat.mul {s t u : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) (DD X g)} (hP : Pat s t P)
    (hQ : Pat t u Q) : Pat s u (P * Q) := by
  intro i j
  rw [Matrix.mul_apply]
  refine ⟨funext fun m => ?_, ?_, fun e => funext fun m => ?_, fun e => ?_⟩
  · rw [sum_ep']
    exact Finset.sum_eq_zero fun c _ => by simp [(hP i c).1, (hQ c j).1]
  · rw [sum_eta]
    exact Finset.sum_eq_zero fun c _ => by simp [(hP i c).1, (hQ c j).1, (hP i c).2.1, (hQ c j).2.1]
  · rw [sum_ep]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : s i = t c
    · simp [(hP i c).2.2.1 h, (hQ c j).2.2.1 (h.symm.trans e)]
    · simp [(hP i c).2.2.2 h, (hQ c j).2.2.2 (fun h' => h (e.trans h'.symm))]
  · rw [sum_a]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : s i = t c
    · simp [(hQ c j).2.2.2 (fun h' => e (h.trans h'))]
    · simp [(hP i c).2.2.2 h]

private theorem pat_map {s t : Fin n → Bool} (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, s i ≠ t j → M i j = 0) :
    Pat s t (M.map (algebraMap A (DD X g))) := fun i j =>
  ⟨rfl, rfl, fun _ => rfl, fun e => by simp [h i j e]⟩

private theorem pat_add {s : Fin n → Bool} (M : Fin g → Matrix (Fin n) (Fin n) X)
    (h : ∀ m i j, s i = s j → M m i j = 0) : Pat s s (1 + DD.epM M) := by
  intro i j
  refine ⟨funext fun m => ?_, ?_, fun e => funext fun m => ?_, fun e => ?_⟩
  · by_cases c : i = j <;> simp [DD.epM, Matrix.one_apply, c]
  · by_cases c : i = j <;> simp [DD.epM, Matrix.one_apply, c]
  · have := h m i j e
    by_cases c : i = j
    · subst c; simp [DD.epM, this]
    · simp [DD.epM, c, this]
  · have c : i ≠ j := by rintro rfl; exact e rfl
    simp [DD.epM, c]

private theorem pat_sub {s : Fin n → Bool} (M : Fin g → Matrix (Fin n) (Fin n) X)
    (h : ∀ m i j, s i = s j → M m i j = 0) : Pat s s (1 - DD.epM M) := by
  have e : 1 - DD.epM M = 1 + DD.epM fun m => - M m := by
    ext a b <;> simp [DD.epM, sub_eq_add_neg]
  rw [e]
  exact pat_add _ fun m i j c => by simp [h m i j c]

private theorem mem_W1_iff_pattern (a : ℕ) (Z : Matrix (Fin n) (Fin n) (DD X g)) :
    Z ∈ W1 n A X g a ↔ Pat (fun i => decide ((i : ℕ) < a)) (fun i => decide ((i : ℕ) < a)) Z := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · simp [h, ddPart, ← SetLike.mem_coe]; tauto
  · simp [h, ddPart, ← SetLike.mem_coe]; tauto

private theorem key (wi r ri w : Matrix (Fin n) (Fin n) A) (Y K : Fin g → Matrix (Fin n) (Fin n) A)
    (h1 : w * wi = 1) (h2 : ri * r = 1) :
    wi.map (algebraMap A (DD X g)) * (1 + DD.epM fun j => (Y j).map (algebraMap A X)) *
      ((1 + DD.epM fun j => (K j).map (algebraMap A X)) * r.map (algebraMap A (DD X g))) *
      ((1 - DD.epM fun j => (Y j).map (algebraMap A X)) * w.map (algebraMap A (DD X g))) =
    (1 + DD.epM fun j => (wi * (K j - (r * Y j * ri - Y j)) * w).map (algebraMap A X)) *
      (wi * r * w).map (algebraMap A (DD X g)) := by
  have e : (DD.epM fun j => (wi * (K j - (r * Y j * ri - Y j)) * w).map (algebraMap A X)) =
      wi.map (algebraMap A (DD X g)) * ((DD.epM fun j => (K j).map (algebraMap A X)) -
        (r.map (algebraMap A (DD X g)) * (DD.epM fun j => (Y j).map (algebraMap A X)) * ri.map (algebraMap A (DD X g)) -
          DD.epM fun j => (Y j).map (algebraMap A X))) * w.map (algebraMap A (DD X g)) := by
    rw [mul_epM, epM_mul, ← epM_sub, ← epM_sub, mul_epM, epM_mul]
    congr 1
    funext j
    simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub (algebraMap A X))]
  have i1 : w.map (algebraMap A (DD X g)) * wi.map (algebraMap A (DD X g)) = 1 := by
    rw [← Matrix.map_mul, h1]; simp
  have i2 : ri.map (algebraMap A (DD X g)) * r.map (algebraMap A (DD X g)) = 1 := by
    rw [← Matrix.map_mul, h2]; simp
  have z1 := epM_mul_epM (fun j => (Y j).map (algebraMap A X)) (fun j => (K j).map (algebraMap A X))
  have z2 : (DD.epM fun j => (Y j).map (algebraMap A X)) * r.map (algebraMap A (DD X g)) *
      (DD.epM fun j => (Y j).map (algebraMap A X)) = 0 := by rw [epM_mul, epM_mul_epM]
  have z3 : (DD.epM fun j => (K j).map (algebraMap A X)) * r.map (algebraMap A (DD X g)) *
      (DD.epM fun j => (Y j).map (algebraMap A X)) = 0 := by rw [epM_mul, epM_mul_epM]
  rw [e, Matrix.map_mul, Matrix.map_mul]
  generalize (DD.epM fun j => (Y j).map (algebraMap A X)) = P at *
  generalize (DD.epM fun j => (K j).map (algebraMap A X)) = Q at *
  generalize wi.map (algebraMap A (DD X g)) = a at *
  generalize w.map (algebraMap A (DD X g)) = b at *
  generalize r.map (algebraMap A (DD X g)) = c at *
  generalize ri.map (algebraMap A (DD X g)) = d at *
  calc a * (1 + P) * ((1 + Q) * c) * ((1 - P) * b)
      = a * (c + Q * c + P * c - c * P + (P * Q) * c * (1 - P) - Q * c * P - P * c * P) * b := by noncomm_ring
    _ = a * (c + Q * c + P * c - c * P * (d * c)) * b := by rw [z1, z2, z3, i2]; noncomm_ring
    _ = a * c * b + a * (Q - (c * P * d - P)) * (b * a) * c * b := by rw [i1]; noncomm_ring
    _ = _ := by noncomm_ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.tri :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (v : F.Vl), (∀ g : F.Gv v, (∀ i j, j < i → (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v) i j = 0) ∧ (∀ i, (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v) i i = algebraMap x.A (DD X k.g) (x.ψ v i g : x.A)) ∧ TyPat (x.ty v) (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v)) ∧ ∀ Z : Matrix (Fin n) (Fin n) (DD X k.g), Z ∈ k.M1 X ↔ TyPat (x.ty v) (k.wi1 X v * Z * k.w1 X v) := by
  intro l _ F n x k X _ _ v
  have od : ∀ M ∈ Od x.A x.A n x.a, ∀ i j : Fin n, decide ((i : ℕ) < x.a) = decide ((j : ℕ) < x.a) →
      M.map (algebraMap x.A X) i j = 0 := fun M hM i j e => by
    have : M i j = 0 := (hM i j).1 (by simpa using e)
    simp [this]
  have hw : Pat (fun i => decide ((i : ℕ) < x.a)) (x.ty v) (k.w1 X v) :=
    (pat_sub _ fun m => od _ (k.Y_mem m v)).mul (pat_map _ (x.w_blk v))
  have hwi : Pat (x.ty v) (fun i => decide ((i : ℕ) < x.a)) (k.wi1 X v) :=
    (pat_map _ (tyCard l F n x v 0).2.2.2).mul (pat_add _ fun m => od _ (k.Y_mem m v))
  obtain ⟨i1, i2⟩ := (rho1 l F n x k X).2.2.2.1 v
  refine ⟨fun g => ?_, fun Z => ?_⟩
  · have hr : Pat (fun i => decide ((i : ℕ) < x.a)) (fun i => decide ((i : ℕ) < x.a)) (k.ρ1 X (F.φ v g)) :=
      (pat_add _ fun m => od _ ((k.mem m).1 _)).mul
        (pat_map _ fun i j e => (x.blk (F.φ v g) i j).2 (by simpa using e))
    have hp : TyPat (x.ty v) (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v) := (hwi.mul hr).mul hw
    have e := key (X := X) (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) (mat x.ρ (F.φ v g))
      (mat x.ρ (F.φ v g)⁻¹) (x.w v : Matrix (Fin n) (Fin n) x.A) (fun j => k.Y j v) (fun j => k.κ j (F.φ v g))
      (Units.mul_inv _) (by simp [mat])
    change k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v = _ at e
    have t1 : ∀ i j, j < i → ((((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) * mat x.ρ (F.φ v g) *
      (x.w v : Matrix (Fin n) (Fin n) x.A)) i j = 0 := (x.tri v g).1
    have t2 : ∀ i, ((((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) * mat x.ρ (F.φ v g) *
      (x.w v : Matrix (Fin n) (Fin n) x.A)) i i = (x.ψ v i g : x.A) := (x.tri v g).2
    have t3 : ∀ m i j, j < i → ((((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) *
      (k.κ m (F.φ v g) - (mat x.ρ (F.φ v g) * k.Y m v * mat x.ρ (F.φ v g)⁻¹ - k.Y m v)) *
      (x.w v : Matrix (Fin n) (Fin n) x.A)) i j = 0 := fun m i j h => by
      have := (k.loc m v g).1 i j h
      simpa only [dY, NP.ρX, NP.wX, NP.wiX, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using this
    generalize (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) * mat x.ρ (F.φ v g) *
      (x.w v : Matrix (Fin n) (Fin n) x.A) = T at e t1 t2
    refine ⟨fun i j h => ?_, fun i => ?_, hp⟩
    · rw [e, add_mul, one_mul, epM_mul]
      have : ∀ (U : Matrix (Fin n) (Fin n) x.A), (∀ i j, j < i → U i j = 0) → (U * T) i j = 0 := fun U hU => by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases hc : c < i
        · rw [hU i c hc, zero_mul]
        · rw [t1 c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
      refine DD.ext ?_ (funext fun m => ?_) (funext fun m => ?_) ?_
      · simp [DD.epM, t1 i j h]
      · simp only [← Matrix.map_mul]
        simp only [DD.epM, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, DD.add_ep, this _ (t3 m), t1 i j h,
          map_zero, DD.zero_ep, add_zero]
      · simp [DD.epM, t1 i j h]
      · simp [DD.epM, t1 i j h]
    · refine DD.ext ?_ ((hp i i).2.2.1 rfl) (hp i i).1 (hp i i).2.1
      rw [e, add_mul, one_mul, epM_mul]
      simp [DD.epM, t2 i]
  · refine (mem_W1_iff_pattern x.a Z).trans ⟨fun h => (hwi.mul h).mul hw, fun h => ?_⟩
    have e : Z = k.w1 X v * (k.wi1 X v * Z * k.w1 X v) * k.wi1 X v := by
      rw [← mul_assoc, ← mul_assoc, i2, one_mul, mul_assoc, i2, mul_one]
    rw [e]
    exact (hw.mul h).mul hwi
