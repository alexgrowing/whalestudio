import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.B2

section

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

def mk2 (P : Fin g → Matrix (Fin n) (Fin n) X) (Z : Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨0, 0, fun j => P j a b, Z a b⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (AddMonoidHom.mk' DD.a DD.add_a) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep j) fun x y => DD.add_ep x y j) f s

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep' j) fun x y => DD.add_ep' x y j) f s

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta :=
  map_sum (AddMonoidHom.mk' DD.eta DD.add_eta) f s

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

theorem epsPrimeEtaMatrix_add (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z + mk2 P' Z' = mk2 (fun j => P j + P' j) (Z + Z') := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_sub (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z - mk2 P' Z' = mk2 (fun j => P j - P' j) (Z - Z') := by
  ext a b <;> simp [mk2, sub_eq_add_neg]

theorem epsPrimeEtaMatrix_smul (c : A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    c • mk2 P Z = mk2 (fun j => c • P j) (c • Z) := by
  ext a b <;> simp [mk2, Algebra.smul_def, alg_eq]

theorem neg_transpose_epsPrimeEtaMatrix (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    -(mk2 P Z)ᵀ = mk2 (fun j => -(P j)ᵀ) (-Zᵀ) := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_apply_eq_zero_iff {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} {a b} :
    mk2 P Z a b = 0 ↔ (∀ j, P j a b = 0) ∧ Z a b = 0 :=
  ⟨fun h => ⟨fun j => congrArg (fun d : DD X g => d.ep' j) h, congrArg DD.eta h⟩,
    fun h => DD.ext rfl rfl (funext h.1) h.2⟩

theorem epsPrimeEtaMatrix_injective_pair {P P' : Fin g → Matrix (Fin n) (Fin n) X} {Z Z'} (h : mk2 P Z = mk2 P' Z') : P = P' ∧ Z = Z' :=
  ⟨funext fun j => Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).ep' j) h,
    Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).eta) h⟩

theorem evenOddBlockMatrix_mem_adjointDeformSubspace {a : ℕ} {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} (hP : ∀ j, P j ∈ Ev A X n a)
    (hZ : Z ∈ Od A X n a) : mk2 P Z ∈ W2 n A X g a := fun i j =>
  ⟨fun e => ⟨fun _ => rfl, fun _ => rfl, fun h => by simp at h, fun _ => (hZ i j).1 e⟩,
    fun e => ⟨fun _ => rfl, fun _ => rfl, fun _ => funext fun m => (hP m i j).2 e, fun h => by simp at h⟩⟩

theorem exists_evenOddBlock_decomposition_of_mem {a : ℕ} {M : Matrix (Fin n) (Fin n) (DD X g)} (h : M ∈ W2 n A X g a) :
    ∃ P Z, (∀ j, P j ∈ Ev A X n a) ∧ Z ∈ Od A X n a ∧ M = mk2 P Z := by
  refine ⟨fun j => M.map fun d => d.ep' j, M.map DD.eta, fun m i j => ⟨fun _ => trivial, fun e => ?_⟩,
    fun i j => ⟨fun e => ((h i j).1 e).2.2.2 rfl, fun _ => trivial⟩, Matrix.ext fun i j => ?_⟩
  · exact congrFun (((h i j).2 e).2.2.1 rfl) m
  · by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact DD.ext (((h i j).1 e).1 rfl) (((h i j).1 e).2.1 rfl) rfl rfl
    · exact DD.ext (((h i j).2 e).1 rfl) (((h i j).2 e).2.1 rfl) rfl rfl

theorem algebraMap_matrix_mul_epsPrimeEtaMatrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    M.map (algebraMap A (DD X g)) * mk2 P Z =
      mk2 (fun j => M.map (algebraMap A X) * P j) (M.map (algebraMap A X) * Z) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epsPrimeEtaMatrix_mul_algebraMap_matrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * M.map (algebraMap A (DD X g)) =
      mk2 (fun j => P j * M.map (algebraMap A X)) (Z * M.map (algebraMap A X)) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epM_mul_epsPrimeEtaMatrix (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    DD.epM Y * mk2 P Z = mk2 (fun _ => 0) (∑ j, Y j * P j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

theorem epsPrimeEtaMatrix_mul_epM (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * DD.epM Y = mk2 (fun _ => 0) (∑ j, P j * Y j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

private theorem ev_od {a : ℕ} {P Y : Matrix (Fin n) (Fin n) X} (hP : P ∈ Ev A X n a) (hY : Y ∈ Od A X n a) :
    Y * P - P * Y ∈ Od A X n a := by
  refine sub_mem (fun i j => ⟨fun e => ?_, fun _ => trivial⟩) (fun i j => ⟨fun e => ?_, fun _ => trivial⟩)
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY i c).1 h), zero_mul]
    · rw [(Submodule.mem_bot A).1 ((hP c j).2 (by tauto)), mul_zero]
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY c j).1 (by tauto)), mul_zero]
    · rw [(Submodule.mem_bot A).1 ((hP i c).2 h), zero_mul]

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

theorem rho1_conj_block_matrix (g g' : F.G₀) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    ∃ Z', k.ρ1 X g * mk2 P Z * k.ρ1 X g' = mk2 (fun j => x.ρX X g * P j * x.ρX X g') Z' := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp only [add_zero]
  exact ⟨_, rfl⟩

theorem rho1_conj_block_zero (g g' : F.G₀) (Z) :
    k.ρ1 X g * mk2 (fun _ => 0) Z * k.ρ1 X g' = mk2 (fun _ => 0) (x.ρX X g * Z * x.ρX X g') := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp

noncomputable def cmm (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) X :=
  ∑ j, ((k.Y j v).map (algebraMap x.A X) * P j - P j * (k.Y j v).map (algebraMap x.A X))

theorem weyl_conj_block_matrix (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    k.wi1 X v * mk2 P Z * k.w1 X v =
      mk2 (fun j => x.wiX X v * P j * x.wX X v) (x.wiX X v * (Z + cmm k X v P) * x.wX X v) := by
  simp only [Kap.w1, Kap.wi1, NP.wX, NP.wiX, cmm]
  rw [mul_assoc _ (1 + _), add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, mul_assoc, ← mul_assoc (mk2 _ _), mul_sub, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_sub, epsPrimeEtaMatrix_mul_algebraMap_matrix, algebraMap_matrix_mul_epsPrimeEtaMatrix]
  simp only [add_zero, sub_zero, Finset.sum_sub_distrib, mul_assoc, add_sub_assoc]

theorem cmm_mem (v : F.Vl) {P : Fin k.g → Matrix (Fin n) (Fin n) X} (hP : ∀ j, P j ∈ Ev x.A X n x.a) :
    cmm k X v P ∈ Od x.A X n x.a :=
  Submodule.sum_mem _ fun j _ => ev_od (hP j) fun a b => ⟨fun e => by
    have : k.Y j v a b = 0 := (k.Y_mem j v a b).1 e
    simp [this], fun _ => trivial⟩

theorem od_diag (v : F.Vl) {Z : Matrix (Fin n) (Fin n) X} (hZ : Z ∈ Od x.A X n x.a) (i : Fin n) :
    (x.wiX X v * Z * x.wX X v) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : decide ((b : ℕ) < x.a) = x.ty v i
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    by_cases ha : x.ty v i = decide ((a : ℕ) < x.a)
    · rw [(Submodule.mem_bot x.A).1 ((hZ a b).1 (by simpa using (hb.trans ha).symm)), mul_zero]
    · have := (tyCard l F n x v 0).2.2.2 i a ha
      simp only [NP.wiX, Matrix.map_apply, this, map_zero, zero_mul]
  · simp only [NP.wX, Matrix.map_apply, x.w_blk v b i hb, map_zero, mul_zero]

theorem isLocallyConstant_rho1_of_algebraMap_pow_eq_zero (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) : IsLocallyConstant (k.ρ1 X) := by
  have aux : ∀ f : F.G₀ → Matrix (Fin n) (Fin n) x.A,
      (∀ i j, AdicCont (Ideal.span {x.t}) fun g => f g i j) → ∀ (R : Type) [CommRing R] [Algebra x.A R],
      algebraMap x.A R (x.t ^ m) = 0 → ∀ g0, ∀ᶠ g in nhds g0, (f g).map (algebraMap x.A R) = (f g0).map (algebraMap x.A R) := by
    intro f hf R _ _ hR g0
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j m).eventually_eq g0]
      with g hg
    refine Matrix.ext fun i j => ?_
    have h2 := Ideal.Quotient.eq.1 (hg i j)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 := congrArg (algebraMap x.A R) hc
    rw [map_sub, map_mul, hR, zero_mul, sub_eq_zero] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  filter_upwards [Filter.eventually_all.2 fun j => aux (k.κ j) (k.mem j).2.1 X hm g0,
    aux (mat x.ρ) (by rw [← PowerSeries.maximalIdeal_eq_span_X]; exact x.cont) (DD X k.g)
      (by rw [alg_eq, hm, map_zero]) g0] with g h1 h2
  simp only [Kap.ρ1, NP.ρX, h1, h2]

end UpperTheory.V.Pa.B2
