import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterB

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem lin_comp {R : Type} [CommRing R] {k : ℕ} (M N : Matrix (Fin k) (Fin k) R) (P : MvPolynomial (Fin k) R) :
    lin M (lin N P) = lin (N * M) P := by
  simp only [lin]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (Fin k) R => F P)
  congr 1
  funext c
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem lin_one {R : Type} [CommRing R] {k : ℕ} (P : MvPolynomial (Fin k) R) : lin (1 : Matrix (Fin k) (Fin k) R) P = P := by
  simp [lin, Matrix.one_apply]

theorem mono_eq {R : Type} [CommRing R] {σ : Type} [Fintype σ] (μ : σ →₀ ℕ) :
    (monomial μ (1 : R)) = ∏ v, X v ^ μ v := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

theorem scaleHd {R : Type} [CommRing R] {k d : ℕ} (q : MvPolynomial (Fin k) R) (P : MvPolynomial (Fin k) R)
    (hP : P ∈ Hd R k d) : aeval (fun c => q * X c) P = q ^ d * P := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  conv_lhs => rw [MvPolynomial.as_sum P]
  conv_rhs => rw [MvPolynomial.as_sum P]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∑ c, μ c = d := hP hμ
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
  ring

theorem lin_smul {R : Type} [CommRing R] {k d : ℕ} (a : R) (M : Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : lin (a • M) P = a ^ d • lin M P := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  simp only [lin]
  conv_lhs => rw [MvPolynomial.as_sum P]
  conv_rhs => rw [MvPolynomial.as_sum P]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∑ c, μ c = d := hP hμ
  have e : ∀ c, (∑ b, C ((a • M) c b) * X b : MvPolynomial (Fin k) R) = C a * ∑ b, C (M c b) * X b := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [e, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_pow]
  ring

theorem lin_Hd {R : Type} [CommRing R] {k d : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : lin M P ∈ Hd R k d := by
  unfold Hd at hP
  rw [restrictSupport_eq_span] at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    have hμ' : ∑ c, μ c = d := hμ
    beta_reduce
    rw [mono_eq, map_prod, ← hμ']
    apply Hd_prod
    intro c _
    rw [map_pow]
    have h1 : lin M (X c) ∈ Hd R k 1 := by
      simp only [lin, aeval_X]
      exact Submodule.sum_mem _ fun b _ => Hd_X R k _ b
    have h2 := Hd_prod (Finset.range (μ c)) (fun _ => 1) (fun _ => lin M (X c)) (fun _ _ => h1)
    simpa using h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem map_Nv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    map f (Nv R m vec c) = Nv R' m vec c := by
  simp only [Nv]
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    have h1 : (MvPolynomial.map f).mapMatrix (genM R m) = genM R' m := by
      ext i j
      simp [genM]
    rw [← h1, ← RingHom.map_adjugate]
    rfl
  · simp

theorem map_theta {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (m : ℕ) (vec : Bool)
    (P : MvPolynomial (Fin (m + 1)) R) : map f (theta R m vec P) = theta R' m vec (map f P) := by
  simp only [theta, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.map_eval₂]
  congr 2
  funext c
  exact map_Nv f m vec c

theorem map_Hd {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {k d : ℕ}
    (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k d) : map f P ∈ Hd R' k d := by
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  exact (Finset.coe_subset.mpr (MvPolynomial.support_map_subset f P)).trans hP

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

def embS (R : Type) [CommRing R] {k : ℕ} (s : S) : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R :=
  rename fun c => (s, c)

def Th0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × Fin (m + 1)) R →ₐ[R] MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

theorem Th0_emb (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) (s : S) (P : MvPolynomial (Fin (m + 1)) R) :
    Th0 R m vec (embS R s P) = blockEmb R s (theta R m (vec s) P) := by
  simp only [Th0, embS, MvPolynomial.aeval_rename, theta]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

def Lin {R : Type} [CommRing R] {k : ℕ} (N : S → Matrix (Fin k) (Fin k) R) :
    MvPolynomial (S × Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R :=
  aeval fun v => ∑ b, C (N v.1 v.2 b) * X (v.1, b)

theorem Lin_emb {R : Type} [CommRing R] {k : ℕ} (N : S → Matrix (Fin k) (Fin k) R) (s : S)
    (P : MvPolynomial (Fin k) R) : Lin N (embS R s P) = embS R s (lin (N s) P) := by
  simp only [Lin, embS, lin, MvPolynomial.aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R => F P)
  congr 1
  funext c
  simp [Function.comp]

theorem Lin_comp {R : Type} [CommRing R] {k : ℕ} (M N : S → Matrix (Fin k) (Fin k) R)
    (P : MvPolynomial (S × Fin k) R) : Lin M (Lin N P) = Lin (fun s => N s * M s) P := by
  simp only [Lin]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  apply congrArg (fun F : MvPolynomial (S × Fin k) R →ₐ[R] MvPolynomial (S × Fin k) R => F P)
  congr 1
  funext v
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem Lin_one {R : Type} [CommRing R] {k : ℕ} (P : MvPolynomial (S × Fin k) R) :
    Lin (fun _ : S => (1 : Matrix (Fin k) (Fin k) R)) P = P := by
  simp [Lin, Matrix.one_apply]

theorem mem_Pol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} {F : MvPolynomial (S × Fin k) R} :
    F ∈ Pol R k d ↔ ∀ μ ∈ F.support, ∀ i, multideg μ i = d i := by
  exact Iff.rfl

theorem Pol_one (R : Type) [CommRing R] (k : ℕ) : (1 : MvPolynomial (S × Fin k) R) ∈ Pol R k (0 : S → ℕ) := by
  rw [mem_Pol]
  intro μ hμ i
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hμ
  split_ifs at hμ with h
  · subst h
    simp [multideg]
  · exact absurd rfl hμ

theorem Pol_mul {R : Type} [CommRing R] {k : ℕ} {a b : S → ℕ} {P Q : MvPolynomial (S × Fin k) R}
    (hP : P ∈ Pol R k a) (hQ : Q ∈ Pol R k b) : P * Q ∈ Pol R k (a + b) := by
  rw [mem_Pol] at hP hQ ⊢
  intro μ hμ i
  classical
  obtain ⟨a', ha, b', hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hμ)
  have e1 := hP a' ha i
  have e2 := hQ b' hb i
  simp only [multideg] at e1 e2 ⊢
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, e1, e2]

theorem Pol_prod {R : Type} [CommRing R] {k : ℕ} {J : Type} (s : Finset J) (δ : J → S → ℕ)
    (q : J → MvPolynomial (S × Fin k) R) (h : ∀ i ∈ s, q i ∈ Pol R k (δ i)) :
    ∏ i ∈ s, q i ∈ Pol R k (∑ i ∈ s, δ i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (Pol_one (S := S) R k)
  · intro j s hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact Pol_mul (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem emb_Pol {R : Type} [CommRing R] {k a : ℕ} (s : S) (P : MvPolynomial (Fin k) R) (hP : P ∈ Hd R k a) :
    embS R s P ∈ Pol R k (Pi.single s a : S → ℕ) := by
  rw [mem_Pol]
  intro μ hμ i
  have hinj : Function.Injective fun c : Fin k => (s, c) := fun a b h => (Prod.mk.inj h).2
  simp only [embS] at hμ
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hμ
  obtain ⟨ν, hν, rfl⟩ := hμ
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff] at hP
  have hd : ∑ c, ν c = a := hP hν
  simp only [multideg]
  by_cases hi : i = s
  · subst hi
    simp only [Pi.single_eq_same]
    rw [← hd]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply hinj ν c
  · rw [Pi.single_eq_of_ne hi]
    exact Finset.sum_eq_zero fun c _ => Finsupp.mapDomain_notin_range _ _
      (by rintro ⟨c', hc'⟩; exact hi (congrArg Prod.fst hc').symm)

theorem prod_emb_Pol {R : Type} [CommRing R] {k : ℕ} (d : S → ℕ) (P : S → MvPolynomial (Fin k) R)
    (hP : ∀ s, P s ∈ Hd R k (d s)) : ∏ s, embS R s (P s) ∈ Pol R k d := by
  have := Pol_prod Finset.univ (fun s => (Pi.single s (d s) : S → ℕ)) (fun s => embS R s (P s))
    (fun s _ => emb_Pol s (P s) (hP s))
  rwa [Finset.univ_sum_single] at this

def partS {k : ℕ} (μ : S × Fin k →₀ ℕ) (s : S) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun c => μ (s, c)

theorem mono_factor (R : Type) [CommRing R] {k : ℕ} (μ : S × Fin k →₀ ℕ) :
    (monomial μ (1 : R)) = ∏ s, embS R s (monomial (partS μ s) 1) := by
  rw [mono_eq, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [mono_eq, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp [embS, partS]

theorem partS_Hd (R : Type) [CommRing R] {k : ℕ} (d : S → ℕ) (μ : S × Fin k →₀ ℕ) (hμ : ∀ i, multideg μ i = d i)
    (s : S) : (monomial (partS μ s) (1 : R)) ∈ Hd R k (d s) := by
  classical
  simp only [Hd, MvPolynomial.mem_restrictSupport_iff]
  intro ν hν
  have := MvPolynomial.support_monomial_subset hν
  rw [Finset.mem_singleton] at this
  subst this
  show ∑ c, partS μ s c = d s
  rw [← hμ s]
  simp [partS, multideg]

theorem scalePol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (Q : S → MvPolynomial (S × Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) :
    aeval (fun v : S × Fin k => Q v.1 * X v) F = (∏ s, Q s ^ d s) * F := by
  classical
  rw [mem_Pol] at hF
  conv_lhs => rw [MvPolynomial.as_sum F]
  conv_rhs => rw [MvPolynomial.as_sum F]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∀ s, ∑ c, μ (s, c) = d s := fun s => hF μ hμ s
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type (fun v => Q v.1 ^ μ v)]
  simp only [Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem Lin_Pol {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (N : S → Matrix (Fin k) (Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) : Lin N F ∈ Pol R k d := by
  unfold Pol at hF
  rw [restrictSupport_eq_span] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, rfl⟩ := hx
    beta_reduce
    rw [mono_factor, map_prod]
    simp only [Lin_emb]
    exact prod_emb_Pol d _ fun s => lin_Hd _ _ (partS_Hd R d μ hμ s)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem Lin_smul {R : Type} [CommRing R] {k : ℕ} {d : S → ℕ} (a : S → R) (M : S → Matrix (Fin k) (Fin k) R)
    (F : MvPolynomial (S × Fin k) R) (hF : F ∈ Pol R k d) :
    Lin (fun s => a s • M s) F = (∏ s, a s ^ d s) • Lin M F := by
  classical
  rw [mem_Pol] at hF
  simp only [Lin]
  conv_lhs => rw [MvPolynomial.as_sum F]
  conv_rhs => rw [MvPolynomial.as_sum F]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hd : ∀ s, ∑ c, μ (s, c) = d s := fun s => hF μ hμ s
  have e : ∀ v : S × Fin k, (∑ b, C ((a v.1 • M v.1) v.2 b) * X (v.1, b) : MvPolynomial (S × Fin k) R) =
      C (a v.1) * ∑ b, C (M v.1 v.2 b) * X (v.1, b) := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [e, mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type (fun v => C (a v.1) ^ μ v)]
  simp only [Finset.prod_pow_eq_pow_sum, hd]
  rw [MvPolynomial.smul_eq_C_mul, map_prod]
  simp only [MvPolynomial.C_pow]
  ring

def Ps0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R →ₐ[R] MvPolynomial (S × Fin (m + 1)) R :=
  aeval fun v => embS R v.1 (psi R m (vec v.1) (X v.2))

theorem Ps0_block (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) (s : S)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :
    Ps0 R m vec (blockEmb R s F) = embS R s (psi R m (vec s) F) := by
  simp only [Ps0, blockEmb, MvPolynomial.aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.aeval_unique ((embS R s).comp (psi R m (vec s)))]
  rfl

theorem polynomial_theta_product (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (F : MvPolynomial (S × Fin (m + 1)) R) (hF : F ∈ Pol R (m + 1) d) :
    Ps0 R m vec (Th0 R m vec F) = (∏ s, (embS R s (qf R m (vec s))) ^ d s) * F := by
  have h1 : (Ps0 R m vec).comp (Th0 R m vec) =
      aeval fun v : S × Fin (m + 1) => embS R v.1 (qf R m (vec v.1)) * X v := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, Th0, aeval_X, Ps0_block, psi_Nv R m hm, map_mul]
    simp [embS]
  rw [← scalePol _ _ hF, ← h1]
  rfl

theorem qf_ne (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (vec : Bool) : qf R m vec ≠ 0 := by
  simp only [qf]
  cases vec <;> simp [MvPolynomial.X_ne_zero]

theorem Th0_inj (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : S → Bool) (d : S → ℕ)
    (F G : MvPolynomial (S × Fin (m + 1)) R) (hF : F ∈ Pol R (m + 1) d) (hG : G ∈ Pol R (m + 1) d)
    (h : Th0 R m vec F = Th0 R m vec G) : F = G := by
  have h1 := polynomial_theta_product R m hm vec d F hF
  have h2 := polynomial_theta_product R m hm vec d G hG
  rw [h, h2] at h1
  refine (mul_left_cancel₀ ?_ h1).symm
  apply Finset.prod_ne_zero_iff.2
  intro s _
  apply pow_ne_zero
  intro h0
  apply qf_ne R m (vec s)
  have hinj : Function.Injective (fun c : Fin (m + 1) => (s, c)) := fun a b h => (Prod.mk.inj h).2
  exact rename_injective _ hinj (by rw [map_zero]; exact h0)

end Multi

end Formalism.L2.G.Model
