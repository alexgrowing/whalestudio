import Mathlib

open TensorProduct

namespace UpperTheory.V.Loc.Thick

theorem trace_eq {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] [DecidableEq n] (p : R →+* R')
    (hp : ∀ a, p a = 0 → IsNilpotent a) (N : ℕ) (hN : IsUnit (N : R)) (M M' : Matrix n n R)
    (hM : M ^ N = 1) (hM' : M' ^ N = 1) (h : p.mapMatrix M = p.mapMatrix M') : M.trace = M'.trace := by
  rcases N with _ | k
  · haveI : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using isUnit_zero_iff.1 (by simpa using hN))
    exact Subsingleton.elim _ _
  let U : Matrix n n R := ∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 - i)
  have h1 : M * U = U * M' := by
    have e1 : M * U = ∑ i ∈ Finset.range (k + 1), M ^ (i + 1) * M' ^ (k + 1 + 1 - (i + 1)) := by
      simp only [U, Finset.mul_sum, ← mul_assoc, ← pow_succ', Nat.add_sub_add_right]
    have e2 : U * M' = ∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 + 1 - i) := by
      simp only [U, Finset.sum_mul, mul_assoc, ← pow_succ]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      congr 2
      omega
    have e3 := (Finset.sum_range_succ' (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1)).symm.trans
      (Finset.sum_range_succ (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1))
    simp only [hM, pow_zero, one_mul, Nat.sub_zero, pow_succ M' (k + 1), hM', Nat.add_sub_cancel_left,
      pow_one] at e3
    rw [e1, e2]
    exact add_right_cancel e3
  have h2 : p.mapMatrix U = p.mapMatrix (((k + 1 : ℕ) : R) • (1 : Matrix n n R)) := by
    have : ∀ i ∈ Finset.range (k + 1), p.mapMatrix (M ^ i * M' ^ (k + 1 - i)) = 1 := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, h, ← map_pow, ← map_mul, ← pow_add, show i + (k + 1 - i) = k + 1 by omega, hM', map_one]
    rw [map_sum, Finset.sum_congr rfl this, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
    simp
  have h3 : IsUnit U.det := by
    have e : p (U.det - ((k + 1 : ℕ) : R) ^ Fintype.card n) = 0 := by
      rw [map_sub, RingHom.map_det, h2, ← RingHom.map_det, Matrix.det_smul, Matrix.det_one, mul_one, sub_self]
    have := (hp _ e).isUnit_add_right_of_commute (hN.pow (Fintype.card n)) (Commute.all _ _)
    simpa using this
  have h4 : M = U * M' * U⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h3, Matrix.mul_one]
  rw [h4, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h3, Matrix.one_mul]

variable {Q E B : Type} [Field Q] [Field E] [CommRing B] [Algebra Q E] [Algebra Q B] [Algebra E B]
  [IsScalarTower Q E B] (π : B →ₐ[E] E)

theorem step [Module.Finite E B] (hπ : ∀ a, π a = 0 → IsNilpotent a) (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ (J' : Ideal B) (t : B) (f : B →ₗ[E] E), J' < J ∧ t ∈ J ∧ f t = 1 ∧ (∀ j ∈ J, ∀ a, f (a * j) = π a * f j) ∧
      ∀ j ∈ J, f j = 0 → j ∈ J' := by
  haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
  have hn : IsNilpotent (RingHom.ker π) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 fun a ha => hπ a ha
  have h1 : ¬ J ≤ RingHom.ker π * J := by
    intro h
    obtain ⟨k, hk⟩ := hn
    have : ∀ i, J ≤ RingHom.ker π ^ i * J := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => exact ih.trans (by rw [pow_succ, mul_assoc]; exact Ideal.mul_mono_right h)
    exact hJ (by simpa [hk] using this k)
  obtain ⟨t, ht, ht'⟩ := Set.not_subset.1 h1
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (RingHom.ker π * J).restrictScalars E) ht' inferInstance
  have hf0 : ∀ x ∈ RingHom.ker π * J, f x = 0 := fun x hx =>
    (Submodule.mem_bot E).1 (hf ▸ Submodule.mem_map_of_mem hx)
  have hm : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j := by
    intro j hj a
    have := hf0 ((a - algebraMap E B (π a)) * j) (Ideal.mul_mem_mul (by simp [RingHom.mem_ker]) hj)
    rw [sub_mul, map_sub, ← Algebra.smul_def, map_smul, sub_eq_zero] at this
    exact this
  let J' : Ideal B :=
    { carrier := {j | j ∈ J ∧ f j = 0}
      zero_mem' := ⟨J.zero_mem, map_zero f⟩
      add_mem' := fun ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
      smul_mem' := fun c j hj => ⟨J.smul_mem c hj.1, by rw [smul_eq_mul, hm j hj.1, hj.2, mul_zero]⟩ }
  refine ⟨J', t, (f t)⁻¹ • f, lt_of_le_of_ne (fun j hj => hj.1) fun h => hf1 (show t ∈ J' from h ▸ ht).2, ht,
    by simp [hf1], fun j hj a => by simp [hm j hj a, mul_left_comm], fun j hj h => ⟨hj, by simpa [hf1] using h⟩⟩

structure Red {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
    (p : X →ₗ[Q] X') (Λ : (B →ₗ[E] E) → X →ₗ[Q] X') : Prop where
  surj : Function.Surjective p
  smul : ∀ a x, p (a • x) = π a • p x
  ker : ∀ x, p x = 0 → x ∈ (RingHom.ker π • ⊤ : Submodule B X)
  form : ∀ (f : B →ₗ[E] E) j, (∀ a, f (a * j) = π a * f j) → ∀ x, Λ f (j • x) = f j • p x

variable {π}

section

variable {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
  {p : X →ₗ[Q] X'} {Λ : (B →ₗ[E] E) → X →ₗ[Q] X'}

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in
theorem Red.desc (h : Red π p Λ) {J J' : Ideal B} {t : B} {f : B →ₗ[E] E} (ht : t ∈ J)
    (hft : f t = 1) (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j) (hJ : ∀ j ∈ J, f j = 0 → j ∈ J')
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) {x : X} (hx : p x = Λ f y) :
    y - t • x ∈ (J' • ⊤ : Submodule B X) := by
  have h1 : ∃ z, p z = Λ f y ∧ y - t • z ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on hy (fun j hj w _ => ⟨algebraMap E B (f j) • w, ?_, ?_⟩) ?_
    · rw [h.smul, h.form f j (hf j hj)]; simp
    · rw [smul_smul, ← sub_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.sub_mem hj (J.mul_mem_right _ ht)) ?_) trivial
      rw [map_sub, mul_comm, hf t ht, hft]; simp
    · rintro a b ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
      refine ⟨z + w, by rw [map_add, map_add, h1, h3], ?_⟩
      convert Submodule.add_mem _ h2 h4 using 1
      rw [smul_add]; abel
  obtain ⟨z, h1, h2⟩ := h1
  have h3 : t • (z - x) ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on (p := fun w => t • w ∈ (J' • ⊤ : Submodule B X))
      (h.ker (z - x) (by rw [map_sub, h1, hx, sub_self])) (fun j hj w _ => ?_) fun a b ha hb => ?_
    · rw [smul_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.mul_mem_right _ ht) ?_) trivial
      rw [mul_comm, hf t ht, RingHom.mem_ker.1 hj, zero_mul]
    · rw [smul_add]; exact Submodule.add_mem _ ha hb
  convert Submodule.add_mem _ h2 h3 using 1
  rw [smul_sub]; abel

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in

theorem lift_param [Module.Finite E B] (hπ : ∀ a, π a = 0 → IsNilpotent a)
    {C C' : Type} [AddCommGroup C] [Module B C] [Module Q C] [AddCommGroup C'] [Module E C'] [Module Q C']
    {q : C →ₗ[Q] C'} {Γ : (B →ₗ[E] E) → C →ₗ[Q] C'} (hX : Red π p Λ) (hC : Red π q Γ)
    (φ : C →ₗ[B] X) (φ' : C' →ₗ[E] X') (hφ : ∀ c, p (φ c) = φ' (q c))
    (S T : Submodule B X) (S' T' : Submodule E X') (hTS : T ≤ S) (hφS : ∀ c, φ c ∈ S)
    (hT : ∀ y ∈ T', ∃ x ∈ T, p x = y)
    (hΛ : ∀ (f : B →ₗ[E] E) (J : Ideal B), (∀ j ∈ J, ∀ a, f (a * j) = π a * f j) →
      ∀ y ∈ (J • ⊤ : Submodule B X), (y ∈ S → Λ f y ∈ S') ∧ (y ∈ T → Λ f y ∈ T'))
    (h : ∀ y ∈ S', ∃! c, y - φ' c ∈ T') : ∀ y ∈ S, ∃! c, y - φ c ∈ T := by
  haveI : IsArtinianRing B := isArtinian_of_tower E inferInstance
  have hs : ∀ J : Ideal B, ∀ y ∈ S, y ∈ (J • ⊤ : Submodule B X) → ∃ c, y - φ c ∈ T := by
    intro J
    induction J using WellFoundedLT.induction with
    | ind J ih =>
    intro y hy hyJ
    by_cases hJ : J = ⊥
    · refine ⟨0, ?_⟩
      rw [hJ, Submodule.bot_smul, Submodule.mem_bot] at hyJ
      simp [hyJ]
    obtain ⟨J', t, f, hlt, ht, hft, hf, hJ'⟩ := step π hπ J hJ
    obtain ⟨c', hc', -⟩ := h _ ((hΛ f J hf y hyJ).1 hy)
    obtain ⟨z, hz, e⟩ := hT _ hc'
    obtain ⟨c, rfl⟩ := hC.surj c'
    obtain ⟨d, hd⟩ := ih J' hlt (y - t • (φ c + z))
      (S.sub_mem hy (S.smul_mem _ (S.add_mem (hφS c) (hTS hz))))
      (hX.desc ht hft hf hJ' hyJ (by rw [map_add, hφ, e]; abel))
    refine ⟨d + t • c, ?_⟩
    convert T.add_mem hd (T.smul_mem t hz) using 1
    rw [map_add, map_smul, smul_add]; abel
  have hi : ∀ J : Ideal B, ∀ c ∈ (J • ⊤ : Submodule B C), φ c ∈ T → c = 0 := by
    intro J
    induction J using WellFoundedLT.induction with
    | ind J ih =>
    intro c hc hcT
    by_cases hJ : J = ⊥
    · rwa [hJ, Submodule.bot_smul, Submodule.mem_bot] at hc
    obtain ⟨J', t, f, hlt, ht, hft, hf, hJ'⟩ := step π hπ J hJ
    have e : Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X) := by
      refine Submodule.smul_induction_on
        (p := fun c => Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X)) hc
        (fun j hj w _ => ⟨?_, ?_⟩) fun a b ha hb => ⟨?_, ?_⟩
      · rw [map_smul, hX.form f j (hf j hj), hC.form f j (hf j hj), map_smul, hφ]
      · rw [map_smul]; exact Submodule.smul_mem_smul hj trivial
      · simp only [map_add, ha.1, hb.1]
      · rw [map_add]; exact Submodule.add_mem _ ha.2 hb.2
    have e2 : Γ f c = 0 := (h 0 S'.zero_mem).unique
      (by rw [← e.1, zero_sub]; exact T'.neg_mem ((hΛ f J hf _ e.2).2 hcT)) (by simp)
    refine ih J' hlt c ?_ hcT
    simpa using hC.desc ht hft hf hJ' hc (x := 0) (by rw [e2, map_zero])
  intro y hy
  obtain ⟨c, hc⟩ := hs ⊤ y hy (by simp)
  refine ⟨c, hc, fun d hd => sub_eq_zero.1 (hi ⊤ _ (by simp) ?_)⟩
  convert T.sub_mem hc hd using 1
  rw [map_sub]; abel

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in
theorem Red.pi (h : Red π p Λ) (n : Type) [Fintype n] : Red π (p.compLeft n) fun f => (Λ f).compLeft n where
  surj y := by
    choose x hx using fun i => h.surj (y i)
    exact ⟨x, funext hx⟩
  smul a x := funext fun i => h.smul a (x i)
  ker x hx := by
    classical
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.smul_induction_on
      (p := fun w => (Pi.single i w : n → X) ∈ (RingHom.ker π • ⊤ : Submodule B (n → X)))
      (h.ker (x i) (congrFun hx i)) (fun j hj w _ => ?_) fun a b ha hb => ?_
    · rw [Pi.single_smul]; exact Submodule.smul_mem_smul hj trivial
    · rw [Pi.single_add]; exact Submodule.add_mem _ ha hb
  form f j hf x := funext fun i => h.form f j hf (x i)

variable [IsScalarTower Q B X] [IsScalarTower Q E X']

omit [IsScalarTower Q E B] in
theorem Red.tensor (h : Red π p Λ) (P : Type) [AddCommGroup P] [Module Q P] :
    Red π (p.rTensor P) fun f => (Λ f).rTensor P where
  surj := LinearMap.rTensor_surjective P h.surj
  smul a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp only [smul_tmul', LinearMap.rTensor_tmul, h.smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  ker x hx := by
    obtain ⟨y, rfl⟩ := (rTensor_exact P (LinearMap.exact_subtype_ker_map p) h.surj x).1 hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [LinearMap.rTensor_tmul]
      refine Submodule.smul_induction_on
        (p := fun w => w ⊗ₜ[Q] b ∈ (RingHom.ker π • ⊤ : Submodule B (X ⊗[Q] P)))
        (h.ker v v.2) (fun j hj w _ => ?_) fun a b ha hb => ?_
      · rw [← smul_tmul']; exact Submodule.smul_mem_smul hj trivial
      · rw [add_tmul]; exact Submodule.add_mem _ ha hb
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  form f j hf x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp only [smul_tmul', LinearMap.rTensor_tmul, h.form f j hf]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] [IsScalarTower Q B X] [IsScalarTower Q E X'] in
theorem Red.comm (h : Red π p Λ) (g : X →ₗ[B] X) (g' : X' →ₗ[E] X') (hg : ∀ x, p (g x) = g' (p x))
    {f : B →ₗ[E] E} {J : Ideal B} (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j)
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) : Λ f (g y) = g' (Λ f y) := by
  refine Submodule.smul_induction_on (p := fun y => Λ f (g y) = g' (Λ f y)) hy (fun j hj w _ => ?_)
    fun a b ha hb => ?_
  · rw [map_smul, h.form f j (hf j hj), h.form f j (hf j hj), map_smul, hg]
  · simp only [map_add, ha, hb]

end

variable (Q π) in
theorem red_self : Red π (π.toLinearMap.restrictScalars Q) fun f => f.restrictScalars Q where
  surj y := ⟨algebraMap E B y, by simp⟩
  smul a x := by simp
  ker x hx := by
    have := Submodule.smul_mem_smul (I := RingHom.ker π) (N := (⊤ : Submodule B B)) (r := x) (n := 1) hx trivial
    simpa using this
  form f j hf x := by
    change f (j * x) = f j * π x
    rw [mul_comm j, hf, mul_comm]

section Sm

variable {A V : Type} [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V]
  {F P : Type} [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]

variable (V P) in

noncomputable def sm : A ⊗[Q] F →ₗ[Q] Module.End Q (V ⊗[Q] P) :=
  (TensorProduct.homTensorHomMap (RingHom.id Q) V P V P).comp
    (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap
      (Algebra.lsmul Q Q P : F →ₐ[Q] Module.End Q P).toLinearMap)

theorem sm_tmul (a : A) (k : F) (v : V) (b : P) : sm V P (a ⊗ₜ[Q] k) (v ⊗ₜ[Q] b) = (a • v) ⊗ₜ[Q] (k • b) := by
  simp [sm]

theorem sm_mul (c d : A ⊗[Q] F) (y : V ⊗[Q] P) : sm V P (c * d) y = sm V P c (sm V P d y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy]
  | tmul a' k' =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [Algebra.TensorProduct.tmul_mul_tmul, sm_tmul, mul_smul]

theorem sm_left (a : A) (y : V ⊗[Q] P) : sm V P (a ⊗ₜ[Q] (1 : F)) y = a • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul v b => simp only [sm_tmul, one_smul, smul_tmul']

theorem sm_one (y : V ⊗[Q] P) : sm V P (1 : A ⊗[Q] F) y = y := by
  rw [Algebra.TensorProduct.one_def, sm_left, one_smul]

theorem sm_smul (a : A) (c : A ⊗[Q] F) (y : V ⊗[Q] P) : sm V P (a • c) y = a • sm V P c y := by
  rw [Algebra.smul_def, sm_mul, Algebra.TensorProduct.algebraMap_apply, sm_left]
  rfl

theorem act_sm (g : V →ₗ[A] V) (u : P →ₗ[Q] P) (hu : ∀ (k : F) b, u (k • b) = k • u b) (c : A ⊗[Q] F)
    (y : V ⊗[Q] P) :
    AlgebraTensorModule.map g u (sm V P c y) = sm V P c (AlgebraTensorModule.map g u y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [sm_tmul, AlgebraTensorModule.map_tmul, map_smul, hu]

theorem sm_mem_range (Φ : Submodule Q P) (hΦ : ∀ (k : F), ∀ b ∈ Φ, k • b ∈ Φ) (c : A ⊗[Q] F) {y : V ⊗[Q] P}
    (hy : y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype)) :
    sm V P c y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype) := by
  obtain ⟨y, rfl⟩ := hy
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | tmul v b => exact ⟨(a • v) ⊗ₜ ⟨k • b.1, hΦ k _ b.2⟩, by simp [sm_tmul]⟩

noncomputable def par (F : Type) [Field F] [Algebra Q F] [Algebra F P] [IsScalarTower Q F P] {ι : Type} [Fintype ι]
    (x : ι → V ⊗[Q] P) : (ι → A ⊗[Q] F) →ₗ[A] V ⊗[Q] P where
  toFun c := ∑ a, sm V P (c a) (x a)
  map_add' c d := by simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, sm_smul, Finset.smul_sum, RingHom.id_apply]

variable {A' V' : Type} [CommRing A'] [Algebra Q A'] [AddCommGroup V'] [Module A' V'] [Module Q V']
  [IsScalarTower Q A' V']

theorem rTensor_sm (q : A →ₗ[Q] A') (p : V →ₗ[Q] V') (hp : ∀ a v, p (a • v) = q a • p v) (c : A ⊗[Q] F)
    (y : V ⊗[Q] P) : p.rTensor P (sm V P c y) = sm V' P (q.rTensor F c) (p.rTensor P y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [sm_tmul, LinearMap.rTensor_tmul, hp]

omit [Algebra Q P] in
theorem rTensor_act [Module Q P] (p : V →ₗ[Q] V') (g : V →ₗ[A] V) (g' : V' →ₗ[A'] V')
    (hp : ∀ v, p (g v) = g' (p v)) (u : P →ₗ[Q] P) (y : V ⊗[Q] P) :
    p.rTensor P (AlgebraTensorModule.map g u y) = AlgebraTensorModule.map g' u (p.rTensor P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [AlgebraTensorModule.map_tmul, LinearMap.rTensor_tmul, hp]

theorem rTensor_mem_range (p : V →ₗ[Q] V') (Φ : Submodule Q P) {y : V ⊗[Q] P}
    (hy : y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype)) :
    p.rTensor P y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[A'] V') Φ.subtype) := by
  obtain ⟨y, rfl⟩ := hy
  refine ⟨p.rTensor _ y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp

end Sm

end UpperTheory.V.Loc.Thick
