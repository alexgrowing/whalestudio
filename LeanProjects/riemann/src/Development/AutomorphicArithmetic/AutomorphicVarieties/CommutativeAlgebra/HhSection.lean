import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ContSection
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add, z2, add_zero, this]

open Matrix Classical in
private theorem inv_supp {O : Type} [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
    (Φ : FormData O w) (a c : ι) (h : Φ.J⁻¹ a c ≠ 0) : Φ.blk c = Φ.σ (Φ.blk a) ∧ w a + w c = Φ.c := by
  have hd : IsUnit Φ.J.det := (Matrix.isUnit_iff_isUnit_det _).1 Φ.unit
  let E : Matrix ι ι O := diagonal fun x => if Φ.blk x = Φ.blk a ∧ w x = w a then 1 else 0
  let E' : Matrix ι ι O := diagonal fun x => if Φ.blk x = Φ.σ (Φ.blk a) ∧ w a + w x = Φ.c then 1 else 0
  have e : E' * Φ.J = Φ.J * E := by
    ext x y
    simp only [E, E', diagonal_mul, mul_diagonal]
    by_cases hxy : Φ.J x y = 0
    · simp [hxy]
    · have h1 := Φ.hblk x y hxy
      have h2 := Φ.hw x y hxy
      have : (Φ.blk x = Φ.σ (Φ.blk a) ∧ w a + w x = Φ.c) ↔ (Φ.blk y = Φ.blk a ∧ w y = w a) := by
        constructor
        · rintro ⟨k1, k2⟩
          refine ⟨by rw [h1, k1, Φ.invol], ?_⟩
          rw [← h2, add_comm] at k2
          exact (add_left_cancel k2).symm
        · rintro ⟨k1, k2⟩
          refine ⟨by rw [← k1, h1, Φ.invol], ?_⟩
          rw [← k2, add_comm, h2]
      simp only [this, mul_comm]
  have e2 : Φ.J⁻¹ * E' = E * Φ.J⁻¹ := by
    calc Φ.J⁻¹ * E' = Φ.J⁻¹ * (E' * Φ.J) * Φ.J⁻¹ := by
          rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
      _ = E * Φ.J⁻¹ := by rw [e, ← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul]
  have e3 := congrFun (congrFun e2 a) c
  simp only [E, E', diagonal_mul, mul_diagonal, and_self, if_true, one_mul] at e3
  by_contra n
  rw [if_neg n, mul_zero] at e3
  exact h e3.symm

open Matrix Classical in
private theorem fix_point {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup X] {w : ι → X} (Φ : FormData O w)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (K : Matrix ι ι R) (hK : Φ.JR R * K = 1)
    (u : R) (hu : 2 * u = 1) (h' : Matrix ι ι R') (hh : Φ.HH h') (h0 : Matrix ι ι R) (b1 : h0.map p = h')
    (b2 : ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0) :
    Φ.HH (h0 + Matrix.of fun a b => if Φ.blk a = Φ.blk b then
      (K * ((-u) • (h0ᵀ * Φ.JR R * h0 - Φ.JR R))) a b else 0) ∧
    (h0 + Matrix.of fun a b => if Φ.blk a = Φ.blk b then
      (K * ((-u) • (h0ᵀ * Φ.JR R * h0 - Φ.JR R))) a b else 0).map p = h' := by
  obtain ⟨a1, a2, a3⟩ := hh
  have b3 : h0.map (res O R) = 1 := by
    rw [← a3, ← b1]
    ext a b
    simp [res_map]
  have jp : (Φ.JR R).map p = Φ.JR R' := by
    ext a b
    simp [FormData.JR]
  have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
    Φ.hblk a b fun n => e (by simp [FormData.JR, n])
  obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
    rcases Φ.sym with e | e
    · refine ⟨1, ?_, by simp⟩
      ext a b
      have := congrFun (congrFun e a) b
      simp only [transpose_apply] at this
      simp [FormData.JR, this]
    · refine ⟨-1, ?_, by simp⟩
      ext a b
      have := congrFun (congrFun e a) b
      simp only [transpose_apply] at this
      simp [FormData.JR, this]
  set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
  have E1 : E.map p = 0 := by
    rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
  have E2 : Eᵀ = ε • E := by
    rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
    simp [mul_assoc]
  have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
    have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
    rw [hE, Matrix.sub_apply, this, sub_zero]
    simp only [mul_apply, transpose_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases e1 : Φ.blk d = Φ.blk a
    · by_cases e2 : Φ.blk c = Φ.blk b
      · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
        simp [this]
      · simp [b2 _ _ e2]
    · simp [b2 _ _ e1]
  set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
  have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
  have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by
    rw [hZ0, mul_apply, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    have : p (E c b) = 0 := congrFun (congrFun E1 c) b
    simp [this]
  let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
  have Z3 : Z.map p = 0 := by
    ext a b
    by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
  have Z4 : Φ.JR R * Z = (-u) • E := by
    ext a b
    by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
    · rw [← Z1, mul_apply, mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases n : Φ.JR R a c = 0
      · simp [n]
      · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
        simp [Z, this]
    · rw [Matrix.smul_apply, E3 a b e, smul_zero, mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases n : Φ.JR R a c = 0
      · simp [n]
      · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
        simp [Z, this]
  have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
    have := congrArg (fun M => ε • Mᵀ) Z4
    simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
    rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
    exact this
  obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
  change Φ.HH (h0 + Z) ∧ (h0 + Z).map p = h'
  refine ⟨⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
  · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
    abel
  · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]

section Good

variable {O X A S : Type} [CommRing O] [AddCommGroup X] [CommRing A] [Algebra O A] [TopologicalSpace S]
  {I : Ideal A} {W : WPres O X A}

private def Good (I : Ideal A) (W : WPres O X A) (j : X) (f : S → A) : Prop :=
  AdicCont I f ∧ ∀ s, f s ∈ W.part j

private theorem good_zero (j : X) : Good I W j fun _ : S => 0 :=
  ⟨fun _ => IsLocallyConstant.const _, fun _ => zero_mem _⟩

private theorem good_add {j : X} {f g : S → A} (hf : Good I W j f) (hg : Good I W j g) :
    Good I W j fun s => f s + g s :=
  ⟨fun N => by simp only [map_add]; exact (hf.1 N).add (hg.1 N), fun s => add_mem (hf.2 s) (hg.2 s)⟩

private theorem good_sub {j : X} {f g : S → A} (hf : Good I W j f) (hg : Good I W j g) :
    Good I W j fun s => f s - g s :=
  ⟨fun N => by simp only [map_sub]; exact (hf.1 N).sub (hg.1 N), fun s => sub_mem (hf.2 s) (hg.2 s)⟩

private theorem good_mul {i j k : X} {f g : S → A} (hf : Good I W i f) (hg : Good I W j g) (e : i + j = k) :
    Good I W k fun s => f s * g s :=
  ⟨fun N => by simp only [map_mul]; exact (hf.1 N).mul (hg.1 N),
    fun s => e ▸ SetLike.GradedMul.mul_mem (hf.2 s) (hg.2 s)⟩

private theorem good_const (c : O) : Good I W 0 fun _ : S => algebraMap O A c :=
  ⟨fun _ => IsLocallyConstant.const _, fun _ => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem⟩

private theorem good_const' (c : O) {j : X} (h : c ≠ 0 → 0 = j) : Good I W j fun _ : S => algebraMap O A c := by
  by_cases e : c = 0
  · simpa [e] using good_zero j
  · exact h e ▸ good_const c

private theorem good_sum {ι : Type} (T : Finset ι) {j : X} {f : ι → S → A} (hf : ∀ i, Good I W j (f i)) :
    Good I W j fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using good_zero j
  | insert a T ha ih => simpa only [Finset.sum_insert ha] using good_add (hf a) ih

end Good

open Matrix in
theorem UpperTheory.V.Alg.hh_section :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (W : WPres O X A), (∀ s, W.z s ∈ maximalIdeal A) →
          ∀ (S : Type) [TopologicalSpace S] (h : S → Matrix ι ι R), (∀ s, Φ.HH (h s)) → (∀ a b, AdicCont (maximalIdeal R) fun s => h s a b) → (∀ s a b, h s a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
          ∃ h' : S → Matrix ι ι A, (∀ s, Φ.HH (h' s)) ∧ (∀ a b, AdicCont (maximalIdeal A) fun s => h' s a b) ∧ (∀ s a b, h' s a b ∈ W.part (w a - w b)) ∧ ∀ s, (h' s).map p = h s := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 A _ _ _ R _ _ _ p hp hs W hz S _ h hH hc hP
  classical
  choose y y1 y2 y3 using fun a b =>
    cont_section O X A R p hp hs W hz S (w a - w b) (fun s => h s a b) (hc a b) (fun s => hP s a b)
  let h0 : S → Matrix ι ι A := fun s => Matrix.of fun a b => if Φ.blk a = Φ.blk b then y a b s else 0
  have g0 : ∀ a b, Good (maximalIdeal A) W (w a - w b) fun s => h0 s a b := fun a b => by
    by_cases e : Φ.blk a = Φ.blk b
    · simp only [h0, of_apply, if_pos e]
      exact ⟨y1 a b, y2 a b⟩
    · simp only [h0, of_apply, if_neg e]
      exact good_zero _
  have b1 : ∀ s, (h0 s).map p = h s := fun s => by
    ext a b
    by_cases e : Φ.blk a = Φ.blk b
    · simp [h0, e, y3]
    · simp [h0, e, (hH s).2.1 a b e]
  have b2 : ∀ s a b, Φ.blk a ≠ Φ.blk b → h0 s a b = 0 := fun s a b e => by simp [h0, e]
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  have hu' : 2 * algebraMap O A u = 1 := by
    have := congrArg (algebraMap O A) hu
    rwa [map_mul, map_ofNat, map_one] at this
  have hK : Φ.JR A * Φ.J⁻¹.map (algebraMap O A) = 1 := by
    have hd : IsUnit Φ.J.det := (Matrix.isUnit_iff_isUnit_det _).1 Φ.unit
    rw [FormData.JR, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd]
    simp
  have key := fun s => fix_point Φ p hs _ hK _ hu' (h s) (hH s) (h0 s) (b1 s) (b2 s)
  have gJ : ∀ a b, Good (maximalIdeal A) W (Φ.c - w a - w b) fun _ : S => Φ.JR A a b := fun a b =>
    good_const' _ fun n => by rw [← Φ.hw a b n]; abel
  have gK : ∀ a b, Good (maximalIdeal A) W (w a + w b - Φ.c) fun _ : S => Φ.J⁻¹.map (algebraMap O A) a b :=
    fun a b => good_const' _ fun n => by rw [← (inv_supp Φ a b n).2]; abel
  have gE : ∀ a b, Good (maximalIdeal A) W (Φ.c - w a - w b)
      fun s => ((h0 s)ᵀ * Φ.JR A * h0 s - Φ.JR A) a b := fun a b => by
    simp only [Matrix.sub_apply, mul_apply, transpose_apply]
    refine good_sub (good_sum _ fun c => good_mul (i := Φ.c - w a - w c) (good_sum _ fun d =>
      good_mul (g0 d a) (gJ d c) (by abel)) (g0 c b) (by abel)) (gJ a b)
  have g1 : ∀ a b, Good (maximalIdeal A) W (w a - w b) fun s => (h0 s + Matrix.of fun a b =>
      if Φ.blk a = Φ.blk b then (Φ.J⁻¹.map (algebraMap O A) *
        ((-algebraMap O A u) • ((h0 s)ᵀ * Φ.JR A * h0 s - Φ.JR A))) a b else 0) a b := fun a b => by
    simp only [Matrix.add_apply, of_apply]
    refine good_add (g0 a b) ?_
    by_cases e : Φ.blk a = Φ.blk b
    · simp only [if_pos e, ← map_neg]
      simp only [mul_apply (M := Φ.J⁻¹.map (algebraMap O A)), Matrix.smul_apply, smul_eq_mul]
      exact good_sum _ fun c => good_mul (gK a c) (good_mul (good_const (-u)) (gE c b) (zero_add _)) (by abel)
    · simp only [if_neg e]
      exact good_zero _
  exact ⟨_, fun s => (key s).1, fun a b => (g1 a b).1, fun s a b => (g1 a b).2 s, fun s => (key s).2⟩
