import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply

noncomputable section

namespace GlobalTheory.DetShiftWeyl

open MvPolynomial WeylLatticeDuality GlobalTheory.IntegralityCompare

theorem hw_shift (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    hw R (r := m + 1) (n := m + 1) le_rfl (fun s => ν s + c) =
      hw R (r := m + 1) (n := m + 1) le_rfl ν * lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c := by
  unfold hw
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    congr 1
    unfold nuNext
    have h : (s.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_castSucc]; omega
    rw [dif_pos h, dif_pos h]
    dsimp only
    omega
  · have h : ¬ ((Fin.last m : Fin (m + 1)).val + 1 < m + 1) := by simp
    unfold nuNext
    rw [dif_neg h, dif_neg h]
    dsimp only
    rw [Nat.sub_zero, Nat.sub_zero, pow_add]
    rfl

theorem rowGen_fullMinor (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    rowGen R a b (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a b).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b
        (((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]

theorem rowDiv_fullMinor_mul (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a b k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_fullMinor R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem rowGen_fullMinor_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) :
    rowGen R a a (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      (1 + Polynomial.X) * Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a a).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem rowDiv_fullMinor_mul_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a a k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          ((c.choose p.1 : ℕ) : MvPolynomial (Fin m × Fin m) R) * rowDiv R a a p.2 f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_fullMinor_self, mul_pow, ← Polynomial.C_pow, mul_comm ((1 + Polynomial.X) ^ c) _,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm (1 : Polynomial (MvPolynomial (Fin m × Fin m) R)), Polynomial.coeff_X_add_one_pow]

theorem rowDiv_add' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]

theorem rowDiv_smul' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (t : R)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b k (t • f) = t • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem rowDiv_zero' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R a b k (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  unfold rowDiv
  rw [map_zero, Polynomial.coeff_zero]

theorem rowDiv_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) : rowDiv R a b k f ∈ weyl R r n hn ν := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => rw [rowDiv_zero']; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add']; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [rowDiv_smul']; exact Submodule.smul_mem _ t hx

theorem weyl_shift_le (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) ≤
      (weyl R (m + 1) (m + 1) le_rfl ν).map
        (LinearMap.mulLeft R (lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c)) := by
  set S := (weyl R (m + 1) (m + 1) le_rfl ν).map
    (LinearMap.mulLeft R (lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c)) with hS
  have hstab : ∀ (a b : Fin (m + 1)) (k : ℕ) (x : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R), x ∈ S →
      rowDiv R a b k x ∈ S := by
    intro a b k x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    simp only [LinearMap.mulLeft_apply]
    by_cases hab : a = b
    · subst hab
      rw [rowDiv_fullMinor_mul_self]
      refine Submodule.mem_map.mpr ⟨_, ?_, rfl⟩
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [← nsmul_eq_mul]
      exact Submodule.smul_of_tower_mem _ _ (rowDiv_mem R le_rfl ν a a p.2 g hg)
    · rw [rowDiv_fullMinor_mul R a b hab]
      exact Submodule.mem_map.mpr ⟨_, rowDiv_mem R le_rfl ν a b k g hg, rfl⟩
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil =>
    refine Submodule.mem_map.mpr ⟨hw R le_rfl ν, Submodule.subset_span ⟨[], rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply, applyWord, List.foldr_nil]
    rw [hw_shift, mul_comm]
  | cons x w ih =>
    exact hstab x.1 x.2.1 x.2.2 _ ih

theorem fullMinor_pow_mul_mem (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (hg : g ∈ weyl R (m + 1) (m + 1) le_rfl ν) :
    lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * g ∈
      weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) := by
  set D := lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c with hD
  set W' := weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) with hW'
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), D * applyWord R w (hw R le_rfl ν) ∈ W' := by
    intro w
    induction w with
    | nil =>
      simp only [applyWord, List.foldr_nil]
      rw [hD, mul_comm, ← hw_shift]
      exact Submodule.subset_span ⟨[], rfl⟩
    | cons x w ih =>
      obtain ⟨a, b, k⟩ := x
      show D * rowDiv R a b k (applyWord R w (hw R le_rfl ν)) ∈ W'
      set g := applyWord R w (hw R le_rfl ν)
      by_cases hab : a = b
      · subst hab
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          have h1 := rowDiv_fullMinor_mul_self R a k c g
          have hmem : ((0 : ℕ), k) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
          rw [← Finset.add_sum_erase _ _ hmem] at h1
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
          have h2 : D * rowDiv R a a k g = rowDiv R a a k (D * g) -
              ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k),
                D * (((c.choose p.1 : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * rowDiv R a a p.2 g) := by
            rw [hD, h1, mul_add, Finset.mul_sum]
            ring
          rw [h2]
          refine Submodule.sub_mem _ (rowDiv_mem R le_rfl _ a a k _ ih) ?_
          refine Submodule.sum_mem _ fun p hp => ?_
          have hp2 : p.2 < k := by
            rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
            have hne : p.1 ≠ 0 := fun h => hp.1 (Prod.ext h (by simp; omega))
            omega
          rw [mul_left_comm, ← nsmul_eq_mul]
          exact Submodule.smul_of_tower_mem _ _ (ihk p.2 hp2)
      · rw [← rowDiv_fullMinor_mul R a b hab]
        exact rowDiv_mem R le_rfl _ a b k _ ih
  unfold weyl at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact key w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem mem_weyl_shift_iff (N : ℕ) (μ : Fin N → ℕ) (c : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ) :
    f ∈ weyl ℤ N N le_rfl (fun s => μ s + c) ↔
      ∃ g ∈ weyl ℤ N N le_rfl μ, f = lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl ^ c * g := by
  cases N with
  | zero =>
    have hμ : (fun s : Fin 0 => μ s + c) = μ := funext fun s => s.elim0
    rw [hμ]
    have h1 : lpMinor ℤ (r := 0) (n := 0) 0 le_rfl le_rfl = 1 := by unfold lpMinor; simp
    simp [h1]
  | succ m =>
    constructor
    · intro hf
      obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp (weyl_shift_le ℤ μ c hf)
      exact ⟨g, hg, hgf.symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact fullMinor_pow_mul_mem ℤ μ c g hg

theorem eval_fullMinor {K : Type} [CommRing K] (N : ℕ) (Y : Matrix (Fin N) (Fin N) K) :
    MvPolynomial.eval (fun k : Fin N × Fin N => Y k.1 k.2)
      (MvPolynomial.map (Int.castRingHom K) (lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl)) = Y.det := by
  unfold lpMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp [Fin.castLE_refl]

def polFunAdd (K : Type) [CommRing K] (T : Type) (N : ℕ) :
    MvPolynomial (T × Fin N × Fin N) K →+ ((T → Matrix (Fin N) (Fin N) K) → K) where
  toFun := polFun
  map_zero' := by funext y; simp [polFun]
  map_add' := by intro a b; funext y; simp [polFun]

def detMul (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) :
    ((T → Matrix (Fin N) (Fin N) K) → K) →+ ((T → Matrix (Fin N) (Fin N) K) → K) :=
  AddMonoidHom.mulLeft (fun y => ∏ τ, (y τ).det ^ k τ)

theorem detMul_apply (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ)
    (F : (T → Matrix (Fin N) (Fin N) K) → K) (y : T → Matrix (Fin N) (Fin N) K) :
    detMul K N k F y = (∏ τ, (y τ).det ^ k τ) * F y := rfl

theorem polFunAdd_apply (K : Type) [CommRing K] (T : Type) (N : ℕ) (P : MvPolynomial (T × Fin N × Fin N) K) :
    polFunAdd K T N P = polFun P := rfl

theorem delW_le_range (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) :
    DelW p T N ν ≤ (polFunAdd ℂ_[p] T N).range := by
  unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, -, -, rfl⟩
  refine ⟨C r * ∏ τ, rename (fun k : Fin N × Fin N => (τ, k.1, k.2))
    (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)), ?_⟩
  funext y
  simp [polFunAdd, polFun, eval_rename, Function.comp_def]

theorem delW_le_comap (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ) :
    DelW p T N ν ≤ (DelW p T N (fun τ r => ν τ r + k τ)).comap (detMul ℂ_[p] N k) := by
  unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, hr, hf, rfl⟩
  apply AddSubgroup.subset_closure
  refine ⟨r, fun τ => lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl ^ k τ * f τ, hr,
    fun τ => (mem_weyl_shift_iff N (ν τ) (k τ) _).2 ⟨f τ, hf τ, rfl⟩, ?_⟩
  funext y
  simp only [detMul_apply, map_mul, map_pow, eval_fullMinor,
    Finset.prod_mul_distrib]
  ring

theorem delW_shift_le_map (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ) :
    DelW p T N (fun τ r => ν τ r + k τ) ≤
      (DelW p T N ν ⊓ (polFunAdd ℂ_[p] T N).range).map (detMul ℂ_[p] N k) := by
  conv_lhs => unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, hr, hf, rfl⟩
  choose g hg hfg using fun τ => (mem_weyl_shift_iff N (ν τ) (k τ) (f τ)).1 (hf τ)
  have hgen : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => r * ∏ τ, MvPolynomial.eval
      (fun kk : Fin N × Fin N => y τ kk.1 kk.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (g τ))) ∈ DelW p T N ν :=
    AddSubgroup.subset_closure ⟨r, g, hr, hg, rfl⟩
  refine AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.mem_inf.mpr ⟨hgen, delW_le_range p T N ν hgen⟩, ?_⟩
  funext y
  simp only [detMul_apply, hfg, map_mul, map_pow, eval_fullMinor,
    Finset.prod_mul_distrib]
  ring

def detPoly (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) : MvPolynomial (T × Fin N × Fin N) K :=
  ∏ τ, (Matrix.of fun a b : Fin N => (X (τ, a, b) : MvPolynomial (T × Fin N × Fin N) K)).det ^ k τ

theorem polFun_detPoly (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ)
    (y : T → Matrix (Fin N) (Fin N) K) : polFun (detPoly K N k) y = ∏ τ, (y τ).det ^ k τ := by
  unfold polFun detPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

theorem detPoly_ne_zero (K : Type) [CommRing K] [Nontrivial K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) :
    detPoly K N k ≠ 0 := by
  intro h
  have := polFun_detPoly K N k (fun _ => 1)
  rw [h] at this
  simp [polFun] at this

theorem detPow_mul_mem_delW_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (k : T → ℕ) (Φ : MvPolynomial (T × Fin N × Fin N) ℂ_[p]),
    ((fun y => (∏ τ, (y τ).det ^ k τ) * polFun Φ y) ∈ WeylLatticeDuality.DelW p T N (fun τ r => ν τ r + k τ) ↔
      polFun Φ ∈ WeylLatticeDuality.DelW p T N ν) := by
  intro p _ T _ N ν k Φ
  constructor
  · intro h
    obtain ⟨G, hGm, hGe⟩ := AddSubgroup.mem_map.mp (delW_shift_le_map p T N ν k h)
    obtain ⟨hG, hR⟩ := AddSubgroup.mem_inf.mp hGm
    obtain ⟨Ψ, rfl⟩ := AddMonoidHom.mem_range.mp hR
    haveI : Infinite ℂ_[p] := CharZero.infinite _
    have hpoly : detPoly ℂ_[p] N k * Ψ = detPoly ℂ_[p] N k * Φ := by
      apply MvPolynomial.funext
      intro x
      let y : T → Matrix (Fin N) (Fin N) ℂ_[p] := fun τ a b => x (τ, a, b)
      have hy : (∏ τ, (y τ).det ^ k τ) * polFun Ψ y = (∏ τ, (y τ).det ^ k τ) * polFun Φ y := congrFun hGe y
      have h1 := polFun_detPoly ℂ_[p] N k y
      have hm : ∀ A B : MvPolynomial (T × Fin N × Fin N) ℂ_[p], polFun (A * B) y = polFun A y * polFun B y :=
        fun A B => by simp [polFun]
      show polFun (detPoly ℂ_[p] N k * Ψ) y = polFun (detPoly ℂ_[p] N k * Φ) y
      rw [hm, hm, h1, hy]
    have hΨ : Ψ = Φ := mul_left_cancel₀ (detPoly_ne_zero ℂ_[p] N k) hpoly
    subst hΨ
    exact hG
  · intro h
    exact AddSubgroup.mem_comap.mp (delW_le_comap p T N ν k h)

end GlobalTheory.DetShiftWeyl

end
