import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetConjOnMatricesKillingIntoSubspaceStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagModulus

section Linear

variable {K A B C : Type} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

theorem det_eq_of_intertwine (e : A ≃ₗ[K] B) (a : A →ₗ[K] A) (b : B →ₗ[K] B)
    (h : ∀ x, e (a x) = b (e x)) : LinearMap.det b = LinearMap.det a := by
  have hb : b = (e : A →ₗ[K] B) ∘ₗ a ∘ₗ (e.symm : B →ₗ[K] A) := by
    ext x
    simp [h]
  rw [hb, LinearMap.det_conj]

theorem det_exact [FiniteDimensional K B] (i : A →ₗ[K] B) (π : B →ₗ[K] C)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π)
    (a : A →ₗ[K] A) (b : B →ₗ[K] B) (c : C →ₗ[K] C)
    (ha : ∀ x, i (a x) = b (i x)) (hc : ∀ x, π (b x) = c (π x)) :
    LinearMap.det b = LinearMap.det a * LinearMap.det c := by
  have hle : LinearMap.ker π ≤ (LinearMap.ker π).comap b := by
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker] at *
    rw [hc, hx, map_zero]
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker π) b hle]
  congr 1
  · refine det_eq_of_intertwine ((LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)) a _ ?_
    intro x
    apply Subtype.ext
    simp [ha]
  · refine (det_eq_of_intertwine (π.quotKerEquivOfSurjective hπ) _ c ?_).symm
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    simp [hc]

theorem det_sup_mul_det_inf [FiniteDimensional K B] (Φ : B →ₗ[K] B) (P Q S I : Submodule K B)
    (hS : S = P ⊔ Q) (hI : I = P ⊓ Q)
    (hP' : ∀ x ∈ P, Φ x ∈ P) (hQ' : ∀ x ∈ Q, Φ x ∈ Q) (hS' : ∀ x ∈ S, Φ x ∈ S)
    (hI' : ∀ x ∈ I, Φ x ∈ I) :
    LinearMap.det (Φ.restrict hI') * LinearMap.det (Φ.restrict hS') =
      LinearMap.det (Φ.restrict hP') * LinearMap.det (Φ.restrict hQ') := by
  subst hS hI
  let i : ↥(P ⊓ Q) →ₗ[K] ↥P × ↥Q :=
    LinearMap.prod (Submodule.inclusion inf_le_left) (-Submodule.inclusion inf_le_right)
  let π : ↥P × ↥Q →ₗ[K] ↥(P ⊔ Q) :=
    LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hi : Function.Injective i := by
    intro x y hxy
    have := congrArg (fun z => ((z.1 : ↥P) : B)) hxy
    exact Subtype.ext (by simpa [i] using this)
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext (by simp [π])⟩
  have hex : LinearMap.range i = LinearMap.ker π := by
    ext ⟨p, q⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      apply Subtype.ext
      simp [i, π]
    · intro h
      have h' : (p : B) + q = 0 := by simpa [π] using congrArg Subtype.val h
      have hpQ : (p : B) ∈ Q := by
        rw [eq_neg_of_add_eq_zero_left h']
        exact Q.neg_mem q.2
      have hq : -(p : B) = q := by
        rw [neg_eq_iff_add_eq_zero]
        exact h'
      refine ⟨⟨p, Submodule.mem_inf.2 ⟨p.2, hpQ⟩⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)⟩
      simpa [i] using hq
  have key := det_exact i π hi hπ hex (Φ.restrict hI')
    (LinearMap.prodMap (Φ.restrict hP') (Φ.restrict hQ')) (Φ.restrict hS')
    (fun x => Prod.ext (Subtype.ext (by simp [i])) (Subtype.ext (by simp [i])))
    (fun x => Subtype.ext (by simp [π]))
  rw [LinearMap.det_prodMap] at key
  exact key.symm

end Linear

variable {n : ℕ}

def homSub (P Q : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q}
  add_mem' := fun {X Y} hX hY => ⟨fun y hy => by rw [Matrix.add_mulVec, hX.1 y hy, hY.1 y hy, add_zero],
    fun y => by rw [Matrix.add_mulVec]; exact Q.add_mem (hX.2 y) (hY.2 y)⟩
  zero_mem' := ⟨fun y _ => Matrix.zero_mulVec y, fun y => by rw [Matrix.zero_mulVec]; exact Q.zero_mem⟩
  smul_mem' := fun c X hX => ⟨fun y hy => by rw [Matrix.smul_mulVec, hX.1 y hy, smul_zero],
    fun y => by rw [Matrix.smul_mulVec]; exact Q.smul_mem c (hX.2 y)⟩

theorem mem_homSub {P Q : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ homSub P Q ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q := by
  exact Iff.rfl

def twoSided (f g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.mulRight ℂ g).comp (LinearMap.mulLeft ℂ f)

theorem twoSided_apply (f g X : Matrix (Fin n) (Fin n) ℂ) : twoSided f g X = f * X * g := rfl

theorem twoSided_mulVec (f g X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    twoSided f g X *ᵥ y = f *ᵥ (X *ᵥ (g *ᵥ y)) := by
  rw [twoSided_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem homSub_stable {f g : Matrix (Fin n) (Fin n) ℂ} {P Q : Submodule ℂ (Fin n → ℂ)}
    (hP : ∀ y ∈ P, g *ᵥ y ∈ P) (hQ : ∀ y ∈ Q, f *ᵥ y ∈ Q) :
    ∀ X ∈ homSub P Q, twoSided f g X ∈ homSub P Q := by
  intro X hX
  rw [mem_homSub] at hX ⊢
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [twoSided_mulVec, hX.1 _ (hP y hy), Matrix.mulVec_zero]
  · rw [twoSided_mulVec]
    exact hQ _ (hX.2 _)

theorem detOn_pos {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  have hf : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  have hg : ∀ y ∈ V, Matrix.toLin' g y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact GlobalTheory.FlagLeviGroup.inv_keeps hgf V hV y hy
  unfold detOn
  rw [dif_pos hf]
  apply norm_pos_iff.2
  intro h0
  have hcomp : ((Matrix.toLin' g).restrict hg).comp ((Matrix.toLin' f).restrict hf) =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, hy⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hgf]
  have := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, h0, mul_zero, LinearMap.det_id] at this
  exact zero_ne_one this

def killing (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (V : Submodule ℂ (Fin n → ℂ)) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) := N ⊓ homSub V ⊤

theorem mem_killing {N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)} {V : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ killing N V ↔ X ∈ N ∧ ∀ y ∈ V, X *ᵥ y = 0 := by
  simp [killing, Submodule.mem_inf, mem_homSub]

section Flag

variable {r : ℕ} {F : ℕ → Submodule ℂ (Fin n → ℂ)} {N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)}

theorem homSub_le (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) (k : ℕ) :
    homSub (F k) (F k) ≤ N := by
  intro X hX
  rw [mem_homSub] at hX
  rw [hN]
  intro s hs y hy
  rcases Nat.lt_or_ge s k with h | h
  · rw [hX.1 y (hF (Nat.succ_le_of_lt h) hy)]
    exact (F s).zero_mem
  · exact hF h (hX.2 y)

theorem killing_eq_sup (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) {k : ℕ} (hk : k < r) :
    killing N (F k) = killing N (F (k + 1)) ⊔ homSub (F k) (F k) := by
  have hkk : F k ≤ F (k + 1) := hF (Nat.le_succ k)
  apply le_antisymm
  · intro X hX
    rw [mem_killing] at hX
    have hXN := (hN X).1 hX.1 k hk
    obtain ⟨p, hp⟩ :=
      LinearMap.exists_leftInverse_of_injective (F (k + 1)).subtype (Submodule.ker_subtype _)
    have hpy : ∀ y ∈ F (k + 1), ((p y : F (k + 1)) : Fin n → ℂ) = y := by
      intro y hy
      simpa using congrArg Subtype.val (LinearMap.congr_fun hp ⟨y, hy⟩)
    let M : Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toMatrix' ((Matrix.toLin' X).comp ((F (k + 1)).subtype.comp p))
    have hM : ∀ y, M *ᵥ y = X *ᵥ ((p y : F (k + 1)) : Fin n → ℂ) := by
      intro y
      simp [M, LinearMap.toMatrix'_mulVec]
    have h2 : M ∈ homSub (F k) (F k) := by
      rw [mem_homSub]
      refine ⟨fun y hy => ?_, fun y => ?_⟩
      · rw [hM, hpy y (hkk hy)]
        exact hX.2 y hy
      · rw [hM]
        exact hXN _ (p y).2
    have h1 : X - M ∈ killing N (F (k + 1)) := by
      rw [mem_killing]
      refine ⟨N.sub_mem hX.1 (homSub_le hF hN k h2), fun y hy => ?_⟩
      rw [Matrix.sub_mulVec, hM, hpy y hy, sub_self]
    have := Submodule.add_mem_sup h1 h2
    rwa [sub_add_cancel] at this
  · apply sup_le
    · intro X hX
      rw [mem_killing] at hX ⊢
      exact ⟨hX.1, fun y hy => hX.2 y (hkk hy)⟩
    · intro X hX
      rw [mem_killing]
      refine ⟨homSub_le hF hN k hX, ?_⟩
      rw [mem_homSub] at hX
      exact hX.1

theorem homSub_eq_inf (hF : Monotone F)
    (hN : ∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) (k : ℕ) :
    homSub (F (k + 1)) (F k) = killing N (F (k + 1)) ⊓ homSub (F k) (F k) := by
  have hkk : F k ≤ F (k + 1) := hF (Nat.le_succ k)
  ext X
  rw [Submodule.mem_inf, mem_killing, mem_homSub, mem_homSub]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : X ∈ homSub (F k) (F k) := by
      rw [mem_homSub]
      exact ⟨fun y hy => h1 y (hkk hy), h2⟩
    exact ⟨⟨homSub_le hF hN k h3, h1⟩, fun y hy => h1 y (hkk hy), h2⟩
  · rintro ⟨⟨_, h1⟩, _, h2⟩
    exact ⟨h1, h2⟩

end Flag

theorem telescope_nat (a c : ℕ → ℕ) (r : ℕ) (h : ∀ k < r, a k = a (k + 1) + c k) :
    a 0 = a r + ∑ s ∈ Finset.range r, c s := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r),
      Finset.sum_range_succ]
    ring

theorem telescope_real (a c : ℕ → ℝ) (r : ℕ) (h : ∀ k < r, a k = a (k + 1) * c k) :
    a 0 = a r * ∏ s ∈ Finset.range r, c s := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r),
      Finset.prod_range_succ]
    ring

theorem flag_finrank_det : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) (F : ℕ → Submodule ℂ (Fin n → ℂ)) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → Monotone F → F 0 = ⊥ → F r = ⊤ → (∀ s, ∀ y ∈ F s, f *ᵥ y ∈ F s) → (∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) → Module.finrank ℂ N = ∑ s ∈ Finset.range r, (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s) ∧ ∀ φ : N →ₗ[ℂ] N, (∀ X : N, ((φ X : N) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = ∏ s ∈ Finset.range r, detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) / detOn f (F (s + 1)) ^ Module.finrank ℂ (F s) := by
  intro n f g r F N hfg hdet hF h0 hr hfF hN
  have hgf : g * f = 1 := mul_eq_one_comm.mp hfg
  have hgF : ∀ s, ∀ y ∈ F s, g *ᵥ y ∈ F s := fun s =>
    GlobalTheory.FlagLeviGroup.inv_keeps hgf (F s) (hfF s)
  have hNst : ∀ X ∈ N, twoSided f g X ∈ N := by
    intro X hX
    rw [hN] at hX ⊢
    intro s hs y hy
    rw [twoSided_mulVec]
    exact hfF s _ (hX s hs _ (hgF (s + 1) y hy))
  have hKst : ∀ k, ∀ X ∈ killing N (F k), twoSided f g X ∈ killing N (F k) := by
    intro k X hX
    rw [mem_killing] at hX ⊢
    refine ⟨hNst X hX.1, fun y hy => ?_⟩
    rw [twoSided_mulVec, hX.2 _ (hgF k y hy), Matrix.mulVec_zero]
  have hHst : ∀ P Q : Submodule ℂ (Fin n → ℂ), (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) →
      ∀ X ∈ homSub P Q, twoSided f g X ∈ homSub P Q := fun P Q hP hQ =>
    homSub_stable (GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP) hQ
  have key := fun (P Q : Submodule ℂ (Fin n → ℂ)) (hP : ∀ y ∈ P, f *ᵥ y ∈ P)
      (hQ : ∀ y ∈ Q, f *ᵥ y ∈ Q) =>
    GlobalTheory.T.det_conj_on_matrices_killing_into_subspace n f g P Q (homSub P Q) hfg hdet hP hQ (fun _ => mem_homSub)
  have hmono : ∀ k, F k ≤ F (k + 1) := fun k => hF (Nat.le_succ k)
  have hK0 : killing N (F 0) = N := by
    ext X
    rw [mem_killing, h0]
    simp
  have hKr : killing N (F r) = ⊥ := by
    ext X
    rw [mem_killing, hr, Submodule.mem_bot]
    constructor
    · rintro ⟨_, h⟩
      have hX : Matrix.toLin' X = 0 := LinearMap.ext fun y => by
        simpa using h y Submodule.mem_top
      exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').1 hX
    · rintro rfl
      exact ⟨N.zero_mem, fun y _ => Matrix.zero_mulVec y⟩
  have hdim : ∀ k < r, Module.finrank ℂ (killing N (F k)) =
      Module.finrank ℂ (killing N (F (k + 1))) +
        (Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k)) * Module.finrank ℂ (F k) := by
    intro k hk
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (killing N (F (k + 1))) (homSub (F k) (F k))
    rw [← killing_eq_sup hF hN hk, ← homSub_eq_inf hF hN k, (key _ _ (hfF (k + 1)) (hfF k)).1,
      (key _ _ (hfF k) (hfF k)).1] at h1
    have hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1)) :=
      Submodule.finrank_mono (hmono k)
    have hle2 : Module.finrank ℂ (F (k + 1)) ≤ n := by
      simpa using Submodule.finrank_le (F (k + 1))
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle1
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle2
    have E1 : n - Module.finrank ℂ (F (k + 1)) = m := by omega
    have E2 : n - Module.finrank ℂ (F k) = m + e := by omega
    have E3 : Module.finrank ℂ (F (k + 1)) - Module.finrank ℂ (F k) = e := by omega
    rw [E1, E2] at h1
    rw [E3]
    rw [add_mul] at h1
    linarith
  have hstep : ∀ k < r, ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖ =
      ‖LinearMap.det ((twoSided f g).restrict (hKst (k + 1)))‖ *
        (detOn f (F k) ^ Module.finrank ℂ (F (k + 1)) /
          detOn f (F (k + 1)) ^ Module.finrank ℂ (F k)) := by
    intro k hk
    have hm := det_sup_mul_det_inf (twoSided f g) (killing N (F (k + 1))) (homSub (F k) (F k))
      (killing N (F k)) (homSub (F (k + 1)) (F k)) (killing_eq_sup hF hN hk)
      (homSub_eq_inf hF hN k) (hKst (k + 1)) (hHst _ _ (hfF k) (hfF k)) (hKst k)
      (hHst _ _ (hfF (k + 1)) (hfF k))
    have hA := (key _ _ (hfF (k + 1)) (hfF k)).2
      ((twoSided f g).restrict (hHst _ _ (hfF (k + 1)) (hfF k))) (fun X => twoSided_apply f g _)
    have hB := (key _ _ (hfF k) (hfF k)).2
      ((twoSided f g).restrict (hHst _ _ (hfF k) (hfF k))) (fun X => twoSided_apply f g _)
    have hnorm := congrArg (fun z : ℂ => ‖z‖) hm
    simp only [norm_mul] at hnorm
    rw [hA, hB] at hnorm
    have hx := detOn_pos hgf (F k) (hfF k)
    have hy := detOn_pos hgf (F (k + 1)) (hfF (k + 1))
    have hle1 : Module.finrank ℂ (F k) ≤ Module.finrank ℂ (F (k + 1)) :=
      Submodule.finrank_mono (hmono k)
    have hle2 : Module.finrank ℂ (F (k + 1)) ≤ n := by
      simpa using Submodule.finrank_le (F (k + 1))
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle1
    obtain ⟨m, hm'⟩ := Nat.exists_eq_add_of_le hle2
    have E1 : n - Module.finrank ℂ (F (k + 1)) = m := by omega
    have E2 : n - Module.finrank ℂ (F k) = m + e := by omega
    rw [E1, E2] at hnorm
    rw [he, mul_div_assoc', eq_div_iff (pow_pos hy _).ne']
    apply mul_left_cancel₀ (pow_ne_zero m hx.ne')
    linear_combination hnorm
  have hDr : ‖LinearMap.det ((twoSided f g).restrict (hKst r))‖ = 1 := by
    have hb : ∀ X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)),
        twoSided f g X ∈ (⊥ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) := by
      intro X hX
      rw [Submodule.mem_bot] at hX ⊢
      rw [hX, map_zero]
    have := det_eq_of_intertwine (LinearEquiv.ofEq _ _ hKr) ((twoSided f g).restrict (hKst r))
      ((twoSided f g).restrict hb) (fun x => Subtype.ext rfl)
    rw [← this, LinearMap.det_eq_one_of_subsingleton, norm_one]
  refine ⟨?_, fun φ hφ => ?_⟩
  · have ht := telescope_nat (fun k => Module.finrank ℂ (killing N (F k)))
      (fun s => (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s))
      r hdim
    rw [hK0, hKr, finrank_bot, zero_add] at ht
    exact ht
  · have ht := telescope_real (fun k => ‖LinearMap.det ((twoSided f g).restrict (hKst k))‖)
      (fun s => detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) /
        detOn f (F (s + 1)) ^ Module.finrank ℂ (F s)) r hstep
    rw [hDr, one_mul] at ht
    rw [← ht]
    have := det_eq_of_intertwine (LinearEquiv.ofEq _ _ hK0) ((twoSided f g).restrict (hKst 0)) φ
      (fun x => Subtype.ext (by rw [hφ]; exact twoSided_apply f g _))
    rw [this]

end GlobalTheory.FlagModulus
