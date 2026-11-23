import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopIffDense

namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem smul_eq_zero_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (e : M ≃ₗ[R] (Fin n → R ⧸ I)) {c : R} (hc : c ∈ I) (x : M) : c • x = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hc]

theorem corner_equiv {R : Type} [CommRing R] (I : Ideal R) (hI : IsLocalRing (R ⧸ I)) {m k : ℕ} (hm : 0 < m)
    (C : Type) [AddCommGroup C] [Module R C] (e : (Fin m → C) ≃ₗ[R] (Fin (m * k) → R ⧸ I)) :
    Nonempty (C ≃ₗ[R] (Fin k → R ⧸ I)) := by
  have hC : Module.IsTorsionBySet R C I := by
    intro x a
    have h := congrFun (smul_eq_zero_of_equiv I e a.2 (Pi.single (⟨0, hm⟩ : Fin m) x)) ⟨0, hm⟩
    simpa using h
  letI : Module (R ⧸ I) C := hC.module
  haveI : IsScalarTower R (R ⧸ I) C := hC.isScalarTower
  let e' : (Fin m → C) ≃ₗ[R ⧸ I] (Fin (m * k) → R ⧸ I) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e
  haveI : Module.Finite (R ⧸ I) (Fin m → C) := Module.Finite.equiv e'.symm
  haveI : Module.Free (R ⧸ I) (Fin m → C) := Module.Free.of_equiv e'.symm
  let i0 : C →ₗ[R ⧸ I] (Fin m → C) := LinearMap.single (R ⧸ I) (fun _ => C) ⟨0, hm⟩
  let p0 : (Fin m → C) →ₗ[R ⧸ I] C := LinearMap.proj ⟨0, hm⟩
  haveI : Module.Projective (R ⧸ I) C := Module.Projective.of_split i0 p0 (by ext x; simp [i0, p0])
  haveI : Module.Finite (R ⧸ I) C := Module.Finite.of_surjective p0 (fun x => ⟨Pi.single ⟨0, hm⟩ x, by simp [p0]⟩)
  haveI : Module.Free (R ⧸ I) C := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (R ⧸ I) (Fin m → C) = m * k := by
    rw [e'.finrank_eq, Module.finrank_fin_fun]
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 : Module.finrank (R ⧸ I) C = k := Nat.eq_of_mul_eq_mul_left hm h1
  exact ⟨(LinearEquiv.ofFinrankEq C (Fin k → R ⧸ I) (by rw [h2, Module.finrank_fin_fun])).restrictScalars R⟩

section
variable {R : Type} [CommRing R] {I : Ideal R} {m : ℕ} {O : Type} [Ring O] [Algebra R O]
  {φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)}
  {P : Type} [AddCommGroup P] [Module O P] [Module R P] [IsScalarTower R O P]

theorem act_congr (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    {b b' : O} (h : φ b = φ b') (x : P) : b • x = b' • x := by
  have hb : b - b' ∈ I • (⊤ : Submodule R O) := hker _ (by rw [map_sub, h, sub_self])
  have key : ∀ y ∈ I • (⊤ : Submodule R O), y • x = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro c hc o _
      rw [smul_assoc, hP c hc]
    · intro y z hy hz
      rw [add_smul, hy, hz, zero_add]
  have := key _ hb
  rwa [sub_smul, sub_eq_zero] at this

def units (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) : MatrixUnits R P (Fin m) where
  E i j := Algebra.lsmul R R P (E i j)
  mul_eq i j k l := by
    by_cases h : j = k
    · subst h
      rw [if_pos rfl, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E j l) • x = E i l • x
      exact act_congr hker hP (by rw [map_mul, hE, hE, hE, Matrix.single_mul_single_same, mul_one]) x
    · rw [if_neg h, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E k l) • x = 0
      have := act_congr hker hP (b := E i j * E k l) (b' := 0)
        (by rw [map_mul, hE, hE, Matrix.single_mul_single_of_ne (h := h), map_zero]) x
      rwa [zero_smul] at this
  sum_diag := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    show ∑ i, E i i • x = x
    rw [← Finset.sum_smul]
    have := act_congr hker hP (b := ∑ i, E i i) (b' := 1)
      (by rw [map_sum, map_one]; simp only [hE]; exact Matrix.sum_single_one) x
    rwa [one_smul] at this

theorem units_E (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) (i j : Fin m) (x : P) :
    (units hker hP E hE).E i j x = E i j • x := rfl

end

end GlobalTheory.MoritaLocal

namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem morita_local : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  intro R _ I hI m k hm O _ _ φ hφ hker M N _ _ _ _ _ _ _ _ eM eN
  have hM : ∀ c ∈ I, ∀ x : M, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eM hc x
  have hN : ∀ c ∈ I, ∀ x : N, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eN hc x
  choose E hE using fun i j : Fin m => hφ (Matrix.single i j (1 : R ⧸ I))
  let UM := units hker hM E hE
  let UN := units hker hN E hE
  let a : Fin m := ⟨0, hm⟩
  obtain ⟨gM⟩ := corner_equiv I hI hm (UM.corner a) ((UM.toPi a).symm.trans eM)
  obtain ⟨gN⟩ := corner_equiv I hI hm (UN.corner a) ((UN.toPi a).symm.trans eN)
  let g := gM.trans gN.symm
  let Φ : M ≃ₗ[R] N := (UM.toPi a).trans ((LinearEquiv.piCongrRight fun _ => g).trans (UN.toPi a).symm)
  have hΦ : ∀ y, UN.toPi a (Φ y) = fun l => g (UM.toPi a y l) := by
    intro y
    simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hΦE : ∀ i j (x : M), Φ (E i j • x) = E i j • Φ x := by
    intro i j x
    apply (UN.toPi a).injective
    have h1 := UM.toPi_E a i j x
    have h2 := UN.toPi_E a i j (Φ x)
    rw [units_E] at h1 h2
    rw [h2, hΦ, hΦ, h1]
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hΦO : ∀ (o : O) (x : M), Φ (o • x) = o • Φ x := by
    intro o x
    choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (φ o i j)
    have hφo : φ (∑ i, ∑ j, r i j • E i j) = φ o := by
      rw [map_sum]
      simp only [map_sum, map_smul, hE]
      refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
        (Matrix.matrix_eq_sum_single (φ o)).symm
      rw [Matrix.smul_single, ← hr i j, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rw [act_congr hker hM hφo.symm x, act_congr hker hN hφo.symm (Φ x)]
    simp only [Finset.sum_smul, smul_assoc, map_sum, map_smul, hΦE]
  exact ⟨{ Φ with map_smul' := fun o x => hΦO o x }⟩

end GlobalTheory.MoritaLocal
