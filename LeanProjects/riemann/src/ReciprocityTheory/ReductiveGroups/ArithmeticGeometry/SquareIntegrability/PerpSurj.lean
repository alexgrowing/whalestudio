import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2.DimA

open Module

section Perp

variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)

theorem alt_swap (halt : ∀ h, B h h = 0) (x y : H) : B x y = -B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  linear_combination h

def perp (e f : H) : Submodule ℤ H := LinearMap.ker (B.flip e) ⊓ LinearMap.ker (B.flip f)

theorem mem_perp {e f h : H} : h ∈ perp B e f ↔ B h e = 0 ∧ B h f = 0 := by
  simp [perp]

variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he

theorem proj_mem (y : H) : y - B y f • e + B y e • f ∈ perp B e f := by
  have h1 : B f e = -1 := by rw [alt_swap B halt, he]
  rw [mem_perp]
  constructor <;> simp [halt, he, h1] <;> ring

def proj : H →ₗ[ℤ] perp B e f where
  toFun y := ⟨y - B y f • e + B y e • f, proj_mem B halt e f he y⟩
  map_add' x y := by ext; simp only [map_add, LinearMap.add_apply, add_smul, Submodule.coe_add]; abel
  map_smul' c x := by
    ext; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul, mul_smul,
      RingHom.id_apply, smul_add, smul_sub]

theorem proj_apply (y : H) : (proj B halt e f he y : H) = y - B y f • e + B y e • f := rfl

def splitEquiv : H ≃ₗ[ℤ] perp B e f × ℤ × ℤ where
  toFun y := (proj B halt e f he y, B y f, B y e)
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun p := (p.1 : H) + p.2.1 • e - p.2.2 • f
  left_inv y := by simp only [proj_apply]; abel
  right_inv p := by
    obtain ⟨⟨p, hp⟩, a, c⟩ := p
    have h1 : B f e = -1 := by rw [alt_swap B halt, he]
    rw [mem_perp] at hp
    have hf : B (p + a • e - c • f) f = a := by
      simp [hp.2, he, halt]
    have hE : B (p + a • e - c • f) e = c := by
      simp [hp.1, h1, halt]
    simp only [Prod.mk.injEq]
    refine ⟨?_, hf, hE⟩
    ext
    rw [proj_apply, hf, hE]
    abel

theorem perp_surj (hB : ∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) (φ : perp B e f →ₗ[ℤ] ℤ) :
    ∃ x : perp B e f, B.domRestrict₁₂ (perp B e f) (perp B e f) x = φ := by
  obtain ⟨x, hx⟩ := hB (φ.comp (proj B halt e f he))
  refine ⟨proj B halt e f he x, LinearMap.ext fun ⟨p, hp⟩ => ?_⟩
  have hp' := (mem_perp B).1 hp
  have hpe : B e p = 0 := by rw [alt_swap B halt, hp'.1, neg_zero]
  have hpf : B f p = 0 := by rw [alt_swap B halt, hp'.2, neg_zero]
  have hproj : proj B halt e f he p = ⟨p, hp⟩ := by
    ext; rw [proj_apply, hp'.1, hp'.2]; simp
  have hxp : B x p = φ (proj B halt e f he p) := by
    rw [hx]; rfl
  rw [LinearMap.domRestrict₁₂_apply, proj_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hpe, hpf, smul_eq_mul, mul_zero, sub_zero, add_zero]
  rw [hxp, hproj]

end Perp

theorem sympl : ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H],
    finrank ℤ H = n → ∀ B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ, (∀ h, B h h = 0) →
    (∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) →
    ∃ k, n = 2 * k ∧ ∃ e f : Fin k → H, (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn B halt hB
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, rfl, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  let b := Module.finBasisOfFinrankEq ℤ H hn
  obtain ⟨x, hx⟩ := hB (b.coord ⟨0, hpos⟩)
  have hxf : B x (b ⟨0, hpos⟩) = 1 := by rw [hx]; simp
  set e := x
  set f := b ⟨0, hpos⟩
  let Q := perp B e f
  haveI : Module.Free ℤ Q := Module.Free.of_basis (Q.basisOfPid b).2
  haveI : Module.Finite ℤ Q := Module.Finite.of_basis (Q.basisOfPid b).2
  have hr : finrank ℤ Q + 2 = n := by
    have h : finrank ℤ H = finrank ℤ (Q × ℤ × ℤ) := (splitEquiv B halt e f hxf).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hn] at h
    omega
  have halt' : ∀ h : Q, B.domRestrict₁₂ Q Q h h = 0 := fun h => halt h
  obtain ⟨k', hk', e', f', hee, hef⟩ :=
    ih (n - 2) (by omega) Q (by omega) (B.domRestrict₁₂ Q Q) halt'
      (perp_surj B halt e f hxf hB)
  refine ⟨k' + 1, by omega, Fin.cons e (fun i => (e' i : H)), Fin.cons f (fun i => (f' i : H)),
    ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using halt e
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (e' j).2).1, neg_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact ((mem_perp B).1 (e' i).2).1
      | succ j =>
        simp only [Fin.cons_succ]
        exact hee i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hxf
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [alt_swap B halt, ((mem_perp B).1 (f' j).2).1, neg_zero]
        simp [(Fin.succ_ne_zero j).symm]
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [((mem_perp B).1 (e' i).2).2]
        simp [Fin.succ_ne_zero i]
      | succ j =>
        simp only [Fin.cons_succ, Fin.succ_inj]
        exact hef i j

end ReciprocityTheory.ChartRestriction.G.I2.DimA
