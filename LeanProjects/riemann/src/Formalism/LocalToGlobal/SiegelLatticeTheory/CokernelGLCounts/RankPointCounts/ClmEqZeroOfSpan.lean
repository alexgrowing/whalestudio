import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne

noncomputable section

open scoped InnerProductSpace
open Matrix Formalism.MainNotions.S

namespace PI.SchurPlaces

section Tens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem eq_of_inner_span (tens : (∀ i, V i) → W) (hspan : Submodule.span ℂ (Set.range tens) = ⊤) {a b : W}
    (h : ∀ z, ⟪tens z, a⟫_ℂ = ⟪tens z, b⟫_ℂ) : a = b := by
  have h2 : ∀ w ∈ Submodule.span ℂ (Set.range tens), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, h z, sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h3 := h2 (a - b) (by rw [hspan]; exact Submodule.mem_top)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

theorem prod_upd_left (y z : ∀ i, V i) (i₀ : ι) (b : V i₀) :
    ∏ i, ⟪Function.update y i₀ b i, z i⟫_ℂ = ⟪b, z i₀⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem prod_upd_right (y z : ∀ i, V i) (i₀ : ι) (c : V i₀) :
    ∏ i, ⟪y i, Function.update z i₀ c i⟫_ℂ = ⟪y i₀, c⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

variable (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
  (hspan : Submodule.span ℂ (Set.range tens) = ⊤)

include hin hspan in
theorem tens_upd_add (x : ∀ i, V i) (i₀ : ι) (p q : V i₀) :
    tens (Function.update x i₀ (p + q)) = tens (Function.update x i₀ p) + tens (Function.update x i₀ q) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_add_right, hin, hin, hin, prod_upd_right, prod_upd_right, prod_upd_right, inner_add_right, add_mul]

include hin hspan in
theorem tens_upd_smul (x : ∀ i, V i) (i₀ : ι) (c : ℂ) (p : V i₀) :
    tens (Function.update x i₀ (c • p)) = c • tens (Function.update x i₀ p) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_smul_right, hin, hin, prod_upd_right, prod_upd_right, inner_smul_right, mul_assoc]

def insertLocal (x : ∀ i, V i) (i₀ : ι) : V i₀ →ₗ[ℂ] W where
  toFun p := tens (Function.update x i₀ p)
  map_add' p q := tens_upd_add tens hin hspan x i₀ p q
  map_smul' c p := tens_upd_smul tens hin hspan x i₀ c p

end Tens

theorem clm_eq_zero_of_span {W W' : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W']
    [InnerProductSpace ℂ W'] {S : Set W'} (hS : Submodule.span ℂ S = ⊤) (P : W' →L[ℂ] W) (h : ∀ w ∈ S, P w = 0) :
    P = 0 := by
  ext w
  have h1 : (P : W' →ₗ[ℂ] W) = ((0 : W' →L[ℂ] W) : W' →ₗ[ℂ] W) :=
    LinearMap.ext_on hS (fun v hv => by simp [h v hv])
  exact LinearMap.congr_fun h1 w

theorem jm_allPos' (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem memU_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  simp only [UJset, Set.mem_setOf_eq, Formalism.REAL.inUJ, jm_allPos', Matrix.mul_one]

theorem memU_mul {k : ℕ} {a b : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) (hb : b ∈ UJset (allPos k)) :
    a * b ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.one_mul, hb]

theorem memU_star {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : aᴴ ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 ha

theorem memU_rinv {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : a * aᴴ = 1 :=
  mul_eq_one_comm.1 ((memU_iff a).1 ha)

theorem memU_one (k : ℕ) : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ UJset (allPos k) := by
  rw [memU_iff]; simp

private theorem inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H} (hσ : IsHCTypeU k u σ) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ UJset (allPos k)) (v w : H) : ⟪v, σ h w⟫_ℂ = ⟪σ hᴴ v, w⟫_ℂ := by
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hnorm, _⟩, _⟩ := hσ
  have hs : hᴴ ∈ UJset (allPos k) := memU_star hh
  have e : hᴴ * h = 1 := (memU_iff h).mp hh
  have hinv : σ hᴴ (σ h w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hs _ hh, e, h1, ContinuousLinearMap.one_apply]
  let L : H →ₗᵢ[ℂ] H := ⟨(σ hᴴ : H →ₗ[ℂ] H), fun x => hnorm _ hs x⟩
  have key := L.inner_map_map v (σ h w)
  change ⟪σ hᴴ v, σ hᴴ (σ h w)⟫_ℂ = _ at key
  rw [hinv] at key
  exact key.symm

private theorem inner_tens_apply_eq_inner_update_adjoint {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hspan : Submodule.span ℂ (Set.range tens) = ⊤) (i₀ : ι) (f g : V i₀ →L[ℂ] V i₀)
    (hfg : ∀ a b, ⟪a, f b⟫_ℂ = ⟪g a, b⟫_ℂ) (T : W →L[ℂ] W)
    (hT : ∀ z, T (tens z) = tens (Function.update z i₀ (f (z i₀)))) (y : ∀ i, V i) (w : W) :
    ⟪tens y, T w⟫_ℂ = ⟪tens (Function.update y i₀ (g (y i₀))), w⟫_ℂ := by
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [hT, hin, hin, prod_upd_right, prod_upd_left, hfg]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, inner_add_right, inner_add_right, ha, hb]
  | smul c a _ ha => rw [map_smul, inner_smul_right, inner_smul_right, ha]

theorem schurCoreA_of (h7 : Formalism.MainNotions.NonGenericAndKTwoTheorems.adm7) : SchurCoreA := by
  classical
  unfold SchurCoreA
  intro k ι _ V V' _ _ _ _ _ _ W W' _ _ _ _ _ _ tens tens' hin hspan hin' hspan' π π' lam lam' hπ hπ' i₀ hne C hC P hP
  have hπ1 : ∀ i, π i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ i
    exact h1
  have hπ'1 : ∀ i, π' i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ' i
    exact h1
  have hπ'mul : ∀ a ∈ UJset (allPos k), ∀ b ∈ UJset (allPos k), π' i₀ (a * b) = π' i₀ a ∘L π' i₀ b := by
    obtain ⟨_, _, ⟨⟨_, hm⟩, _⟩, _⟩ := hπ' i₀
    exact hm
  have key : ∀ h ∈ UJset (allPos k), ∀ (y : ∀ i, V i) (y' : ∀ i, V' i),
      ⟪tens y, P (tens' (Function.update y' i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (y' i₀))))⟫_ℂ =
        ⟪tens (Function.update y i₀ (π i₀ hᴴ (y i₀))), P (tens' y')⟫_ℂ := by
    intro h hh y y'
    have hM : ∀ i, Function.update (fun _ => (1 : Matrix (Fin k) (Fin k) ℂ)) i₀ h i ∈ UJset (allPos k) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simpa using hh
      · rw [Function.update_of_ne hi]
        exact memU_one k
    obtain ⟨A, B, hA, hB, hAB⟩ := hP _ hM
    have hA' : ∀ z, A (tens z) = tens (Function.update z i₀ (π i₀ h (z i₀))) := by
      intro z
      rw [hA]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, hπ1]
    have hB' : ∀ z, B (tens' z) = tens' (Function.update z i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (z i₀))) := by
      intro z
      rw [hB]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, memU_rinv (hC i), hπ'1]
    rw [← hB', ← ContinuousLinearMap.comp_apply P B, ← hAB, ContinuousLinearMap.comp_apply]
    exact inner_tens_apply_eq_inner_update_adjoint tens hin hspan i₀ (π i₀ h) (π i₀ hᴴ) (fun a b => inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh a b) A hA' y _
  have main : ∀ (x : ∀ i, V i) (x' : ∀ i, V' i), ⟪tens x, P (tens' x')⟫_ℂ = 0 := by
    intro x x'
    obtain ⟨Q, hQ⟩ : ∃ Q : V' i₀ →L[ℂ] V i₀, ∀ p q,
        ⟪p, Q q⟫_ℂ = ⟪tens (Function.update x i₀ p), P (tens' (Function.update x' i₀ q))⟫_ℂ := by
      let S : V i₀ →L[ℂ] W := LinearMap.toContinuousLinearMap (insertLocal tens hin hspan x i₀)
      let S' : V' i₀ →L[ℂ] W' := LinearMap.toContinuousLinearMap (insertLocal tens' hin' hspan' x' i₀)
      refine ⟨ContinuousLinearMap.adjoint S ∘L P ∘L S', fun p q => ?_⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rfl
    have hint : ∀ h ∈ UJset (allPos k), Q ∘L π' i₀ (C i₀ * h * (C i₀)ᴴ) = π i₀ h ∘L Q := by
      intro h hh
      ext q
      apply ext_inner_left ℂ
      intro p
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hQ, inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh, hQ]
      have e := key h hh (Function.update x i₀ p) (Function.update x' i₀ q)
      simp only [Function.update_idem, Function.update_self] at e
      exact e
    have hc := hC i₀
    have hR : ∀ h ∈ UJset (allPos k), (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ h = π i₀ h ∘L (Q ∘L π' i₀ (C i₀)) := by
      intro h hh
      have hch : C i₀ * h ∈ UJset (allPos k) := memU_mul hc hh
      have hchc : C i₀ * h * (C i₀)ᴴ ∈ UJset (allPos k) := memU_mul hch (memU_star hc)
      have e : C i₀ * h = C i₀ * h * (C i₀)ᴴ * C i₀ := by
        rw [Matrix.mul_assoc (C i₀ * h), (memU_iff _).mp hc, Matrix.mul_one]
      rw [ContinuousLinearMap.comp_assoc, ← hπ'mul _ hc _ hh, e, hπ'mul _ hchc _ hc,
        ← ContinuousLinearMap.comp_assoc Q, hint h hh, ContinuousLinearMap.comp_assoc (π i₀ h)]
    have hR0 : Q ∘L π' i₀ (C i₀) = 0 :=
      h7 k (lam i₀) (lam' i₀) (V i₀) (V' i₀) (π i₀) (π' i₀) (hπ i₀) (hπ' i₀) hne _ hR
    have hQ0 : Q = 0 := by
      have e1 : π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ = 1 := by
        rw [← hπ'mul _ hc _ (memU_star hc), memU_rinv hc, hπ'1]
      calc Q = Q ∘L (π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ) := by
            rw [e1]
            ext
            simp
        _ = (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ (C i₀)ᴴ := (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = 0 := by rw [hR0, ContinuousLinearMap.zero_comp]
    have e2 := hQ (x i₀) (x' i₀)
    rw [Function.update_eq_self, Function.update_eq_self, hQ0] at e2
    simpa using e2.symm
  apply clm_eq_zero_of_span hspan' P
  rintro w ⟨x', rfl⟩
  exact eq_of_inner_span (a := P (tens' x')) (b := 0) tens hspan (fun x => by rw [main x x', inner_zero_right])

end PI.SchurPlaces
