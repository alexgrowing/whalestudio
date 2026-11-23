import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.IdxSmulSubMap

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def matV {n : Type} [Fintype n] (Γ : Matrix n n K) : (n → V) →ₗ[K] (n → V) :=
  LinearMap.pi fun k => ∑ l, Γ k l • LinearMap.proj l

theorem matV_apply {n : Type} [Fintype n] (Γ : Matrix n n K) (x : n → V) (k : n) :
    matV Γ x k = ∑ l, Γ k l • x l := by
  simp [matV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem matV_mul {n : Type} [Fintype n] (A B : Matrix n n K) :
    (matV (A * B) : (n → V) →ₗ[K] (n → V)) = matV A ∘ₗ matV B := by
  apply LinearMap.ext; intro x; funext k
  simp only [matV_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem matV_one {n : Type} [Fintype n] [DecidableEq n] :
    (matV (1 : Matrix n n K) : (n → V) →ₗ[K] (n → V)) = LinearMap.id := by
  apply LinearMap.ext; intro x; funext k
  simp [matV_apply, Matrix.one_apply, ite_smul]

theorem matV_inv_cancel {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A (matV A⁻¹ x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem matV_inv_cancel' {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A⁻¹ (matV A x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]

theorem map_matV_pi {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (S : Submodule K V) :
    (Submodule.pi Set.univ fun _ : n => S).map (matV A) = Submodule.pi Set.univ fun _ : n => S := by
  have hsub : ∀ B : Matrix n n K, ∀ x ∈ (Submodule.pi Set.univ fun _ : n => S), matV B x ∈
      (Submodule.pi Set.univ fun _ : n => S) := by
    intro B x hx k _
    rw [matV_apply]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact hsub A x hx
  · intro x hx
    exact ⟨matV A⁻¹ x, hsub _ x hx, matV_inv_cancel A hA x⟩

def latPow (n : Type) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) (n → V) := Submodule.pi Set.univ fun _ : n => M

theorem span_latPow {n : Type} [Fintype n] [DecidableEq n] (M : Submodule (𝓞 K) V) :
    Submodule.span K ((latPow n M : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => Submodule.span K (M : Set V) :=
  span_pi_eq _

theorem span_map_matV {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0)
    (L : Submodule (𝓞 K) (n → V)) (S : Submodule K V)
    (hL : Submodule.span K (L : Set (n → V)) = Submodule.pi Set.univ fun _ : n => S) :
    Submodule.span K ((L.map ((matV A).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (n → V)) : Set (n → V)) =
      Submodule.pi Set.univ fun _ : n => S := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL, map_matV_pi A hA]

theorem matV_transvection {n : Type} [Fintype n] [DecidableEq n] (i j : n) (c : K) (x : n → V) :
    matV (Matrix.transvection i j c) x = x + Pi.single i (c • x j) := by
  funext k
  rw [matV_apply]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
    Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Pi.add_apply]
  by_cases hk : i = k
  · subst hk; simp
  · simp [hk, Pi.single_apply, Ne.symm hk]

theorem idx_matV (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {n : Type} [Fintype n] [DecidableEq n]
    (M : Submodule (𝓞 K) V) (hM : M.FG) (A : Matrix n n K) (hA : A.det ≠ 0) :
    idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det := by
  have hLfg : (latPow n M).FG := Submodule.fg_pi fun _ => hM
  have hsp := span_latPow (n := n) M
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det) A hA ?_ ?_ ?_
  ·
    intro D hD
    have hDk : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)
    have hmap : (latPow n M).map ((matV (Matrix.diagonal D)).restrictScalars (𝓞 K)) =
        Submodule.pi Set.univ fun k => smulSub (D k) M := by
      ext x
      simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mem_pi, Set.mem_univ,
        true_implies, latPow, mem_smulSub]
      constructor
      · rintro ⟨y, hy, rfl⟩ k
        exact ⟨y k, hy k, by rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul]⟩
      · intro h
        choose y hy hyx using h
        exact ⟨y, hy, by funext k; rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul, hyx]⟩
    rw [hmap, latPow, idx_pi hI w _ _ (fun _ => hM) (fun k => fg_smulSub _ M hM)
      (fun k => (span_smulSub _ (hDk k) M).symm), Matrix.det_diagonal,
      vAdd_prod w _ _ (fun k _ => hDk k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => idx_smulSub hI w (D k) (hDk k) M hM
  ·
    intro t
    rw [Matrix.TransvectionStruct.toMatrix, Matrix.det_transvection_of_ne _ _ t.hij]
    have hv1 : vAdd w (1 : K) = 0 := by simp [vAdd]
    rw [hv1, mul_zero]
    set φ : (n → V) →ₗ[K] (n → V) := LinearMap.id - (LinearMap.single K (fun _ => V) t.i) ∘ₗ LinearMap.proj t.i
      with hφ
    have hφapp : ∀ x : n → V, φ x = x - Pi.single t.i (x t.i) := fun x => by simp [hφ]
    have hφT : φ ∘ₗ matV (Matrix.transvection t.i t.j t.c) = φ := by
      apply LinearMap.ext; intro x
      rw [LinearMap.comp_apply, hφapp, hφapp, matV_transvection]
      funext k
      by_cases hk : k = t.i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    have hker0 : ∀ z : n → V, φ z = 0 ↔ ∀ k, k ≠ t.i → z k = 0 := by
      intro z
      rw [hφapp]
      constructor
      · intro h k hk
        have := congrFun h k
        simpa [Pi.single_apply, hk] using this
      · intro h
        funext k
        by_cases hk : k = t.i
        · subst hk; simp
        · simp [Pi.single_apply, hk, h k hk]
    have hfix : ∀ z : n → V, φ z = 0 → matV (Matrix.transvection t.i t.j t.c) z = z := by
      intro z hz
      rw [matV_transvection, (hker0 z).mp hz t.j (Ne.symm t.hij), smul_zero, Pi.single_zero, add_zero]
    have hT := span_map_matV (Matrix.transvection t.i t.j t.c)
      (by rw [Matrix.det_transvection_of_ne _ _ t.hij]; exact one_ne_zero) (latPow n M) _ hsp
    rw [idx_map hI w φ _ _ hLfg (hLfg.map _) (by rw [hT, hsp])]
    · rw [← Submodule.map_comp]
      have : ((φ.restrictScalars (𝓞 K)).comp ((matV (Matrix.transvection t.i t.j t.c)).restrictScalars (𝓞 K))) =
          φ.restrictScalars (𝓞 K) := by
        rw [← LinearMap.restrictScalars_comp, hφT]
      rw [this, idx_self]
    · ext z
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨hz, hz0⟩
        exact ⟨⟨z, hz, hfix z hz0⟩, hz0⟩
      · rintro ⟨⟨x, hx, rfl⟩, hz0⟩
        have hx0 : φ x = 0 := by
          rw [← hz0, ← LinearMap.comp_apply, hφT]
        rw [hfix x hx0]
        exact ⟨hx, by rw [hfix x hx0] at hz0; exact hz0⟩
  ·
    intro A B hA hB hPA hPB
    have hsB := span_map_matV B hB (latPow n M) _ hsp
    have hsA := span_map_matV A hA (latPow n M) _ hsp
    have hsAB := span_map_matV A hA _ _ hsB
    have hcomp : (latPow n M).map ((matV (A * B)).restrictScalars (𝓞 K)) =
        ((latPow n M).map ((matV B).restrictScalars (𝓞 K))).map ((matV A).restrictScalars (𝓞 K)) := by
      rw [← Submodule.map_comp, matV_mul, LinearMap.restrictScalars_comp]
    rw [hcomp, idx_chain hI w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) _ hLfg
      (hLfg.map _) ((hLfg.map _).map _) (by rw [hsA, hsp]) (by rw [hsAB, hsA])]
    have hinj : ∀ P : Submodule (𝓞 K) (n → V), ∀ x ∈ P, matV A x = 0 → x = 0 := by
      intro P x _ hx
      rw [← matV_inv_cancel' A hA x, hx, map_zero]
    rw [← idx_map_inj hI w (matV A) (latPow n M) _ hLfg (hLfg.map _) (by rw [hsB, hsp]) (hinj _) (hinj _),
      hPA, hPB, Matrix.det_mul, vAdd_mul w _ _ hA hB]
    ring

end Gen

end PI.Dv.TIW
