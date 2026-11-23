import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRayStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.FaceSub

variable {X : Type} [AddCommGroup X]

theorem eq_of_toReal_sum_eq {p : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} (hu : LinearIndependent ℤ u)
    {r r' : Fin p → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ j, r' j • toReal (u j)) : r = r' := by
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin p → ℤ), ∑ j, c j • u j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c hc => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    exact funext (Fintype.linearIndependent_iff.1 hu c hc)
  have h0 : ∑ j, (r - r') j • toReal (u j) = ∑ k, (Fin.elim0 k : ℝ) • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self, Finset.univ_eq_empty, Finset.sum_empty]
  exact sub_eq_zero.1 (eq_zero_of_toReal_rel hind h0)

theorem eq_zero_of_toReal_eq_zero {β : LinearMap.BilinForm ℤ X} (h : toReal β = 0) : β = 0 :=
  LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.zero_apply] at this
    simpa using this

theorem exists_ray {p q : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} {v : Fin q → LinearMap.BilinForm ℤ X}
    (hu : LinearIndependent ℤ u) (hv : ∀ l, v l ≠ 0) (A : Fin q → ℝ) (B : Fin q → Fin p → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hB : ∀ l k', 0 ≤ B l k') (k : Fin p) (hk : toReal (u k) = ∑ l, A l • toReal (v l))
    (hBe : ∀ l, 0 < A l → toReal (v l) = ∑ k', B l k' • toReal (u k')) :
    ∃ l, 0 < A l ∧ ∃ c : ℝ, 0 < c ∧ toReal (v l) = c • toReal (u k) := by
  classical
  set B' : Fin q → Fin p → ℝ := fun l k' => if 0 < A l then B l k' else 0 with hB'
  have hB'0 : ∀ l k', 0 ≤ B' l k' := fun l k' => by
    simp only [hB']; split_ifs <;> [exact hB l k'; exact le_rfl]
  have hterm : ∀ l, A l • toReal (v l) = A l • ∑ k', B' l k' • toReal (u k') := fun l => by
    rcases (hA l).lt_or_eq with hl | hl
    · simp only [hB', if_pos hl]; rw [hBe l hl]
    · simp [← hl]
  have hsum : ∑ k', (if k' = k then (1 : ℝ) else 0) • toReal (u k') =
      ∑ k', (∑ l, A l * B' l k') • toReal (u k') := by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    rw [if_pos rfl, one_smul, hk]
    simp only [hterm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc := eq_of_toReal_sum_eq hu hsum
  have hk1 : ∑ l, A l * B' l k = 1 := by simpa using (congrFun hc k).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, A l * B' l k ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero hne] at hk1
    exact zero_ne_one hk1
  have hAl : 0 < A l := (hA l).lt_of_ne fun h0 => hl (by rw [← h0, zero_mul])
  have hoff : ∀ k', k' ≠ k → B l k' = 0 := fun k' hk' => by
    have h0 : ∑ l, A l * B' l k' = 0 := by simpa [hk'] using (congrFun hc k').symm
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hA l) (hB'0 l k'))).1 h0 l (Finset.mem_univ _)
    simpa [hB', if_pos hAl, hAl.ne'] using this
  have hvl : toReal (v l) = B l k • toReal (u k) := by
    rw [hBe l hAl, Finset.sum_eq_single k (fun b _ hb => by rw [hoff b hb, zero_smul]) (by simp)]
  refine ⟨l, hAl, B l k, (hB l k).lt_of_ne fun h0 => hv l (eq_zero_of_toReal_eq_zero ?_), hvl⟩
  rw [hvl, ← h0, zero_smul]

end GlobalTheory.PolFan.FaceSub

open GlobalTheory.PolFan.FaceSub in

theorem GlobalTheory.PolFan.eq_subfamily_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  intro O _ bar X _ _ m n δ γ hδ hγ h hδi hγi hδp hγp hγc hδn hγz hZ
  classical
  choose b hb hbe using hγc
  choose a ha hae using hZ
  have hsupp : ∀ j i, 0 < b j i → h (δ i) = 0 := fun j i hji => by
    have e := apply_eq_of_toReal_eq (hbe j) h
    rw [hγz j, Int.cast_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hb j i) (by exact_mod_cast hδn i))).1 e.symm i
      (Finset.mem_univ _)
    have h2 : ((h (δ i) : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hji.ne'
    exact_mod_cast h2
  have hex1 : ∀ i, h (δ i) = 0 → ∃ j, γ j = δ i := fun i hi => by
    obtain ⟨j, -, c, hc, e⟩ := exists_ray hδi hγi.ne_zero (a i hi) b (ha i hi) hb i (hae i hi) (fun l _ => hbe l)
    exact ⟨j, GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (γ j) (δ i) (hγ j) (hδ i) (hγp j) (hδp i) c hc e⟩
  have hex2 : ∀ j, ∃ i, h (δ i) = 0 ∧ γ j = δ i := fun j => by
    obtain ⟨i, hbi, c, hc, e⟩ := exists_ray hγi hδi.ne_zero (b j)
      (fun i => if hi : h (δ i) = 0 then a i hi else 0) (hb j)
      (fun i j' => by split_ifs with hi <;> [exact ha i hi j'; exact le_rfl]) j (hbe j)
      (fun l hl => by rw [dif_pos (hsupp j l hl)]; exact hae l _)
    exact ⟨i, hsupp j i hbi, (GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (δ i) (γ j) (hδ i) (hγ j) (hδp i) (hγp j) c hc e).symm⟩
  choose s hsZ hsγ using hex2
  have hsinj : Function.Injective s := fun j j' hjj => hγi.injective (by rw [hsγ j, hsγ j', hjj])
  refine ⟨⟨s, hsinj⟩, hsγ, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := hex1 i hi
    exact ⟨j, hδi.injective (show δ (s j) = δ i by rw [← hsγ j, hj])⟩
  · rintro ⟨j, rfl⟩
    exact hsZ j
