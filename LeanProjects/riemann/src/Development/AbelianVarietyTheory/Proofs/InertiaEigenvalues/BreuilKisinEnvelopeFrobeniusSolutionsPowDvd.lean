import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem envelope_dvd_lpow_aux₁ {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (L a b : R) (u v : ι → R)
    (hL : L ∈ nonZeroDivisors R) (h : a * (L * b) = ∑ i ∈ s, L * u i * v i) : a * b = ∑ i ∈ s, u i * v i := by
  refine sub_eq_zero.1 ((mem_nonZeroDivisors_iff.mp hL).2 _ ?_)
  have e : ∑ i ∈ s, u i * v i * L = ∑ i ∈ s, L * u i * v i := Finset.sum_congr rfl fun i _ => by ring
  rw [sub_mul, Finset.sum_mul, e, ← h]
  ring

theorem envelope_dvd_lpow_aux₂ {R : Type} [CommRing R] (L w z : R) (k : ℕ)
    (hL : ∀ x : R, L * x = 0 → x = 0) (h : L * w = L ^ (k + 1) * z) : L ^ k ∣ w :=
  ⟨z, sub_eq_zero.1 (hL _ (by rw [mul_sub, h, pow_succ', mul_assoc, sub_self]))⟩

theorem envelope_dvd_lpow_aux₄ {R : Type} [CommRing R] (L x y : R) (k : ℕ) (hxy : x = L * y) (h : L ^ k ∣ y) :
    L ^ (k + 1) ∣ x := by
  rw [hxy, pow_succ']
  exact mul_dvd_mul_left _ h

theorem envelope_dvd_lpow_aux₃ {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} (σ : Hom B (ainfObj K))
    (x y : B.A) (k : ℕ) (hxy : x = (l : B.A) * y) (h : ((l : ℕ) : (ainfObj K).A) ^ (k + 1) ∣ σ.f x) :
    ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f y := by
  subst hxy
  obtain ⟨z, hz⟩ := h
  rw [map_mul, map_natCast] at hz
  exact envelope_dvd_lpow_aux₂ (R := Ainf l) (l : Ainf l) (σ.f y) z k ainf_torsionFree hz

theorem envelope_dvd_lpow_of_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  intro l _ K bk En κ _ c h k
  have hreg : ((l : ℕ) : En.Q.A) ∈ nonZeroDivisors En.Q.A :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk En.Q.A (BK.hf En.inl) (Digits l) En.tb).2.2.1
  induction k with
  | zero => intro x _ _ j; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx hσ j
    have h1 := GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct l K bk En κ x c h hx
      (fun g σ e1 e2 i => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) (hσ g σ e1 e2 i))
    choose y hy using h1
    have hyeq : ∀ j, BK.hf En.inl bk.E ^ h * y j = ∑ i, En.Q.D.φ (y i) * c i j := by
      intro j
      have hxj := hx j
      simp only [hy, map_mul, map_natCast] at hxj
      exact envelope_dvd_lpow_aux₁ Finset.univ _ _ _ (fun i => En.Q.D.φ (y i)) (fun i => c i j) hreg hxj
    have hσ' : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
        σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (y j) := by
      intro g σ e1 e2 i
      exact envelope_dvd_lpow_aux₃ σ (x i) (y i) k (hy i) (hσ g σ e1 e2 i)
    exact envelope_dvd_lpow_aux₄ _ _ _ k (hy j) (ih y hyeq hσ' j)

end GlobalTheory
