import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_threshold_mem_box {m : ℕ} (y : Fin m → k) (t₀ : kˣ) :
    ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ t : kˣ, valuation k (t₁ : k) ≤ valuation k (t : k) → y ∈ box m t := by
  classical
  have hstep : ∀ (S : Finset (Fin m)), ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ j ∈ S, valuation k (y j) ≤ valuation k (t₁ : k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨t₀, le_rfl, by simp⟩
    | insert a S _ ih =>
      obtain ⟨t₁, h0, h1⟩ := ih
      by_cases hle : valuation k (y a) ≤ valuation k (t₁ : k)
      · refine ⟨t₁, h0, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hle
        · exact h1 j hj
      · have hlt := lt_of_not_ge hle
        have hya : y a ≠ 0 := by
          intro h0'
          rw [h0', map_zero] at hlt
          exact not_lt_zero' hlt
        refine ⟨Units.mk0 (y a) hya, ?_, fun j hj => ?_⟩
        · simpa using h0.trans hlt.le
        · rcases Finset.mem_insert.1 hj with rfl | hj
          · simp
          · simpa using (h1 j hj).trans hlt.le
  obtain ⟨t₁, h0, h1⟩ := hstep Finset.univ
  exact ⟨t₁, h0, fun t ht j => (h1 j (Finset.mem_univ j)).trans ht⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem setIntegral_box_add (ν : Measure k) [ν.IsAddHaarMeasure] {m : ℕ} (t : kˣ) {y : Fin m → k}
    (hy : y ∈ box m t) (f : (Fin m → k) → ℂ) :
    ∫ x in (box m t : Set (Fin m → k)), f (x + y) ∂(piHaar ν m) =
      ∫ x in (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) := by
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : (piHaar ν m).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hpre : (fun x => x + y) ⁻¹' (box m t : Set (Fin m → k)) = box m t := by
    ext x
    exact (box m t).add_mem_cancel_right hy
  have := (measurePreserving_add_right (piHaar ν m) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) f (box m t : Set (Fin m → k))
  rwa [hpre] at this

theorem wt_sub (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x - y) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x - y) (Fin.last n) = y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.sub_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem wt_add (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x + y) = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x + y) (Fin.last n) = -y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.add_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem EvVal_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB y v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨t₁, h01, h1⟩ := exists_threshold_mem_box y t₀
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.mirabolic_coefficient_translation T T' B s hB
  refine ⟨⟨t₁, fun t ht => ?_⟩, ⟨t₁, fun t ht => ?_⟩⟩
  · have hy := h1 t ht
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy (fun x => wt ψ n (x - y) * coef T B v v' x)
    simp only [add_sub_cancel_right] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) (T (uM (n + 1) y) v) v' =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x + y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc1]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_sub, mul_assoc]
  · have hy := h1 t ht
    have hy' : -y ∈ box (n + 1) t := neg_mem hy
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy' (fun x => wt ψ n (x + y) * coef T B v v' x)
    simp only [← sub_eq_add_neg, sub_add_cancel] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v (T' (uM (n + 1) y) v') =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x - y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc2]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_add, mul_assoc]

end GlobalTheory.CompanionTheory.MirPair

end
