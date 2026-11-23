import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVSumTmul

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) z) = sigR σ (v.adicCompletion F) (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [prV, sigR, evalV, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, evalV, Algebra.TensorProduct.map_tmul]

def single {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F := by
  classical
  exact adOf (Pi.single v a) (fun w => by
    by_cases h : w = v
    · subst h; simpa using ha
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _)

theorem single_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : single v a ha v = a := by
  classical
  simp [single, adOf_apply]

theorem lift_lat (hG : PLGen) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x ∈ latV v Lb) :
    ∃ y ∈ latA F Lb, (fun j => prV (E := E) v (y j)) = x := by
  obtain ⟨k, m, hm, hgen⟩ := exists_gen Lb hfin
  obtain ⟨a, ha, rfl⟩ :=
    (hG F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Lb m hm hgen x).1 hx
  refine ⟨fun j => ∑ i, m i j ⊗ₜ[F] single v (a i) (ha i), ?_, ?_⟩
  · exact (hG F E (FiniteAdeleRing (𝓞 F) F) (intAd F) n k Lb m hm hgen _).2
      ⟨fun i => single v (a i) (ha i), fun i => adOf_mem _ _, rfl⟩
  · funext j
    rw [prV_sum_tmul]
    simp only [single_apply]

theorem plLocal_of (hG : PLGen) (hD : PLDown) : PLLocal := by
  intro F E _ _ _ _ _ n σ J Lb hfin g hg v
  have fwd : ∀ h ∈ levelAfL σ J Lb, ∀ x ∈ latV v Lb,
      ((bc (prV (E := E) v) h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latV v Lb := by
    intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := lift_lat hG Lb hfin v x hx
    rw [← bc_mulVec]
    exact hD F E n Lb v _ (((Subgroup.mem_inf.1 hh).2 y).1 hy)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hU := (Subgroup.mem_inf.1 hg).1
    change cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (g : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) at hU
    change cT (sigR σ (v.adicCompletion F)) ((g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
    have e2 : J.map (inclE (F := F) (v.adicCompletion F)) =
        (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) := by
      ext i j; simp [prV_inclE]
    have e3 : cT (sigR σ (v.adicCompletion F)) ((g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
        (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
      ext i j; simp [cT, prV_sigR]
    rw [e3, e2, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  · intro x
    constructor
    · exact fwd g hg x
    · intro hx
      have h2 := fwd g⁻¹ (inv_mem hg) _ hx
      rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2

end PI.LPI
