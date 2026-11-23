import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVectorStatement
open Filter Topology TopologicalSpace TensorProduct
open GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer

theorem evT_map_shA {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
    {R : Type} [CommRing R] [Algebra ℂ R] {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k')
    (y : R ⊗[ℂ] Hol (K.W k)) :
    evT R p hp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) y) =
      evT R (F.shift l p) (K.maps h p hp) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.comp_apply, Hol.ev_apply, Hol.ev_apply, Charts.shA_apply, Charts.fn_sh h y hp]
    rfl

theorem close_taylor_shift : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  intro I _ _ g Λ _ F F₀ K K₀ R _ _ J N hJ r m hm hmm hτ l k k' k₀ k₀' h h₀ hW ρ ρ' hρ hρ'
  by_cases hne : ∃ p, p ∈ K₀.W k₀'
  swap
  · have e : ρ'.comp (Charts.sh h) =
        (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ :=
      RingHom.ext fun f ↦ GlobalTheory.tensor_hol_ext_of_values _ _ _ _ fun p hp ↦ (hne ⟨p, hp⟩).elim
    rw [e]
    exact Relation.ReflTransGen.refl
  obtain ⟨p₀, hp₀⟩ := hne
  have h0 : (0 : I → ℂ) ∈ F.V := K.base k' _ (hW p₀ hp₀)
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l _ h0
  obtain ⟨n, hn, hnn, hd⟩ := GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector J N hJ r m hm hmm (F.τ l) hτa
  have ht : ∀ i, (fun i ↦ ∑ j, m j i) i ∈ J := fun i ↦ J.sum_mem fun j _ ↦ hm j i
  have htN : ∀ s : Fin (N + 1) → I, ∏ a, (fun i ↦ ∑ j, m j i) (s a) = 0 :=
    fun s ↦ hJ _ fun a ↦ ht (s a)
  have hin : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k :=
    fun p hp ↦ K.maps h _ (hW p hp)
  obtain ⟨-, -, hconst, hgerm, -, -⟩ := taylor_formal_properties N (fun i ↦ ∑ j, m j i)
  refine close_of_sliceTaylor J N hJ _ ht r n hn hnn (K.W k) (K₀.W k₀') (fun p ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hin _ _ ?_ ?_
  · intro f p hp
    refine (hρ' (Charts.sh h f) p hp).trans ?_
    have hc : ContinuousAt (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) 0 := by fun_prop
    have e : (fun z ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      filter_upwards [hc.preimage_mem_nhds ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
      exact Charts.fn_sh h f hz
    rw [hgerm _ _ e, taylor_shear N _ htN f.fn (F.τ l) p.2 hτa (f.analytic _ (hin p hp))]
    simp only [hd]
  · intro f p hp
    refine (evT_map_shA h₀ p hp (ρ f)).trans ?_
    refine (hρ f _ _).trans ?_
    have e : (F₀.shift l p).2 = p.2 + F.τ l 0 := by
      change p.2 + F₀.τ l p.1 = _
      rw [hτ]
    rw [e]
    refine (taylor_shear N _ htN f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hin p hp))).trans ?_
    simp only [hconst, sub_self]

end GlobalTheory.AnPer
