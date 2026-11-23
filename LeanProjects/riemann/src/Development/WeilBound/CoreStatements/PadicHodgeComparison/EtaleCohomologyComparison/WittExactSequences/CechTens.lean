import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl

set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

theorem test_of_pre : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (r : ℕ → B), Pf p B → IsRt p r → AIC B → VAL (r 0) → ∃ (T : Type) (_ : CommRing T) (g : B →+* T), Pf p T ∧ AIC T ∧ VAL (g (r 0)) ∧ IsAdicComplete (Ideal.span {g (r 0)}) T ∧ g (r 0) ∈ nonZeroDivisors T ∧ (∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g (r 0) ^ M}) ∧ (∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g (r 0) ^ M} → ∀ k, r k * x ∈ Ideal.span {r 0 ^ M}) ∧ ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x (r 0)}) T₁ → x (r 0) ∈ nonZeroDivisors T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := by
  intro p _ B _ r hB hr h1 h2
  obtain ⟨B₁, _, q, hq, hB₁, hreg, hker, ha, hv⟩ := Leaf.tors_quot p B (r 0) hB
  obtain ⟨T, _, g, hg⟩ := Leaf.compl_ex B₁ (q (r 0))
  refine ⟨T, inferInstance, g.comp q, Leaf.compl_pf p B₁ T _ g hg hB₁, Leaf.compl_aic B₁ T _ g hg hreg (ha h1) (hv h2),
    Leaf.compl_val B₁ T _ g hg (hv h2), hg.compl, Leaf.compl_reg B₁ T _ g hg hreg, fun M y => ?_, fun M x hx k => ?_,
    fun T₁ _ x hc hx => ?_⟩
  · obtain ⟨x, hx⟩ := hg.surj M y
    obtain ⟨x, rfl⟩ := hq x
    exact ⟨x, hx⟩
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hg.inj M (q x) hx)
    obtain ⟨b, rfl⟩ := hq b
    have e : r 0 ^ 1 * (x - b * r 0 ^ M) = 0 := by
      rw [pow_one, ← hker, map_sub, map_mul, map_pow, hb, sub_self]
    have e' := ((Leaf.pf_facts p B hB).2.2.2.2 r hr).2.2 1 _ e k
    exact Ideal.mem_span_singleton'.2 ⟨r k * b, by linear_combination -e'⟩
  · let x₁ : B₁ →+* T₁ := q.liftOfSurjective hq ⟨x, fun a ha => by
      have := congrArg x ((hker a).1 ha)
      rw [map_mul, map_zero] at this
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hx).1 this⟩
    have hx₁ : ∀ a, x₁ (q a) = x a := fun a => RingHom.liftOfSurjective_comp_apply _ _ _ a
    obtain ⟨ψ, hψ, hu⟩ := Leaf.compl_univ B₁ T _ g hg T₁ x₁ (by rw [hx₁]; exact hc)
    refine ⟨ψ, RingHom.ext fun a => (RingHom.congr_fun hψ (q a)).trans (hx₁ a), fun ψ' h' => hu ψ' (RingHom.ext fun a => ?_)⟩
    obtain ⟨a, rfl⟩ := hq a
    exact (RingHom.congr_fun h' a).trans (hx₁ a).symm

theorem cech_tens : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (A : Type) [CommRing A] [Algebra R A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] [∀ n, Algebra R (K n)] [∀ n, IsScalarTower R A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), IsRt p r → (∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M) → Pf p A → Pf p B → Cov p (fun k => algebraMap R A (r k)) B → (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → (∀ w : N ⊗[R] K 0, ((alt (δ 0)).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w = 0) ∧ ∀ (n : ℕ) (w : N ⊗[R] K (n + 1)), ((alt (δ (n + 1))).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (((alt (δ n)).restrictScalars R).lTensor N) := by
  intro p _ R _ _ _ r N _ _ A _ _ B _ _ K _ _ _ _ ι δ hr h1 hA hB hc hw hδ
  have hK : ∀ n, Pf p (K n) := fun n => Leaf.wp_pf p A B (K n) n (ι n) (hw n) hA hB
  have dd := Leaf.wp_dd A B K ι δ hw hδ
  obtain ⟨H, hH⟩ := Leaf.wp_htpy A B K ι δ hw hδ
  obtain ⟨e0, e1⟩ := Leaf.ami_exact p A B _ hA hc K (fun n => alt (δ n)) H hK dd hH
  have e1' : ∀ n z, ((alt (δ (n + 1))).restrictScalars R) z = 0 → ∀ k, r k • z ∈ LinearMap.range ((alt (δ n)).restrictScalars R) := by
    intro n z hz k
    obtain ⟨y, hy⟩ := e1 n z hz k
    exact ⟨y, hy.trans (algebraMap_smul A (r k) z)⟩
  have tor : ∀ n (a : R) (x : K n), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0 := by
    intro n a x ha hx k
    obtain ⟨M, c, hc⟩ := h1 a ha
    rw [Algebra.smul_def]
    refine ((Leaf.pf_facts p (K n) (hK n)).2.2.2.2 (fun k => algebraMap R (K n) (r k)) (fun k => by rw [← map_pow, hr k])).2.2 M x ?_ k
    rw [← map_pow, ← Algebra.smul_def, hc, mul_comm, mul_smul, hx, smul_zero]
  refine ⟨fun w hw k => ?_, fun n => Leaf.tens_exact p R r N _ _ _ _ _ _ ((alt (δ (n + 2))).restrictScalars R) hr
    (dd (n + 1)) (e1' n) (e1' (n + 1)) (tor _)⟩
  obtain ⟨y, hy⟩ := Leaf.tens_exact p R r N PUnit _ _ _ 0 _ ((alt (δ 1)).restrictScalars R) hr (dd 0)
    (fun z hz k => ⟨0, by rw [map_zero, ← algebraMap_smul A, e0 z hz k]⟩) (e1' 0) (tor _) w hw k
  rw [← hy, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem fin_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → IsRt p r → (∀ E ∈ 𝓔, ∀ (B : Type) [CommRing B] [Algebra A B], Pf p B → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra B B₁), Pf p B₁ ∧ Cov p (fun k => algebraMap A B (r k)) B₁ ∧ Pt ((algebraMap B B₁).comp (algebraMap A B)) E) → ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E := by
  intro p _ A _ r 𝓔 hA hr h J hJ
  induction J, hJ using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨A, inferInstance, inferInstance, hA, (Leaf.cov_mono p A r).1, fun _ h => h.elim⟩
  | @insert E J _ _ ih =>
    intro hs
    obtain ⟨B, _, _, hB, hc, hp⟩ := ih fun x hx => hs (Or.inr hx)
    obtain ⟨B₁, _, _, hB₁, hc₁, hp₁⟩ := h E (hs (Or.inl rfl)) B hB
    let _ : Algebra A B₁ := ((algebraMap B B₁).comp (algebraMap A B)).toAlgebra
    have : IsScalarTower A B B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine ⟨B₁, inferInstance, inferInstance, hB₁, Leaf.cov_comp p A B B₁ r hA hB hr hc hc₁, ?_⟩
    rintro E' (rfl | h')
    · exact hp₁
    · obtain ⟨y, hy⟩ := hp E' h'
      refine ⟨algebraMap B B₁ ∘ y, fun q hq => ?_⟩
      have := congrArg (algebraMap B B₁) (hy q hq)
      rwa [MvPolynomial.eval₂_comp_left, map_zero] at this

end CrystallineSemistableComparison.D
