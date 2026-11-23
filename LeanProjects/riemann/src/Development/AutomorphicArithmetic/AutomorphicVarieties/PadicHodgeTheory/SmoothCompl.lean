import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothComplA
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDerivationsDualToCotangentParameters
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PowerSeriesApproximationModMaximal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsHomogeneousLiftModKerPowSuccSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfHomogeneousAevalMemMaximalIdealPowSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNotMemMulMemIdealOfForallPrimePowSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HeightKerSectionLeOfCotangentGenerators
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimMvPowerSeriesFinField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimEqHeightKerSectionAddOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem sc_pi (E : Type) [Field E] (n k : ℕ) :
    ∃ π : (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (k + 2)) →ₐ[E] E,
      (∀ g, π (Ideal.Quotient.mk _ g) = MvPowerSeries.constantCoeff g) ∧ ∀ a, π a = 0 → IsNilpotent a := by
  let cc : MvPowerSeries (Fin n) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) E →+* E) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  refine ⟨Ideal.Quotient.liftₐ _ cc fun g hg => (sc_max E n g).1 (Ideal.pow_le_self (by omega) hg),
    fun g => rfl, fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨k + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ((sc_max E n g).2 ha) _

private theorem sc_inj {O E R : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E)
    (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I)
    (N : ℕ) : ∀ a, φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N →
      ∃ e : O, e ≠ 0 ∧ e • a ∈ RingHom.ker x ^ N ⊔ I := by
  have hmap : ∀ k, ∀ b ∈ RingHom.ker x ^ k ⊔ I, φ b ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k := by
    intro k
    have : RingHom.ker x ^ k ⊔ I ≤ (maximalIdeal (MvPowerSeries (Fin n) E) ^ k).comap (φ : R →+* _) := by
      refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) k) (Ideal.le_comap_pow _ k)) fun y hy => ?_
      · refine (sc_max E n (φ y)).2 ?_
        rw [hconst, show x y = 0 from hy, map_zero]
      · show φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k
        rw [show φ y = 0 from hI hy]
        exact zero_mem _
    exact fun b hb => this hb
  induction N with
  | zero => exact fun a _ => ⟨1, one_ne_zero, by simp⟩
  | succ N ih =>
    intro a ha
    obtain ⟨e, he, h1⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ N) ha)
    obtain ⟨b, hb, i, hi, hbi⟩ := Submodule.mem_sup.1 h1
    obtain ⟨e', h, he', hh, h2⟩ := UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup O R I x n t ht0 hspan N b hb
    have hφb : φ b = e • φ a := by
      rw [← map_smul, ← hbi, map_add, show φ i = 0 from hI hi, add_zero]
    have h3 : MvPolynomial.aeval (fun j => φ (t j)) h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) := by
      have h4 := hmap _ _ h2
      rw [map_sub, map_smul, hφb, MvPolynomial.comp_aeval_apply] at h4
      have h5 : e' • e • φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) :=
        Submodule.smul_of_tower_mem _ _ (Submodule.smul_of_tower_mem _ _ ha)
      simpa using sub_mem h5 h4
    have h0 := UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ O E n _ c hc ht N h hh h3
    rw [h0, map_zero, sub_zero] at h2
    refine ⟨e' * e, mul_ne_zero he' he, ?_⟩
    rw [mul_smul, ← hbi, smul_add]
    exact add_mem h2 (Ideal.mem_sup_right (Submodule.smul_of_tower_mem _ _ hi))

private theorem sc_dim {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ringKrullDim (R ⧸ RingHom.ker φ) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have : IsCO O (R ⧸ RingHom.ker φ) :=
    co_quot O R _ (Ideal.Quotient.mkₐ O _) Ideal.Quotient.mk_surjective
  have hPx : ∀ a ∈ RingHom.ker φ, x a = 0 := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨x', hx'⟩ : ∃ x' : (R ⧸ RingHom.ker φ) →ₐ[O] O, ∀ a, x' (Ideal.Quotient.mk _ a) = x a :=
    ⟨Ideal.Quotient.liftₐ _ x hPx, fun _ => rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : (R ⧸ RingHom.ker φ) →ₐ[O] MvPowerSeries (Fin n) E,
      ∀ a, φ' (Ideal.Quotient.mk _ a) = φ a := ⟨Ideal.Quotient.liftₐ _ φ fun _ h => h, fun _ => rfl⟩
  have h1 := UpperTheory.ringKrullDim_mvPowerSeries_fin_field O E _ x' n φ' (fun i => Ideal.Quotient.mk _ (t i)) c hc
    (fun a => by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hφ', hx', hconst])
    (fun i => by rw [hφ']; exact ht i)
  have h2 := UpperTheory.height_ker_section_le_of_cotangent_generators O _ x' n (fun i => Ideal.Quotient.mk _ (t i)) (fun i => by rw [hx', ht0])
    (fun a ha => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨e, o, he, h⟩ := hspan a (by rw [← hx', ha])
      refine ⟨e, o, he, ?_⟩
      have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker x' ^ 2).comap (Ideal.Quotient.mk (RingHom.ker φ)) := by
        refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)) fun y hy => ?_
        · exact (hx' y).trans hy
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (hI hy)]
          exact zero_mem _
      have h3 : Ideal.Quotient.mkₐ O (RingHom.ker φ) (e • a - ∑ i, o i • t i) ∈ RingHom.ker x' ^ 2 := hle h
      simpa only [map_sub, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using h3)
  rw [UpperTheory.ringKrullDim_eq_height_ker_section_add_one O _ x', le_antisymm h2 h1]
  norm_cast

private theorem sc_end {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (hIx : I ≤ RingHom.ker x) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ∃ P : Ideal R, UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧
      (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧
      ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hinj := sc_inj I x n φ t c hc hI hconst ht0 ht hspan
  have hPx : RingHom.ker φ ≤ RingHom.ker x := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨y, hy, hyP⟩ := UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup R I (RingHom.ker x) (RingHom.ker φ) (RingHom.ker_isPrime _) hIx
    fun a ha N => by
      obtain ⟨e, he, h⟩ := hinj N a (by rw [show φ a = 0 from ha]; exact zero_mem _)
      refine ⟨algebraMap O R e, fun h' => he ?_, by rwa [← Algebra.smul_def]⟩
      simpa using h'
  have hle : ∀ Q : Ideal R, Q.IsPrime → I.radical ≤ Q → Q ≤ RingHom.ker x → RingHom.ker φ ≤ Q :=
    fun Q hQ h1 h2 a ha => (hQ.mem_or_mem (h1 (Ideal.le_radical (hyP a ha)))).resolve_left fun h => hy (h2 h)
  have hrad : I.radical ≤ RingHom.ker φ := hP.radical_le_iff.2 hI
  refine ⟨RingHom.ker φ, ⟨rfl, hconst, UpperTheory.power_series_approximation_mod_maximal O E R n φ t c hc ht, fun N a ha => ?_⟩, hI, ⟨y, hy, hyP⟩,
    fun Q hQ => ⟨fun h => ?_, fun h => h ▸ hPx⟩, ⟨⟨hP, hrad⟩, fun Q hQ h => hle Q hQ.1 hQ.2 (h.trans hPx)⟩,
    sc_dim I x n φ t c hc hI hconst ht0 ht hspan⟩
  · obtain ⟨e, he, h⟩ := hinj N a ha
    exact ⟨e, he, sup_le_sup_left hI _ h⟩
  · have h1 := hle Q hQ.1.1 hQ.1.2 h
    exact le_antisymm (hQ.2 ⟨hP, hrad⟩ h1) h1

theorem UpperTheory.V.Loc.smoothCompl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ f' : R →ₐ[O] B', I ≤ RingHom.ker f' → (∀ a, π' (f' a) = algebraMap O E (x a)) → ∃ f : R →ₐ[O] B, I ≤ RingHom.ker f ∧ ∀ a, p (f a) = f' a) → ∃ (n : ℕ) (P : Ideal R) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧ (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧ ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ R _ _ _ I x hIx H
  obtain ⟨n, D, t, c, hc, hD, hDI, ht0, htD, hspan⟩ := UpperTheory.exists_derivations_dual_to_cotangent_parameters O E R I x hIx
  obtain ⟨f₀, hf₀⟩ := sc_first x n D hD
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) E)) (MvPowerSeries (Fin n) E) := by
    rw [← sc_span]; infer_instance
  have hfin : ∀ k, Module.Finite ℚ_[l] (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
    fun k => by
      have : Module.Finite E (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
        GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le (N := k) (by rw [sc_span])
      exact Module.Finite.trans E _
  have hc0 : ∀ a g, Ideal.Quotient.mk _ g = f₀ a → MvPowerSeries.constantCoeff g = algebraMap O E (x a) := by
    intro a g hg
    rw [hf₀, Ideal.Quotient.eq] at hg
    have := (sc_max E n _).1 (Ideal.pow_le_self (by omega) hg)
    simpa [sub_eq_zero] using this
  obtain ⟨φ, hφI, hφ⟩ := sc_tower (maximalIdeal (MvPowerSeries (Fin n) E)) I f₀
    (fun a ha => by
      rw [RingHom.mem_ker, hf₀, show x a = 0 from hIx ha]
      simp [hDI _ a ha])
    (fun N f' h1 h2 => by
      obtain ⟨π, hπ, hn⟩ := sc_pi E n (N + 1)
      obtain ⟨π', hπ', hn'⟩ := sc_pi E n N
      have := hfin (N + 1 + 2)
      have := hfin (N + 2)
      refine H _ π hn _ π' hn' (Ideal.Quotient.factorₐ E (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)))
        (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2))) (AlgHom.ext fun b => ?_) f' h1 fun a => ?_
      · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (hπ' g).trans (hπ g).symm
      · obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f' a)
        rw [← hg, hπ']
        refine hc0 a g ?_
        rw [← h2, ← hg, Ideal.Quotient.factor_mk])
  obtain ⟨P, hP⟩ := sc_end I x hIx n φ t c hc hφI (fun a => hc0 a _ (hφ a)) ht0 (fun i => by
    have h := hφ (t i)
    rw [hf₀, Ideal.Quotient.eq] at h
    simpa [ht0, htD, apply_ite, Algebra.smul_def, MvPowerSeries.algebraMap_apply] using h) hspan
  exact ⟨n, P, φ, hP⟩
