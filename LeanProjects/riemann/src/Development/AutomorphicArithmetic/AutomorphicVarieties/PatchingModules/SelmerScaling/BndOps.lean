import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section SlopeTestRemainingChoices
variable {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {I : Ideal A} {t : A}

private theorem ac_const (c : A) : AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

end SlopeTestRemainingChoices

private theorem adicCont_add_and_adicCont_mul {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ ψ : G → R}
    (hφ : AdicCont I φ) (hψ : AdicCont I ψ) :
    AdicCont I (fun g => φ g + ψ g) ∧ AdicCont I (fun g => φ g * ψ g) := by
  unfold AdicCont at *
  constructor
  · intro N
    simpa [map_add] using (hφ N).comp₂ (hψ N) (· + ·)
  · intro N
    simpa [map_mul] using (hφ N).comp₂ (hψ N) (· * ·)

private theorem adicCont_neg_of_adicCont {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ : G → R}
    (hφ : AdicCont I φ) : AdicCont I (fun g => -φ g) := by
  unfold AdicCont at *
  intro N
  simpa [map_neg, Function.comp_def] using (hφ N).comp (fun y => -y)

private theorem adicCont_comp_inv_of_isTopologicalGroup {R G : Type} [CommRing R] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {I : Ideal R} {φ : G → R} (hφ : AdicCont I φ) : AdicCont I (fun g => φ g⁻¹) := by
  unfold AdicCont at *
  intro N
  exact (hφ N).comp_continuous continuous_inv

theorem UpperTheory.V.Pa.bndOps :
    ∀ (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G], (∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c) ∧ (∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧ BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹) ∧ (∀ (ι : Type) (s : Finset ι) (φ : ι → G → FractionRing (PowerSeries K)), (∀ i ∈ s, BndF (PowerSeries.X : PowerSeries K) (φ i)) → BndF (PowerSeries.X : PowerSeries K) fun g => ∑ i ∈ s, φ i g) ∧ (∀ φ : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ → BndF (PowerSeries.X : PowerSeries K) fun g => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ g)) ∧ ∀ (φ : G → FractionRing (PowerSeries K)), BndF (PowerSeries.X : PowerSeries K) φ → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ φ' : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ' ∧ ∀ g, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ' g) = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * φ g := by
  intro K G _ _ _ _
  have hconst : ∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c := by
    intro c
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (PowerSeries K)) c
    have hb : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    obtain ⟨v, hv⟩ := PowerSeries.isUnit_divided_by_X_pow_order hb
    obtain ⟨n, hbv⟩ : ∃ n : ℕ, (b : PowerSeries K) = PowerSeries.X ^ n * (v : PowerSeries K) :=
      ⟨(b : PowerSeries K).order.toNat, by rw [hv, PowerSeries.X_pow_order_mul_divXPowOrder]⟩
    have hb0 : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))).mpr hb
    unfold BndF
    refine ⟨n, fun _ => a * ↑v⁻¹, ac_const _, fun _ => ?_⟩
    dsimp only
    rw [IsFractionRing.mk'_eq_div, mul_div_assoc', eq_div_iff hb0,
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_pow (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))]
    congr 1
    rw [hbv, show a * ↑v⁻¹ * (PowerSeries.X ^ n * ↑v) = PowerSeries.X ^ n * a * (↑v⁻¹ * ↑v) by ring,
      Units.inv_mul, mul_one]
  have hops : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ →
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧
      BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹ := by
    intro φ ψ hφ hψ
    unfold BndF at hφ hψ ⊢
    obtain ⟨s1, φ1, hc1, he1⟩ := hφ
    obtain ⟨s2, ψ2, hc2, he2⟩ := hψ
    refine ⟨⟨s1 + s2, fun g => PowerSeries.X ^ s2 * φ1 g + PowerSeries.X ^ s1 * ψ2 g, ?_, fun g => ?_⟩,
      ⟨s1 + s2, fun g => φ1 g * ψ2 g, (adicCont_add_and_adicCont_mul hc1 hc2).2, fun g => ?_⟩,
      ⟨s1, fun g => -φ1 g, adicCont_neg_of_adicCont hc1, fun g => ?_⟩,
      ⟨s1, fun g => φ1 g⁻¹, adicCont_comp_inv_of_isTopologicalGroup hc1, fun g => he1 g⁻¹⟩⟩
    · exact (adicCont_add_and_adicCont_mul (adicCont_add_and_adicCont_mul (ac_const _) hc1).2 (adicCont_add_and_adicCont_mul (ac_const _) hc2).2).1
    · simp only [map_add, map_mul, map_pow, he1, he2]
      ring
    · simp only [map_mul, he1, he2]
      ring
    · simp only [map_neg, he1]
      ring
  refine ⟨hconst, hops, ?_, ?_, ?_⟩
  · intro ι s φ hφ
    classical
    revert hφ
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hconst 0
    · intro a t hat ih hall
      have h1 := hall a (Finset.mem_insert_self a t)
      have h2 := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert hat]
      exact (hops _ _ h1 h2).1
  · intro φ hφ
    unfold BndF
    exact ⟨0, φ, hφ, fun g => by simp⟩
  · intro φ hφ
    unfold BndF at hφ
    obtain ⟨s0, φ0, hc0, he0⟩ := hφ
    refine ⟨s0, fun s hs => ⟨fun g => PowerSeries.X ^ (s - s0) * φ0 g, (adicCont_add_and_adicCont_mul (ac_const _) hc0).2, fun g => ?_⟩⟩
    rw [map_mul, map_pow, he0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
