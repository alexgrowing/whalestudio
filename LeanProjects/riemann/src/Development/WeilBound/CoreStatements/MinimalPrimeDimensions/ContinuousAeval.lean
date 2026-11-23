import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros

open MvPolynomial Filter Topology NumberField

namespace ChowFormHeightComparison₂.GenericDenseBound

theorem ratPrimeDense : GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
    GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof

theorem continuous_aeval {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Continuous fun z : Fin n → ℂ => aeval z f := by
  have : (fun z : Fin n → ℂ => aeval z f) = fun z => eval z (map (algebraMap ℚ ℂ) f) := by
    funext z
    rw [eval_map, aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

theorem generic_dense {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℚ)) (hP : P.IsPrime) {z₀ : Fin n → ℂ}
    (hz₀ : ∀ g ∈ P, aeval z₀ g = 0) :
    ∃ z : ℕ → Fin n → ℂ, (∀ m g, aeval (z m) g = 0 ↔ g ∈ P) ∧ Tendsto z atTop (𝓝 z₀) := by
  let V : Set (Fin n → ℂ) := {z | ∀ g ∈ P, aeval z g = 0}
  have hV : IsClosed V := by
    have : V = ⋂ g ∈ P, {z | aeval z g = 0} := by ext z; simp [V]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (continuous_aeval g) continuous_const
  haveI : CompleteSpace V := hV.completeSpace_coe
  haveI : Countable (MvPolynomial (Fin n) ℚ) := (basisMonomials (Fin n) ℚ).repr.injective.countable
  let O : {f : MvPolynomial (Fin n) ℚ // f ∉ P} → Set V := fun f => {z | aeval z.1 f.1 ≠ 0}
  have hO : ∀ f, IsOpen (O f) := fun f =>
    isOpen_ne_fun ((continuous_aeval f.1).comp continuous_subtype_val) continuous_const
  have hD : ∀ f, Dense (O f) := fun f => by
    rw [Subtype.dense_iff]
    refine (ratPrimeDense (Fin n) P f.1 hP f.2).trans (closure_mono ?_)
    rintro z ⟨h1, h2⟩
    exact ⟨⟨z, h1⟩, h2, rfl⟩
  obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.1 (dense_iInter_of_isOpen hO hD ⟨z₀, hz₀⟩)
  refine ⟨fun m => (u m).1, fun m g => ⟨fun h => ?_, fun h => (u m).2 g h⟩,
    (continuous_subtype_val.tendsto _).comp hl⟩
  by_contra hg
  exact Set.mem_iInter.1 (hu m) ⟨g, hg⟩ h

theorem exists_int_mul {n : ℕ} (g : MvPolynomial (Fin n) ℚ) :
    ∃ (N : ℕ) (g' : MvPolynomial (Fin n) ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) g' = (N : MvPolynomial (Fin n) ℚ) * g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, a.den_ne_zero, ?_⟩
    rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Fin n) ℚ), ← map_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨N, p', hN, hp⟩ := hp
    obtain ⟨M, q', hM, hq⟩ := hq
    refine ⟨N * M, M * p' + N * q', mul_ne_zero hN hM, ?_⟩
    rw [map_add, map_mul, map_mul, hp, hq, map_natCast, map_natCast]
    push_cast
    ring
  | mul_X p i hp =>
    obtain ⟨N, p', hN, hp⟩ := hp
    refine ⟨N, p' * X i, hN, ?_⟩
    rw [map_mul, hp, map_X, mul_assoc]

theorem aeval_map_int {n : ℕ} {A : Type} [CommRing A] [Algebra ℚ A] (z : Fin n → A) (g : MvPolynomial (Fin n) ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, map_X, aeval_X]

theorem hom_aeval {n : ℕ} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : Fin n → A)
    (g : MvPolynomial (Fin n) ℤ) : φ (aeval z g) = aeval (fun i => φ (z i)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X]

theorem exists_seq_emb {B Ω : Type} [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B] [Field Ω] [CharZero Ω]
    [Algebra B Ω] [IsFractionRing B Ω] (x : B →+* ℂ) :
    ∃ ρ : ℕ → Ω →+* ℂ, ∀ b : B, Tendsto (fun m => ρ m (algebraMap B Ω b)) atTop (𝓝 (x b)) := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ B)
  let a : Fin n → B := fun i => π (X i)
  have hπa : ∀ g, π g = aeval a g := fun g => by
    have : π = aeval a := MvPolynomial.algHom_ext fun i => by simp [a]
    rw [this]
  let φ : MvPolynomial (Fin n) ℚ →ₐ[ℚ] Ω := aeval fun i => algebraMap B Ω (a i)
  let P : Ideal (MvPolynomial (Fin n) ℚ) := RingHom.ker φ
  have hP : P.IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ g : MvPolynomial (Fin n) ℤ, map (Int.castRingHom ℚ) g ∈ P ↔ π g = 0 := fun g => by
    rw [RingHom.mem_ker]
    show aeval _ _ = 0 ↔ _
    rw [aeval_map_int, ← hom_aeval (algebraMap B Ω) a g, ← hπa]
    exact map_eq_zero_iff _ (IsFractionRing.injective B Ω)
  have hz₀ : ∀ g ∈ P, aeval (fun i => x (a i)) g = 0 := fun g hg => by
    obtain ⟨N, g', hN, e⟩ := exists_int_mul g
    have h1 : π g' = 0 := (hmem g').1 (e ▸ P.mul_mem_left _ hg)
    have h2 : aeval (fun i => x (a i)) (map (Int.castRingHom ℚ) g') = 0 := by
      rw [aeval_map_int, ← hom_aeval x a g', ← hπa, h1, map_zero]
    rw [e, map_mul, map_natCast] at h2
    exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hN)
  obtain ⟨z, hz, hl⟩ := generic_dense P hP hz₀
  have hker : ∀ m g, aeval (z m) g = 0 ↔ π g = 0 := fun m g => by
    rw [← hmem, ← hz m, aeval_map_int]
  have hex : ∀ m, ∃ r : B →+* ℂ, ∀ g, r (π g) = aeval (z m) g := fun m =>
    ⟨RingHom.liftOfSurjective (π : MvPolynomial (Fin n) ℤ →+* B) hπ
      ⟨(aeval (z m) : MvPolynomial (Fin n) ℤ →ₐ[ℤ] ℂ), fun g hg => (hker m g).2 hg⟩,
      fun g => RingHom.liftOfSurjective_comp_apply _ _ _ g⟩
  choose r hr using hex
  have hinj : ∀ m, Function.Injective (r m) := fun m => by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨g, rfl⟩ := hπ b
    exact (hker m g).1 ((hr m g).symm.trans hb)
  refine ⟨fun m => IsFractionRing.lift (hinj m), fun b => ?_⟩
  obtain ⟨g, rfl⟩ := hπ b
  have h1 := ((continuous_aeval (map (Int.castRingHom ℚ) g)).tendsto _).comp hl
  simp only [IsFractionRing.lift_algebraMap, hr]
  rw [hπa, hom_aeval x a g, ← aeval_map_int]
  refine h1.congr fun m => ?_
  exact aeval_map_int _ _

theorem bound_of_emb {K B Ω : Type} [Field K] [NumberField K] [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    [Field Ω] [Algebra B Ω] [IsFractionRing B Ω] (ι : K →+* Ω) (a₀ : 𝓞 K →+* B)
    (ha : ∀ c : 𝓞 K, algebraMap B Ω (a₀ c) = ι (c : K)) (x : B →+* ℂ) {J : Type} (r : J → B)
    (F G : (K →+* ℂ) → (J → ℂ) → ℝ) (hF : ∀ σ, Continuous (F σ)) (hG : ∀ σ, Continuous (G σ))
    (h : ∀ ρ : Ω →+* ℂ, F (ρ.comp ι) (fun j => ρ (algebraMap B Ω (r j))) ≤ G (ρ.comp ι) (fun j => ρ (algebraMap B Ω (r j)))) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = x.comp a₀ ∧ F σ (fun j => x (r j)) ≤ G σ (fun j => x (r j)) := by
  have : CharZero Ω := charZero_of_injective_ringHom ι.injective
  obtain ⟨ρ, hρ⟩ := exists_seq_emb (Ω := Ω) x
  obtain ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, ∃ᶠ m in atTop, (ρ m).comp ι = σ :=
    frequently_exists.1 (Frequently.of_forall fun m => ⟨_, rfl⟩)
  have ht : Tendsto (fun m j => ρ m (algebraMap B Ω (r j))) atTop (𝓝 fun j => x (r j)) :=
    tendsto_pi_nhds.2 fun j => hρ _
  refine ⟨σ, RingHom.ext fun c => ?_, ?_⟩
  · refine tendsto_nhds_unique_of_frequently_eq (tendsto_const_nhds (x := σ (c : K))) (hρ (a₀ c))
      (hσ.mono fun m hm => ?_)
    rw [ha, ← hm]
    rfl
  · refine le_of_tendsto_of_tendsto_of_frequently (((hF σ).tendsto _).comp ht) (((hG σ).tendsto _).comp ht)
      (hσ.mono fun m hm => ?_)
    have := h (ρ m)
    rwa [hm] at this

end ChowFormHeightComparison₂.GenericDenseBound
