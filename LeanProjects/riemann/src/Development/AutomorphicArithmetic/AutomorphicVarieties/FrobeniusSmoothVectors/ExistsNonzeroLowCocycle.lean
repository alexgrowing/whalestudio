import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsMemStrSNeZeroOfFrameOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsLocallyConstantTwistedCocycleNeZeroOfFrameOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LowerTriangularConjAntidiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OneAddMaximalIdealSubsetUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothHomWeightSumNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothCharacterExtendsToOpenSubgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothDualExact

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_nonzero_low_cocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ u : F.G0 → k, IsLocallyConstant u → (∀ g h : F.G0, u (g * h) = (F.Ψ h : k) * u g + u h) → (∀ g : F.G0, u (F.star g) = (((F.Ψ g)⁻¹ : kˣ) : k) * u g) → (∀ v, ∃ α : k, ∀ s, u (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) * α) → u ≠ 0 → ∃ y a : F.G0 → k, F.Low k y a ∧ y ≠ 0 := by
  intro l _ k _ _ F C₀ hF u u1 u2 u3 u4 u5
  have h2 : (2 : k) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : k) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff k l] at e'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 e')
  obtain ⟨-, -, s3, -, -⟩ := UpperTheory.V.Fr.star hF
  let P : F.G0 → k := fun g => F.Ψ g
  have P0 : ∀ g, P g ≠ 0 := fun g => Units.ne_zero _
  have Pm : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [P]
  have Ps : ∀ g, P (F.star g) = (P g)⁻¹ := fun g => by simp only [P, s3, Units.val_inv_eq_inv_val]
  have Pl : IsLocallyConstant P := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h : F.G0 => (g : F.Γ)⁻¹ * h) ⁻¹' F.Ψ.ker,
      hF.Ψ_open.preimage (by fun_prop), by simp, fun h hh => ?_⟩
    have : F.Ψ ((g : F.Γ)⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simp only [P, this]
  have u2' : ∀ g h, u (g * h) = P h * u g + u h := u2
  have u3' : ∀ g, u (F.star g) = (P g)⁻¹ * u g := fun g => by rw [u3, Units.val_inv_eq_inv_val]
  have hg : P F.g0 ^ 2 - 1 ≠ 0 := fun e => hF.baseSubgroup_spec (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.1 e))
  obtain ⟨δ, hδ⟩ : ∃ δ : k, δ * (P F.g0 ^ 2 - 1) = -(u F.g0 * (P F.g0 - 1)) := ⟨_, div_mul_cancel₀ _ hg⟩
  refine ⟨fun g => u g + δ * (P g - 1),
    fun g => δ ^ 2 - δ ^ 2 * (P g + (P g)⁻¹) / 2 - δ * (u g + (P g)⁻¹ * u g) + (P g)⁻¹ * u g ^ 2 / 2,
    ⟨?_, ?_, fun g h => ?_, fun g h => ?_, fun g => ?_, ?_, fun v => ?_⟩, fun e => u5 ?_⟩
  · exact (u1.prodMk Pl).comp fun z => z.1 + δ * (z.2 - 1)
  · exact (u1.prodMk Pl).comp fun z =>
      δ ^ 2 - δ ^ 2 * (z.2 + z.2⁻¹) / 2 - δ * (z.1 + z.2⁻¹ * z.1) + z.2⁻¹ * z.1 ^ 2 / 2
  · show _ = P h * _ + _
    rw [u2', Pm]; ring
  · rw [Units.val_inv_eq_inv_val]
    show _ = P h * _ + _ + (P g)⁻¹ * _
    have := P0 g
    have := P0 h
    simp only [u2', Pm, u3', Ps]
    field_simp
    ring
  · have := P0 g
    simp only [u3', Ps]
    field_simp
    ring
  · have := P0 F.g0
    simp only [u3', Ps]
    field_simp
    linear_combination hδ
  · obtain ⟨α, hα⟩ := u4 v
    refine ⟨δ + α, α - δ, α ^ 2 / 2 - δ * α - δ ^ 2 / 2, fun s => ?_⟩
    have h1 : u (F.loc0 v s) = (P (F.loc0 v s) - 1) * α := hα s
    have := P0 (F.loc0 v s)
    rw [Units.val_inv_eq_inv_val]
    show _ = (P (F.loc0 v s) - 1) * _ ∧ _ = (1 - (P (F.loc0 v s))⁻¹) * _ ∧
      _ = (P (F.loc0 v s) - (P (F.loc0 v s))⁻¹) * _ - (1 - (P (F.loc0 v s))⁻¹) * _
    simp only [u3', Ps, h1]
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
  · have e1 : ∀ g, u g + δ * (P g - 1) = 0 := congrFun e
    have e2 := e1 (F.star F.g0)
    have e3 := e1 F.g0
    have := P0 F.g0
    rw [u3', Ps] at e2
    field_simp at e2
    have e4 : 2 * δ * (P F.g0 ^ 2 - 1) = 0 := by linear_combination (P F.g0 + 1) * e3 - (P F.g0 + 1) * e2
    have e5 : δ = 0 := by simpa [h2, hg] using e4
    funext g
    simpa [e5] using e1 g

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3)
include hF

private theorem at_ex (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] {y a : F.G0 → Q}
    (h : F.Low Q y a) : ∃ ξ : S.A →+* Q, S.At ξ y a := by
  obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := UpperTheory.lowerTriangular_conj_antidiag hF Q y a h
  obtain ⟨ξ, h6, rfl⟩ := UpperTheory.smoothHom_weight_sum_neg hF (Or.inr rfl) S Q ρ h1 h2 h3
  refine ⟨ξ, h6, Ideal.span_le.2 ?_, h4, h5⟩
  rintro _ ⟨g, i, j, hij, rfl⟩
  have : (S.u.map ξ).r g i j ∈ (S.u.map ξ).triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
  rwa [h2, Ideal.mem_bot] at this

private theorem at_uniq {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {y a : F.G0 → Q} {ξ ξ' : S.A →+* Q}
    (h : S.At ξ y a) (h' : S.At ξ' y a) : ξ' = ξ := by
  obtain ⟨h1, -, h2⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S Q ξ h.fpt
  obtain ⟨h1', -, -⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S Q ξ' h'.fpt
  refine h2 ξ' h'.fpt fun g i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hm : S.u.r g i j ∈ S.u.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    exact (h'.low hm).trans (h.low hm).symm
  · exact (h1'.1 g i).trans (h1.1 g i).symm
  have hc : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h.hy, h'.hy]
  · have h5 : S.u.r (F.star g) 1 0 = S.u.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 S.u g 1 0
    rw [← h5, h.hy, h'.hy]
  · rw [h.ha, h'.ha]

private theorem at_res (p : PrimeSpectrum S.A) (hp : p ∈ S.BB) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (ResidueField O) K) (ξ : S.A →+* K) (y a : F.G0 → K),
      RingHom.ker ξ = p.asIdeal ∧ S.At ξ y a ∧ F.Low K y a := by
  obtain ⟨K, _, _, ξ, h1, h2, h3⟩ := UpperTheory.smoothDual_exact hF (Or.inr rfl) S p hp
  obtain ⟨h4, h5, -⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S K ξ h2
  refine ⟨K, inferInstance, inferInstance, ξ, _, _, h1, ⟨h2, h3, fun _ => rfl, fun _ => rfl⟩,
    UpperTheory.one_add_maximalIdeal_subset_units hF K (S.u.map ξ) h4 (Ideal.span_eq_bot.2 ?_) h5⟩
  rintro _ ⟨g, i, j, hij, rfl⟩
  exact h3 (Ideal.subset_span ⟨g, i, j, hij, rfl⟩)

private theorem line {K : Type} [Field K] [Algebra (ResidueField O) K] {Y A : F.G0 → Polynomial K}
    (h : F.Low (Polynomial K) Y A) :
    ∃ η : PrimeSpectrum S.A, S.mB ≤ S.π η.asIdeal ∧ (S.u.ee ≤ η.asIdeal → Y = 0) ∧
      ∀ (c : K) (ξ : S.A →+* K) (y a : F.G0 → K), S.At ξ y a → (∀ g, (Y g).eval c = y g) →
        (∀ g, (A g).eval c = a g) → η.asIdeal ≤ RingHom.ker ξ := by
  obtain ⟨ζ, hζ⟩ := at_ex hF S _ h
  refine ⟨⟨RingHom.ker ζ, RingHom.ker_isPrime ζ⟩, Ideal.map_le_iff_le_comap.1 hζ.fpt.x0, fun he => ?_,
    fun c ξ y a hξ hy ha x hx => ?_⟩
  · funext g
    rw [← hζ.hy]
    exact he (Ideal.subset_span ⟨g, 1, 0, by decide, rfl⟩)
  · let φ : Polynomial K →ₐ[ResidueField O] K := (Polynomial.aeval c : Polynomial K →ₐ[K] K).restrictScalars _
    have h1 := hζ.comp φ
    have e1 : (fun g => φ (Y g)) = y := funext fun g => by simpa [φ] using hy g
    have e2 : (fun g => φ (A g)) = a := funext fun g => by simpa [φ] using ha g
    rw [e1, e2] at h1
    rw [← at_uniq hF S hξ h1]
    have : ζ x = 0 := hx
    show φ (ζ x) = 0
    rw [this, map_zero]

end

theorem UpperTheory.V.Fr.preconnected_rank_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, S.BB.Nonempty ∧ IsPreconnected S.BB ∧ S.BB ⊆ closure (S.BB \ {p | S.u.ee ≤ p.asIdeal}) := by
  intro l _ O _ _ _ _ F C₀ hF S
  obtain ⟨b, hb, hb0⟩ := UpperTheory.exists_mem_strS_ne_zero_of_frameOk hF
  obtain ⟨u, u1, u2, u3, u4, u5⟩ := UpperTheory.exists_locallyConstant_twistedCocycle_ne_zero_of_frameOk hF
  obtain ⟨y₀, a₀, h₀, hy₀⟩ := exists_nonzero_low_cocycle hF u u1 u2 u3 u4 u5
  have hl : F.Low (ResidueField O) 0 b := by
    have := (Frame.Low.zero (F := F)).comb 0 hb
    simp only [Pi.zero_apply, mul_zero, zero_add] at this
    exact this
  obtain ⟨ξ₀, hξ₀⟩ := at_ex hF S _ hl
  let p₀ : PrimeSpectrum S.A := ⟨RingHom.ker ξ₀, RingHom.ker_isPrime ξ₀⟩
  have hp₀ : p₀ ∈ S.BB := ⟨Ideal.map_le_iff_le_comap.1 hξ₀.fpt.x0, fun h => hb0 (funext fun g => by
    rw [← hξ₀.ha]
    exact h (Ideal.subset_span ⟨g, 2, 0, by decide, rfl⟩))⟩
  refine ⟨⟨p₀, hp₀⟩, isPreconnected_of_forall p₀ fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨K, _, _, ξ, y, a, h1, h2, h3⟩ := at_res hF S p hp
    let c : K →ₐ[ResidueField O] Polynomial K := IsScalarTower.toAlgHom _ _ _
    let i : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
    obtain ⟨η, e1, -, e2⟩ := line hF S ((h3.map c).comb Polynomial.X
      (Frame.strS_mul (1 - Polynomial.X) (Frame.strS_map (c.comp i).toLinearMap hb)))
    have l1 : η ≤ p := by
      have := e2 1 ξ y a h2 (fun g => by simp [c]) (fun g => by simp [c])
      rwa [h1] at this
    have l0 : η ≤ p₀ := fun x hx => by
      have := e2 0 _ _ _ (hξ₀.comp i) (fun g => by simp [c]) (fun g => by simp [c, i]) hx
      exact (map_eq_zero i).1 this
    have hη : η ∈ S.BB := ⟨e1, fun h => hp.2 (h.trans l1)⟩
    refine ⟨{η, p, p₀}, ?_, by simp, by simp, isPreconnected_singleton.subset_closure (s := {η}) (by simp) ?_⟩
    · rintro q (rfl | rfl | rfl) <;> assumption
    · rintro q (rfl | rfl | rfl)
      · exact subset_closure rfl
      · exact (PrimeSpectrum.le_iff_mem_closure _ _).1 l1
      · exact (PrimeSpectrum.le_iff_mem_closure _ _).1 l0
  · by_cases he : S.u.ee ≤ p.asIdeal
    swap
    · exact subset_closure ⟨hp, he⟩
    obtain ⟨K, _, _, ξ, y, a, h1, h2, h3⟩ := at_res hF S p hp
    obtain rfl : y = 0 := funext fun g => by
      rw [← h2.hy]
      exact (h1 ▸ he) (Ideal.subset_span ⟨g, 1, 0, by decide, rfl⟩)
    let c : K →ₐ[ResidueField O] Polynomial K := IsScalarTower.toAlgHom _ _ _
    let i : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
    obtain ⟨η, e1, e3, e2⟩ := line hF S ((h₀.map (c.comp i)).comb Polynomial.X (Frame.strS_map c.toLinearMap h3.strS))
    have l1 : η ≤ p := by
      have := e2 0 ξ 0 a h2 (fun g => by simp [c]) (fun g => by simp [c])
      rwa [h1] at this
    have hη : η ∈ S.BB \ {p | S.u.ee ≤ p.asIdeal} := ⟨⟨e1, fun h => hp.2 (h.trans l1)⟩, fun h => hy₀ (funext fun g => by
      have := congrFun (e3 h) g
      simpa [c, i] using this)⟩
    exact closure_mono (Set.singleton_subset_iff.2 hη) ((PrimeSpectrum.le_iff_mem_closure _ _).1 l1)
