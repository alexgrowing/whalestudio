import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FewOrbitsSubspacesHermitianLatticeDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumRestrictSliceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLeStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMean

theorem orbSum_encard_le (G A B : Type) [Group G] [MulAction G A] [MulAction G B] (Y : Set A) (P : A → Set B)
    (hP : ∀ (g : G) a b, g • b ∈ P (g • a) ↔ b ∈ P a) (hY : Stable G Y)
    (hfin : ∀ y ∈ Y, Finite (MulAction.stabilizer G y)) (s : Finset B)
    (hs : ∀ a ∈ Y, ∀ b ∈ P a, ∃ b₀ ∈ s, ∃ g : G, g • b₀ = b) :
    orbSum G Y (fun a => (((P a).encard : ℕ∞) : ℝ≥0∞)) ≤
      ∑ b₀ ∈ s, orbMass (MulAction.stabilizer G b₀) {a | a ∈ Y ∧ b₀ ∈ P a} := by
  set X : Set (A × B) := {p | p.1 ∈ Y ∧ p.2 ∈ P p.1} with hX
  have hXs : Stable G X := fun g p hp => ⟨hY g _ hp.1, (hP g _ _).2 hp.2⟩
  have h1 := GlobalTheory.Mass.orbMass_eq_orbSum_fibre G (A × B) A X Y Prod.fst (fun _ _ => rfl) hXs hY
    (fun p hp => hp.1) hfin
  have h2 : orbSum G Y (fun a => (((P a).encard : ℕ∞) : ℝ≥0∞)) ≤ orbMass G X := by
    rw [h1]
    refine (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive G A).1 Y Y _ _ subset_rfl fun a ha => ?_
    have : (P a).encard ≤ (X ∩ Prod.fst ⁻¹' {a}).encard :=
      Set.encard_le_encard_of_injOn (f := fun b => (a, b)) (fun b hb => ⟨⟨ha, hb⟩, rfl⟩)
        (fun b _ b' _ e => (Prod.ext_iff.1 e).2)
    exact_mod_cast this
  refine h2.trans ?_
  have h3 := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive G (A × B)).2.2.1 B s X (fun b₀ => {p | p ∈ X ∧ ∃ g : G, g • b₀ = p.2})
    (fun _ => 1) (by
      intro p hp
      obtain ⟨b₀, hb₀, g, hg⟩ := hs _ hp.1 _ hp.2
      simp only [Set.mem_iUnion]
      exact ⟨b₀, hb₀, hp, g, hg⟩)
  refine h3.trans (Finset.sum_le_sum fun b₀ _ => le_of_eq ?_)
  have hS : Stable (MulAction.stabilizer G b₀) {p : A × B | p ∈ X ∧ p.2 = b₀} := by
    rintro g p ⟨hp, e⟩
    refine ⟨hXs g p hp, ?_⟩
    change (g : G) • p.2 = b₀
    rw [e]
    exact g.2
  have h4 := GlobalTheory.T.orbitWeightedStabilizerSum_restrict_slice G (A × B) (MulAction.stabilizer G b₀)
    {p | p ∈ X ∧ ∃ g : G, g • b₀ = p.2} {p | p ∈ X ∧ p.2 = b₀} (fun _ => 1)
    (fun p hp => ⟨hp.1, 1, by rw [one_smul, hp.2]⟩)
    (by
      rintro g p ⟨hp, g', e⟩
      refine ⟨hXs g p hp, g * g', ?_⟩
      rw [mul_smul, e]
      rfl)
    hS (fun _ _ => rfl)
    (by
      rintro p ⟨hp, g, e⟩
      refine ⟨g⁻¹, hXs _ p hp, ?_⟩
      change g⁻¹ • p.2 = b₀
      rw [← e, inv_smul_smul])
    (by
      rintro g p ⟨_, e⟩ ⟨_, e'⟩
      change g • p.2 = b₀ at e'
      rw [e] at e'
      exact e')
  rw [← h4]
  exact GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant (MulAction.stabilizer G b₀) (MulAction.stabilizer G b₀) (A × B) A (MulEquiv.refl _)
    Prod.fst {p | p ∈ X ∧ p.2 = b₀} {a | a ∈ Y ∧ b₀ ∈ P a} (fun _ => 1) hS
    (by
      rintro g a ⟨ha, hb⟩
      refine ⟨hY g a ha, ?_⟩
      have := (hP g a b₀).2 hb
      rw [g.2] at this
      exact this)
    ⟨fun p hp => ⟨hp.1.1, hp.2 ▸ hp.1.2⟩,
      fun p hp q hq e => Prod.ext e (hp.2.trans hq.2.symm),
      fun a ha => ⟨(a, b₀), ⟨ha, rfl⟩, rfl⟩⟩
    (fun _ _ _ => rfl) (fun _ _ => rfl)

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · positivity
  · exact le_rfl

theorem isIntLat_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L)
    (U : Submodule K V) : IsIntLat (hRes h U) (latIn U L) := by
  refine ⟨⟨?_, ?_⟩, fun x hx y hy => hL.2 x hx y hy⟩
  · apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype
    exact hL.1.fg.of_le (Submodule.map_comap_le _ _)
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : V) ∈ Submodule.span K (L : Set V) := by rw [hL.1.span_eq_top]; trivial
    obtain ⟨a, hax⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx
    rw [Submodule.span_eq] at hax
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero a
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax

end

theorem exponents (n X j s l c : ℝ) (m : ℕ) (hm : (m : ℝ) = s) (hn : 1 ≤ n) (hX : n ≤ X) (hl : 0 ≤ l)
    (hc : c ≤ n ^ (1 + l)) :
    c * (n ^ ((j + l) / 2) * (X * X ^ ((s + l) / 2)) * (n * X) ^ (2 * m + 1)) ≤
      n ^ (j / 2) * X ^ ((9 * s + 8 + 4 * l) / 2) := by
  have n0 : 0 < n := by linarith
  have X0 : 0 < X := by linarith
  have e1 : n ^ ((j + l) / 2) = n ^ (j / 2) * n ^ (l / 2) := by
    rw [← Real.rpow_add n0]; congr 1; ring
  have b1 : c ≤ X ^ (1 + l) := hc.trans (Real.rpow_le_rpow n0.le hX (by linarith))
  have b2 : n ^ (l / 2) ≤ X ^ (l / 2) := Real.rpow_le_rpow n0.le hX (by linarith)
  have b3 : (n * X) ^ (2 * m + 1) ≤ X ^ (4 * s + 2) := by
    have : (n * X) ^ (2 * m + 1) ≤ (X * X) ^ (2 * m + 1) := by gcongr
    refine this.trans (le_of_eq ?_)
    rw [← hm, ← sq, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e2 : X ^ ((9 * s + 8 + 4 * l) / 2) =
      X ^ (1 + l) * (X ^ (l / 2) * (X * X ^ ((s + l) / 2)) * X ^ (4 * s + 2)) := by
    have : X * X ^ ((s + l) / 2) = X ^ (1 + (s + l) / 2) := by rw [Real.rpow_add X0, Real.rpow_one]
    rw [this, ← Real.rpow_add X0, ← Real.rpow_add X0, ← Real.rpow_add X0]
    congr 1
    ring
  rw [e1, e2]
  calc c * (n ^ (j / 2) * n ^ (l / 2) * (X * X ^ ((s + l) / 2)) * (n * X) ^ (2 * m + 1))
      ≤ X ^ (1 + l) * (n ^ (j / 2) * X ^ (l / 2) * (X * X ^ ((s + l) / 2)) * X ^ (4 * s + 2)) := by
        gcongr
    _ = _ := by ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j s : ℕ), 1 ≤ j → 1 ≤ s → j + s = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ s → ∀ (n N₀ : ℕ), 1 ≤ n → 1 ≤ N₀ → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (n : ℝ) ^ ((j : ℝ) / 2) * ((n : ℝ) * N₀) ^ ((9 * (s : ℝ) + 8 + 4 * Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j s hj hs1 hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    n N₀ hn hN 𝒢 hst h𝒢
  obtain ⟨S, hcard, hdim, hcov⟩ := GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant K V h hK hs hp hLand j n hn
  have hnd : h.Nondegenerate := by
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · by_contra hne
      have := hp τ x hne
      simp [hx x] at this
    · by_contra hne
      have := hp τ x hne
      simp [hx x] at this
  set l : ℝ := Real.logb 2 (Module.finrank ℚ K) with hl
  have l0 : 0 ≤ l := Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos)
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢 (fun L => primSp h L j n)
    (fun g L U => (GlobalTheory.T.primitive_sublattices_move_with_isometries K V h hK hs hnd g L U j n).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  set X : ℝ := (n : ℝ) * N₀ with hX
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have N1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN
  have hnX : (n : ℝ) ≤ X := le_mul_of_one_le_right (by positivity) N1
  have X0 : 0 ≤ X := by positivity
  set C : ℝ := (mass h₁ I₁ * (n : ℝ) ^ (((j : ℝ) + l) / 2)) * (X * (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) *
    ((n : ℝ) * X) ^ (2 * s + 1) with hC
  have C0 : 0 ≤ C := by positivity
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j n} ≤
      ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, sU, pU, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
    obtain ⟨-, sW, pW, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 (perp h U)
    have dW : Module.finrank K (perp h U) = s := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j n}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2, hL.2.2⟩) (fun _ _ => le_rfl)
    refine a1.trans ((GlobalTheory.T.orbitStabilizerMass_subspace_cyclicDiscriminant_le K V h hK hs hp U n N₀).trans ?_)
    have a2 := GlobalTheory.T.mass_integralLattices_discriminantOrder_le hM K U (hRes h U) hK sU pU (dU ▸ hj) V₁ h₁ hs₁ I₁ (dU ▸ hI₁) n hn
    rw [dU] at a2
    have a3 : ∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') ≤
        ENNReal.ofReal (X * (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) := by
      refine (Finset.sum_le_card_nsmul _ _
        (ENNReal.ofReal (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) fun n' hn' => ?_).trans (le_of_eq ?_)
      · obtain ⟨b1, b2⟩ := Finset.mem_Icc.1 hn'
        have a := GlobalTheory.T.mass_integralLattices_discriminantOrder_le hM K (perp h U) (hRes h (perp h U)) hK sW pW (dW ▸ hs1) V₂ h₂ hs₂ I₂
          (dW ▸ hI₂) n' b1
        rw [dW] at a
        refine a.trans (ENNReal.ofReal_le_ofReal ?_)
        have b3 : (n' : ℝ) ≤ X := by rw [hX]; exact_mod_cast b2
        gcongr
      · rw [ENNReal.ofReal_mul X0, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, hX,
          ← Nat.cast_mul, ENNReal.ofReal_natCast]
    rw [hC, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), dW]
    refine mul_le_mul' (mul_le_mul' a2 a3) (le_of_eq ?_)
    rw [← ENNReal.ofReal_natCast, hX]
    push_cast
    rfl
  refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have key := exponents n X j s l S.card s rfl n1 hnX l0 hcard
  have := mul_le_mul_of_nonneg_left key (mul_nonneg m1 m2)
  calc (S.card : ℝ) * C = mass h₁ I₁ * mass h₂ I₂ * ((S.card : ℝ) * ((n : ℝ) ^ (((j : ℝ) + l) / 2) *
        (X * X ^ (((s : ℝ) + l) / 2)) * ((n : ℝ) * X) ^ (2 * s + 1))) := by rw [hC]; ring
    _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.Mass.PrimMean
