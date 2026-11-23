import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLineStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedAlongLineStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanOne

open GlobalTheory.Mass.FixedSub GlobalTheory.Mass.PrimMean

theorem orbMass_stabilizer_le (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (U : Submodule K V) (n N₀ : ℕ) (T : 𝓞 K) (hT : T ≠ 0)
    (dW : Module.finrank K (perp h U) = 1) :
    orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
      (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
      (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} ≤
    orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) *
      (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) *
      ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h5, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ γ.1 • dual h L := dual_smul h γ.1 L ▸ hx
      change T • x ∈ γ.1 • L
      rw [smul_def'] at hx' ⊢
      unfold gmap at hx' ⊢
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨T • y, h5 y hy, map_smul _ _ _⟩
    · rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, -, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    obtain ⟨b1, -, -⟩ := (memB M').1 h2
    have cnt := GlobalTheory.T.card_hermitianLattices_glued_along_line K V h hK hs hp U M M' T hT dW h1.1 b1
    have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
        {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = M ∧
          latIn (perp h U) L = M'} :=
      fun N hN => ⟨hN.1.1, hN.1.2.2.2.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
    have e : discN (hRes h U) M = n := h1.2
    rw [e] at cnt
    have := ENat.toENNReal_le.2 ((Set.encard_le_encard sub).trans cnt)
    rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → j + 1 = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ 1 → ∀ (de t : ℕ) (T : 𝓞 K), 1 ≤ de → 1 ≤ t → T ≠ 0 → Ideal.absNorm (Ideal.span {T}) = t ^ 2 → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ x ∈ dual h L, T • x ∈ L) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (de : ℝ) ^ j * ((de : ℝ) ^ (4 + Real.logb 2 (fDeg K)) * (t : ℝ) ^ 2 * ((de : ℝ) * t) ^ (2 + Real.logb 2 (fDeg K)))) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j hj hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    de t T hde ht hT hN 𝒢 hst h𝒢
  obtain ⟨S, hdim, hcov, hsum⟩ := GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le hM K V h hK hs hp hLand j hj V₁ h₁ I₁ hs₁ hI₁ de hde
  have hnd := pd_nondeg h hp
  set l : ℝ := Real.logb 2 (fDeg K) with hl
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢
    (fun L => primSp h L j (de ^ 2))
    (fun g L U => (GlobalTheory.T.primitive_sublattices_move_with_isometries K V h hK hs hnd g L U j (de ^ 2)).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  have d0 : (0 : ℝ) < de := by exact_mod_cast hde
  have t0 : (0 : ℝ) < t := by exact_mod_cast ht
  set C : ℝ := mass h₂ I₂ * ((de : ℝ) * t) ^ (2 + l) * ((t : ℝ) ^ 2 * (de : ℝ) ^ 2) with hC
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)} ≤
      orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) * ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, -, -, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
    have dW : Module.finrank K (perp h U) = 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
        discN (hRes h U) (latIn U L) = de ^ 2}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2.1, (h𝒢 L hL.1).2.2.2, hL.2.2⟩)
      (fun _ _ => le_rfl)
    refine a1.trans ((orbMass_stabilizer_le K V h hK hs hp U (de ^ 2) (t ^ 2) T hT dW).trans ?_)
    have a3 := GlobalTheory.T.totalMass_integralLattices_bounded_det_line hM K (perp h U) (hRes h (perp h U)) hK (hRes_symm h hs _) (hRes_pd h hp _) dW
      V₂ h₂ I₂ hs₂ hI₂ (de * t) (Nat.mul_pos hde ht)
    rw [mul_pow, Nat.cast_mul] at a3
    rw [mul_assoc, hC, ENNReal.ofReal_mul (by positivity), hN]
    refine mul_le_mul' le_rfl (mul_le_mul' a3 (le_of_eq ?_))
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  refine (mul_le_mul' hsum le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e : (de : ℝ) ^ (4 + l) = (de : ℝ) ^ (2 + l) * (de : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add d0]
    congr 1
    push_cast
    ring
  rw [e, hC]
  ring

end GlobalTheory.Mass.PrimMeanOne
