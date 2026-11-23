import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem ringKrullDim_eq_one' [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 := by
  have := hf
  have : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have : Ring.DimensionLEOne k := Ring.DimensionLEOne.of_isIntegral (R := ℤ) k
  apply eq_of_le_of_not_lt
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · intro h'
    have h'' : ringKrullDim k ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    have hk : IsField k := Ring.KrullDimLE.isField_of_isDomain
    exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := k) Int.cast_injective hk)

theorem topologicalKrullDim_of_polyCovered' [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨ξ, -, hcov⟩ := h
  have hdim : ∀ (σ : Type) [Fintype σ], Fintype.card σ = d →
      topologicalKrullDim (Sp (MvPolynomial σ k)) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro σ _ hσ
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial σ k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, hk, Nat.card_eq_fintype_card, hσ, add_comm]
    norm_cast
  apply le_antisymm
  · unfold topologicalKrullDim
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    obtain ⟨σ, _, e, he, hσ, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    let Φ := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding e e.isOpenEmbedding
    have hZ : TopologicalSpace.IrreducibleCloseds.map e e.isOpenEmbedding.continuous
        (Φ.symm ⟨Z, ⟨y, hx⟩⟩) = Z :=
      congrArg Subtype.val (Φ.apply_symm_apply ⟨Z, ⟨y, hx⟩⟩)
    rw [← hZ, e.isOpenEmbedding.coheight_map]
    have h1 := Order.coheight_le_krullDim (Φ.symm ⟨Z, ⟨y, hx⟩⟩)
    have h2 := hdim σ hσ
    unfold topologicalKrullDim at h2
    rw [h2] at h1
    exact h1
  · obtain ⟨σ, _, e, he, hσ, -, -, -⟩ := hcov ξ
    haveI := he
    rw [← hdim σ hσ]
    exact e.isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem isIntegral_of_polyCovered' [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X := by
  obtain ⟨ξ, -, hcov⟩ := h
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨σ, _, e, he, -, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    exact isReduced_of_injective (e.stalkMap y).hom
      (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hirr : ∀ x : X, ∃ R : Set X, IsOpen R ∧ IsIrreducible R ∧ x ∈ R ∧ ξ ∈ R := by
    intro x
    obtain ⟨σ, _, e, he, -, -, hx, hξ⟩ := hcov x
    haveI := he
    refine ⟨Set.range e, e.isOpenEmbedding.isOpen_range, ?_, hx, hξ⟩
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (Sp (MvPolynomial σ k))).image _
      e.continuous.continuousOn
  haveI : IrreducibleSpace X := by
    refine (irreducibleSpace_def X).mpr ⟨⟨ξ, trivial⟩, ?_⟩
    rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
    obtain ⟨Ra, hRa, iRa, haRa, hξa⟩ := hirr a
    obtain ⟨Rb, hRb, iRb, hbRb, hξb⟩ := hirr b
    obtain ⟨p, hpa, hpu, hpb⟩ := iRa.2 u Rb hu hRb ⟨a, haRa, ha⟩ ⟨ξ, hξa, hξb⟩
    obtain ⟨q, -, ⟨hqu, -⟩, hqv⟩ :=
      iRb.2 (u ∩ Ra) v (hu.inter hRa) hv ⟨p, hpb, hpu, hpa⟩ ⟨b, hbRb, hb⟩
    exact ⟨q, trivial, hqu, hqv⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem polyCovered_pSpace' [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N := by
  classical
  letI : GradedAlgebra (ProjSpace.grading k N) := MvPolynomial.gradedAlgebra
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ≠ 0 :=
    fun i => MvPolynomial.X_ne_zero i
  let ξ0 : PSpace k N := (⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.bot_prime, fun hle => hX 0 (by
      have h0 : MvPolynomial.X 0 ∈ HomogeneousIdeal.irrelevant (ProjSpace.grading k N) := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem k N 0) one_ne_zero
      have h1 := hle h0
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h1
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h1)⟩ :
    ProjectiveSpectrum (ProjSpace.grading k N))
  have hmem : ∀ i, ξ0 ∈ ProjSpace.chart k N i := fun i =>
    (Proj.mem_basicOpen _ _ _).mpr fun h => hX i (by
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h)
  have hspec : ∀ z : PSpace k N, ξ0 ⤳ z := fun z =>
    specializes_iff_mem_closure.mpr
      ((ProjectiveSpectrum.le_iff_mem_closure (𝒜 := ProjSpace.grading k N)
        (ξ0 : ProjectiveSpectrum (ProjSpace.grading k N)) (z : ProjectiveSpectrum (ProjSpace.grading k N))).mp
      (show (⊥ : HomogeneousIdeal (ProjSpace.grading k N)) ≤ z.asHomogeneousIdeal from bot_le))
  have hr : ∀ i, ξ0 ∈ Set.range (ProjSpace.chartι k N i) := fun i => by
    have := hmem i
    rw [← ProjSpace.opensRange_chartι] at this
    exact this
  obtain ⟨η, hη⟩ := hr 0
  let w : Sp (MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) := ⟨⊥, Ideal.bot_prime⟩
  have hηw : η ⤳ w := by
    have h1 : ProjSpace.chartι k N 0 η ⤳ ProjSpace.chartι k N 0 w := by
      rw [hη]
      exact hspec _
    exact (ProjSpace.chartι k N 0).isOpenEmbedding.isInducing.specializes_iff.mp h1
  have hηbot : η.asIdeal = ⊥ := le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr hηw)
  refine ⟨ξ0, fun y => ?_, fun x => ?_⟩
  · have hs : PSpace.str k N ξ0 = (spMap MvPolynomial.C) η := by
      rw [← hη, ← ProjSpace.chartι_str k N 0]
      rfl
    rw [hs]
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    change Ideal.comap (MvPolynomial.C : k →+* MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) η.asIdeal ≤ y.asIdeal
    intro a ha
    rw [Ideal.mem_comap, hηbot, Ideal.mem_bot, MvPolynomial.C_eq_zero] at ha
    rw [ha]
    exact zero_mem _
  · obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
    refine ⟨{j : Fin (N + 1) // j ≠ i}, inferInstance, ProjSpace.chartι k N i, inferInstance, ?_,
      ProjSpace.chartι_str k N i, ?_, hr i⟩
    · simp
    · rw [← ProjSpace.opensRange_chartι] at hi
      exact hi

end GlobalTheory.Amb
