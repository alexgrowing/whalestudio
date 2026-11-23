import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsInvariantLiftAverage
import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem unitStep_holds {e : W.DD W.one} (hUnitGen : UnitGen W e) (hCrysOne : IsCrys PD W.one.ρ) :
    UnitStep W e := by
  have hB := unitBasis_of hUnitGen hCrysOne
  have hγ : ∀ g, W.γD W.one g e = e := hUnitGen.2.2.1
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, hc2⟩ := hc ()
    simp only [lc, Fintype.sum_unique]
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [← smul_assoc, hc1]
    · rw [W.γD_smul, hγ, hc2 δ hδ]
  · intro c c' _ _ h
    simp only [lc, Fintype.sum_unique] at h
    funext u
    obtain ⟨ε, _, huniq⟩ := hB (c () • e)
    exact (huniq (c u) rfl).trans (huniq (c' u) h).symm
  · intro x hx
    obtain ⟨ε, hε, huniq⟩ := hB x
    obtain ⟨h1, h2⟩ := hx
    refine ⟨fun _ => ε, fun _ => ⟨?_, fun δ hδ => ?_⟩, ?_⟩
    · have hx' : x = ((letE i : LetA O n) • ε) • e := by
        rw [smul_assoc, ← hε, h1]
      exact huniq _ hx'
    · have hx' : x = W.γE δ ε • e := by
        conv_lhs => rw [← h2 δ hδ, hε]
        rw [W.γD_smul, hγ]
      exact huniq _ hx'
    · simp only [lc, Fintype.sum_unique]
      exact hε.symm

theorem splitStep_holds (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (hs : W.s = 1) (hp2 : PD.p ≠ 2) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h) :
    SplitStep W := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨m₁, B₁, hB₁, -⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₁ hc₁.2.2.2
  obtain ⟨m₂, B₂, hB₂, hB₂N⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₂ hc₂.2.2.2
  have hcu := isUnit_card_finiteDelta hP9 hs hp2 T₁ hc₁.2.2.2
  have hlift : ∀ k, ∃ w : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w = w) ∧ W.map F w = B₂ k := by
    intro k
    obtain ⟨w₀, hw₀⟩ := exists_lift_of_onto hs hLem3 hJ F hc₁ hc₂ hon (B₂ k) (hB₂N k)
    exact exists_invariant_lift_average hcu F w₀ (B₂ k) (hB₂ k) hw₀
  choose w hwΔ hwF using hlift
  refine ⟨m₂, m₁ - m₂, fun i => ?_⟩
  have hloc := letterRing_isLocalRing (W := W) hOloc hOnil i
  set M : Fin m₁ → Fin m₂ → W.EE := fun l k => B₂.repr (W.map F (B₁ l)) k with hMdef
  have hMγ : ∀ l k, ∀ δ ∈ W.DelF, W.γE δ (M l k) = M l k := by
    intro l k δ hδ
    rw [hMdef, ← basis_repr_gamma B₂ hB₂ _ δ hδ, ← W.map_γ, hB₁ l δ hδ]
  have hM : ∀ l k, k17e W i * M l k ∈ EEl W i := by
    intro l k
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
    · rw [map_mul, idempotent_gamma_invariant, hMγ l k δ hδ]
  choose μ hμ using fun l k => letterRing_val_surjective i _ (hM l k)
  have hcoef : ∀ (u : Fin m₁ → k17R W i) (k : Fin m₂),
      letterRingVal W i (k17f μ u k) = ∑ l, letterRingVal W i (u l) * M l k := by
    intro u k
    change letterRingVal W i (∑ l, u l * μ l k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [letterRing_val_mul, hμ, ← mul_assoc, letterRing_mul_idempotent]
  have hmap : ∀ u : Fin m₁ → k17R W i, W.map F (∑ l, letterRingVal W i (u l) • B₁ l) =
      ∑ k, letterRingVal W i (k17f μ u k) • B₂ k := by
    intro u
    simp only [hcoef, Finset.sum_smul, map_sum, map_smul]
    have h1 : ∀ l, W.map F (B₁ l) = ∑ k, M l k • B₂ k := fun l => (B₂.sum_repr _).symm
    simp only [h1, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hstd : ∀ k, ∃ u : Fin m₁ → k17R W i, k17f μ u = Pi.single k 1 := by
    intro k
    have hd : ∀ l, k17e W i * B₁.repr (w k) l ∈ EEl W i := by
      intro l
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
      · rw [map_mul, idempotent_gamma_invariant, ← basis_repr_gamma B₁ hB₁ _ δ hδ, hwΔ k δ hδ]
    obtain ⟨u, hu⟩ := exists_preimage_letter_ring i _ hd
    refine ⟨u, funext fun k' => letterRing_val_injective i ?_⟩
    have h1 : ∑ l, letterRingVal W i (u l) • B₁ l = k17e W i • w k := by
      simp only [hu, ← smul_smul, ← Finset.smul_sum, B₁.sum_repr]
    have h2 := hmap u
    rw [h1, map_smul, hwF] at h2
    have h3 : k17e W i • B₂ k = ∑ k', letterRingVal W i ((Pi.single k 1 : Fin m₂ → k17R W i) k') • B₂ k' := by
      simp only [Pi.single_apply]
      simp only [apply_ite (letterRingVal W i), map_zero, letterRing_val_one, ite_smul, zero_smul]
      rw [Finset.sum_ite_eq']
      simp
    rw [h3] at h2
    exact congrFun (basis_coefficients_unique B₂ h2.symm) k'
  choose ν hν using hstd
  have hsurj : Function.Surjective (k17f μ) := by
    intro y
    refine ⟨∑ k, y k • ν k, ?_⟩
    rw [map_sum]
    simp only [map_smul, hν]
    funext k'
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨C, hCl, hCr⟩ := exists_basis_of_surjective (k17f μ) hsurj
  refine ⟨fun t => ∑ l, letterRingVal W i (C t l) • B₁ l,
    fun j => ∑ l, letterRingVal W i (Pi.basisFun (k17R W i) (Fin m₂) j l) • B₂ l,
    letter_invariants_basis B₁ hB₁ i C, letter_invariants_basis B₂ hB₂ i (Pi.basisFun _ _), fun j => ?_, fun j => ?_⟩
  · rw [hmap, hCl]
    simp only [Pi.basisFun_apply]
  · rw [hmap, hCr]
    simp

end Formalism.MainNotions.N.Ln03.Pf
