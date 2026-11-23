import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousLiftToJoinStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousNonvanishingOnJoinStatement

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace ResTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem coord_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem charZero_of_horizontal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, map_natCast, map_natCast,
      ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [IsHorizontal] at h
  rw [h, Ideal.mem_bot] at h1
  exact_mod_cast h1

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem isBlockMap_joinInl : IsBlockMap (Sum.inl : K → K ⊕ K₂) (joinInl ι ι₂) := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Sum.inl_injective (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨k, i⟩ ⟨k', rfl⟩
    exact ⟨⟨k', i⟩, rfl⟩

theorem evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (f : MRing ι) :
    evC z (rename (joinInl ι ι₂) f) = evC (z ∘ joinInl ι ι₂) f := by
  unfold evC
  rw [map_rename, eval_rename]

theorem comp_inl_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {z : (Σ k, joinIdx ι ι₂ k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y₂))) :
    z ∘ joinInl ι ι₂ ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have hc : (mConeMap (joinVec y y₂)).comp (rename (joinInl ι ι₂)) =
      ((rename (Sum.inl : K → K ⊕ K₂) : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars ℤ).comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨k, i⟩ := p
    simp [mConeMap, joinInl, joinVec]
  have hf' : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y y₂) := by
    have h1 := AlgHom.congr_fun hc f
    have h0 : mConeMap y f = 0 := hf
    simp only [AlgHom.comp_apply, h0, map_zero] at h1
    exact h1
  exact (evC_rename_inl z f).symm.trans (hz.2 _ hf')

end ResTop

open ResTop in

theorem resExists_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ResExistsStatement := by
  intro hRes K _ ι _ P J e hP hJ hJP
  obtain ⟨Ω, _, y, rfl, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K ι P (e + 1) hP
  haveI : CharZero Ω := charZero_of_horizontal y hP.2.2.1
  have hprime : (mCoordIdeal y).IsPrime := hP.2.1.1
  obtain ⟨β, hβJ, ⟨b, hβ⟩, hβP⟩ : ∃ β ∈ J, (∃ b, IsMultiHomog β b) ∧ β ∉ mCoordIdeal y := by
    obtain ⟨S, hS, rfl⟩ := hJ
    by_contra hcon
    push Not at hcon
    exact hJP (Ideal.span_le.mpr fun f hf => hcon f (Ideal.subset_span hf) (hS f hf))
  obtain ⟨β', b', M, y', J₁, hβ', hβ'P, hzero, hy', hfield, hJ₁h, hJ₁, hsnc, hz, hG⟩ :=
    GlobalTheory.T.multihomogeneous_lift_to_join hRes K ι Ω y e β b hP hβ hβP
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  have hblocks : ∀ k, ∃ i, joinVec y y' ⟨k, i⟩ ≠ 0 := by
    rintro (k | u)
    · exact hy k
    · exact hy'
  have hcomp : joinVec y y' ∘ joinInl ι (fun _ : Unit => Fin M) = y := rfl
  have harith : IsArithVar (mCoordIdeal (joinVec y y')) (e + 1) := by
    refine isArithVar_of_isAlgebraic_image K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y') (e + 1) isBlockMap_joinInl hblocks ?_ ?_
    · rw [hcomp]; exact hP
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y') e J₁
    harith hJ₁h hJ₁ hsnc
  have hγ := homog_mul hβ hβ'
  have hγP : β * β' ∉ mCoordIdeal y := fun h => (hprime.mem_or_mem h).elim hβP hβ'P
  have hmul : ∀ z : (Σ k, ι k) → ℂ, evC z (β * β') = evC z β * evC z β' := fun z => by
    simp only [evC, map_mul]
  refine ⟨Ideal.span {β * β'}, ?_, ⟨{β * β'}, ?_, rfl⟩, ?_, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact J.mul_mem_right _ hβJ
  · rintro f rfl
    exact ⟨_, hγ⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hγP
  · refine GlobalTheory.T.multihomogeneous_nonvanishing_on_join K ι Ω y e M y' J₁ R (β * β') (b + b') hR hy' hy hγ hγP ?_ ?_
    · intro z hzm h0
      apply hz z hzm
      rw [evC_rename_inl] at h0 ⊢
      rw [hmul] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact hzero _ (comp_inl_mem y y' hzm) h
      · exact h
    · intro z hzm hne
      apply hG z hzm
      rw [hmul] at hne
      exact right_ne_zero_of_mul hne

end GlobalTheory.CompanionTheory.Ar.Giv
