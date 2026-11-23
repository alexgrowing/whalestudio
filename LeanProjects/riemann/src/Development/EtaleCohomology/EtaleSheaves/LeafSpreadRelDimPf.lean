import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf

namespace LateralTheory.E.LeafSpreadRelDimPf

def LeafRelDimAtImage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ y : C, ∃ V : D.Opens, v y ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q)

def LeafGenericOpenSpread : Prop := ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (D : Scheme.{0}) (q : D ⟶ Sp A),
    IsAffine D → LocallyOfFinitePresentation q → ∀ U : D.Opens,
    (∀ x : D, (show PrimeSpectrum A from q x).asIdeal = ⊥ → x ∈ U) →
    ∃ f : A, f ≠ 0 ∧ ∀ x : D, f ∉ (show PrimeSpectrum A from q x).asIdeal → x ∈ U

theorem generic_pt {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (ω : Sp Ω) :
    (show PrimeSpectrum R from toR R ω).asIdeal = ⊥ := by
  have h0 : (show PrimeSpectrum Ω from ω).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap (algebraMap R Ω) (show PrimeSpectrum Ω from ω).asIdeal = ⊥
  rw [h0]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R Ω)

theorem LeafSpreadRelDim_of_sub (hA : LeafRelDimAtImage) (hB : LeafGenericOpenSpread) : LeafSpreadRelDim := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv
  let U : D.Opens := sSup {V : D.Opens | SmoothOfRelativeDimension 1 (V.ι ≫ q)}
  have hU : ∀ x : D, (show PrimeSpectrum R from q x).asIdeal = ⊥ → x ∈ U := by
    intro x hx
    let ω : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    have he : q x = toR R ω := PrimeSpectrum.ext (hx.trans (generic_pt R ω).symm)
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x ω he
    obtain ⟨V, hV, hVs⟩ := hA k Ω R hR c q v hD hlfp hsm hs hv (hv.isoPullback.inv z)
    have : v (hv.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz1]
    rw [this] at hV
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hVs, hV⟩
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨f, hf0, hf⟩ := hB R D q hD hlfp U hU
  have hf0' : (f : Ω) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let T : Subalgebra k Ω := Algebra.adjoin k ((({((f : Ω))⁻¹} : Finset Ω)) : Set Ω)
  refine ⟨R ⊔ T, le_sup_left, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  intro R' hR' hRR E q' r hE
  have hinv : ((f : Ω))⁻¹ ∈ R' :=
    hR' (le_sup_right (a := R) (Algebra.subset_adjoin (by simp)))
  have hunit : IsUnit (Subalgebra.inclusion hRR f) := by
    have h1 : Subalgebra.inclusion hRR f * (⟨_, hinv⟩ : R') = 1 := Subtype.ext (mul_inv_cancel₀ hf0')
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun V : {V : D.Opens // SmoothOfRelativeDimension 1 (V.ι ≫ q)} => r ⁻¹ᵁ V.1) ?_ ?_
  · refine top_le_iff.mp fun e _ => ?_
    have hq : q (r e) = incl hRR (q' e) := by
      rw [← Scheme.Hom.comp_apply, hE.w, Scheme.Hom.comp_apply]
    have hx : f ∉ (show PrimeSpectrum R from q (r e)).asIdeal := by
      rw [hq]
      change Subalgebra.inclusion hRR f ∉ (show PrimeSpectrum R' from q' e).asIdeal
      exact fun h => (show PrimeSpectrum R' from q' e).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h hunit)
    obtain ⟨V, hVs, hV⟩ := TopologicalSpace.Opens.mem_sSup.mp (hf (r e) hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hV⟩
  · intro V
    have h2 := (isPullback_morphismRestrict r V.1).paste_vert hE
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback h2 V.2

end LateralTheory.E.LeafSpreadRelDimPf

namespace LateralTheory.E.LeafSpreadRelDimPf.Spread
open Topology TopologicalSpace

theorem exists_ne_zero_of_constructible {A : Type} [CommRing A] [IsDomain A] (T : Set (PrimeSpectrum A))
    (hT : IsConstructible T) (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ T) :
    ∃ f : A, f ≠ 0 ∧ ∀ p ∈ T, f ∈ p.asIdeal := by
  revert h
  induction T, hT using IsConstructible.induction_of_isTopologicalBasis
    (fun f : A => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))
    PrimeSpectrum.isTopologicalBasis_basic_opens (fun f => PrimeSpectrum.isCompact_basicOpen f) with
  | sdiff g s hs =>
    intro h
    by_cases hg : g = 0
    · refine ⟨1, one_ne_zero, fun p hp => ?_⟩
      have := hp.1
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hg] at this
      exact absurd p.asIdeal.zero_mem this
    · have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hg
      have : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ ⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum A)) := by
        by_contra hn; exact h ⟨hη, hn⟩
      obtain ⟨j, hj, hηj⟩ := Set.mem_iUnion₂.mp this
      have hj0 : j ≠ 0 := by simpa [PrimeSpectrum.mem_basicOpen] using hηj
      refine ⟨j, hj0, fun p hp => ?_⟩
      have h2 := hp.2
      by_contra hn
      exact h2 (Set.mem_iUnion₂.mpr ⟨j, hj, by simpa [PrimeSpectrum.mem_basicOpen] using hn⟩)
  | union s hs t ht ihs iht =>
    intro h
    obtain ⟨f1, h1, hf1⟩ := ihs (fun hh => h (Or.inl hh))
    obtain ⟨f2, h2, hf2⟩ := iht (fun hh => h (Or.inr hh))
    refine ⟨f1 * f2, mul_ne_zero h1 h2, fun p hp => ?_⟩
    rcases hp with hp | hp
    · exact Ideal.mul_mem_right _ _ (hf1 p hp)
    · exact Ideal.mul_mem_left _ _ (hf2 p hp)

theorem LeafGenericOpenSpread_pf : LeafGenericOpenSpread := by
  intro A _ _ _ D q hD hlfp U hU
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := {}
  have hZ : IsConstructible ((U : Set D)ᶜ) :=
    ((NoetherianSpace.isCompact (U : Set D)).isConstructible U.isOpen).compl
  have : QuasiCompact q := inferInstance
  have hI := q.isConstructible_image hZ
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_of_constructible (A := A) (q '' ((U : Set D)ᶜ)) hI (by
    rintro ⟨x, hx, hqx⟩
    exact hx (hU x (by rw [hqx])))
  refine ⟨f, hf0, fun x hx => ?_⟩
  by_contra hxU
  exact hx (hf (q x) ⟨x, hxU, rfl⟩)

end LateralTheory.E.LeafSpreadRelDimPf.Spread

namespace LateralTheory.E.LeafSpreadRelDimPf

theorem LeafRelDimAtImage_pf : LeafRelDimAtImage := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv y
  obtain ⟨n, W, hW, hWs⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim q (v y)
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_base hv hWs hs y hW
  subst this
  exact ⟨W, hW, hWs⟩

theorem LeafSpreadRelDim_of : LeafSpreadRelDim :=
  LeafSpreadRelDim_of_sub LeafRelDimAtImage_pf Spread.LeafGenericOpenSpread_pf

end LateralTheory.E.LeafSpreadRelDimPf

end
