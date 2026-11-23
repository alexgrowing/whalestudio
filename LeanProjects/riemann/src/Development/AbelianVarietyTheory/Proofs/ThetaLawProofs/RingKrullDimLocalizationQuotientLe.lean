import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsRegularOfFnOfRingKrullDimQuotientAddLe
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZerosStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
