import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArith
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieFD

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Pf.AlTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

def DiscriminantAbsEq : Prop := |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)|

def InfinitePlacesCardEq : Prop := Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F

def EulerProductEta : Prop :=
  ∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)

def LocalFactorProduct : Prop :=
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1))

def VInvEqHalfRootDiscriminant : Prop :=
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2

def QuadraticInfinitePlaces : Prop := Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F

def DifferentGeneratorUnit : Prop := ∀ p : TypX X, absV p.1 (dV p.1) = 1

def TypedGeneratorProduct : Prop := ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

theorem discriminant_abs_eq : DiscriminantAbsEq X := by
  unfold DiscriminantAbsEq
  rw [NumberField.discr_eq_discr_of_algEquiv X.B.I.F (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X))]

theorem finrank_eq : Module.finrank ℚ X.B.I.F = Module.finrank ℚ D.host.F :=
  (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).toLinearEquiv.finrank_eq

theorem infinite_places_card : InfinitePlacesCardEq X := by
  unfold InfinitePlacesCardEq
  rw [← finrank_eq X]
  haveI := X.B.I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank X.B.I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h1
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h1]

theorem T_not_mem (w : D.what₂.Word) (p : TypX X) : ¬ ((((D.mem w).A.T : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal) := by
  intro hw
  have hc := (resChar_eq_iff (plEquiv X p.1) (D.mem w).A.T_prime).2 ((natCast_mem_plEquiv X p.1 _).2 hw)
  rcases (typAt_iff X p.1).1 p.2 with h | h
  · exact D.T_ne_g w 0 (hc.symm.trans h)
  · exact D.T_ne_g w 1 (hc.symm.trans h)

theorem local_a_factor_symmetric : ∀ p : TypX X,
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) := by
  intro p
  unfold aP Tw
  rw [if_neg (T_not_mem X u' p), if_neg (T_not_mem X u p)]

theorem fieldDict_of (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) (h6 : QuadraticInfinitePlaces (D := D)) (h8 : DifferentGeneratorUnit X)
    (h10 : TypedGeneratorProduct X) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := by
  unfold Formalism.L2.SG.Pf.NcVal.FieldDict
  exact ⟨discriminant_abs_eq X, infinite_places_card X, h3, h4, h5, h6, X.n_eq, h8, local_a_factor_symmetric X u u', h10⟩

theorem over_g_of_typed (p : TypX X) : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have h := (mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero p.1).1 p.2
  rcases h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem different_generator_unit : DifferentGeneratorUnit X := by
  intro p
  obtain ⟨i, hi⟩ := over_g_of_typed X p
  have hnd := not_dvd_diff X p.1 i hi
  have hex : ∃ x ∈ differentIdeal ℤ (𝓞 X.B.I.F), x ∉ p.1.asIdeal := by
    by_contra hc
    push Not at hc
    exact hnd (Ideal.dvd_iff_le.2 hc)
  have hval : ∀ x : 𝓞 X.B.I.F,
      Valued.v (algebraMap X.B.I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv X.B.I.F p.1) (x : X.B.I.F)) = p.1.intValuation x := by
    intro x
    have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := X.B.I.F) p.1 x
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at h
    exact h
  have hv1 : Valued.v (dV p.1) = 1 := by
    unfold dV
    split_ifs with hd
    · obtain ⟨-, hle, x0, -, heq⟩ := hd.choose_spec
      obtain ⟨x1, hx1, hx1n⟩ := hex
      have h1 := hle x1 hx1
      rw [hval, (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hx1n] at h1
      rw [hval] at heq
      have h2 := p.1.intValuation_le_one x0
      rw [heq] at h2
      exact le_antisymm h2 h1
    · exact map_one _
  unfold absV
  split_ifs with h0
  · exact absurd (hv1 ▸ h0) one_ne_zero
  · have e2 : WithZero.unzero h0 = 1 := by
      apply WithZero.coe_inj.1
      rw [WithZero.coe_unzero, hv1, WithZero.coe_one]
    rw [e2]
    simp

theorem not_both (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
  obtain ⟨a, b, hab⟩ := hcop
  have hone : (1 : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 X.B.I.F) hab
    push_cast at e
    rw [← e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h0) (v.asIdeal.mul_mem_left _ h1)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem card_over (i : Fin 2) :
    ({v : HeightOneSpectrum (𝓞 X.B.I.F) | ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}).ncard =
      Module.finrank ℚ X.B.I.F := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  have := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hsum := Ideal.sum_ramification_inertia (𝓞 X.B.I.F) ℚ X.B.I.F hq0
  have hall : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((D.host.g i : ℕ) : ℤ)}) (𝓞 X.B.I.F),
      (Ideal.span {((D.host.g i : ℕ) : ℤ)}).ramificationIdx' Q * (Ideal.span {((D.host.g i : ℕ) : ℤ)}).inertiaDeg' Q = 1 := by
    intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff hq0] at hQ
    have hQ' : Q ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := hQ
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp] at hQ'
    obtain ⟨v, hv, rfl⟩ := hQ'
    obtain ⟨he, hf⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
    rw [he, hf]
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [← hsum, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0,
    Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]
  exact (Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)).symm

theorem typed_generator_product : TypedGeneratorProduct X := by
  unfold TypedGeneratorProduct
  have hg0 := (D.host.g_prime 0).ne_zero
  have hg1 := (D.host.g_prime 1).ne_zero
  have hA0 := finite_over X.B.I.F (D.host.g 0) hg0
  have hA1 := finite_over X.B.I.F (D.host.g 1) hg1
  have hT : typSet X.B.I.F (D.host.g 0) (D.host.g 1) = hA0.toFinset ∪ hA1.toFinset := by
    ext v
    rw [mem_typSet _ _ _ hg0 hg1, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rfl
  have hdisj : Disjoint hA0.toFinset hA1.toFinset :=
    Finset.disjoint_left.2 fun v h0 h1 =>
      not_both X v (hA0.mem_toFinset.1 h0) (hA1.mem_toFinset.1 h1)
  have hc0 : hA0.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA0, card_over X 0, finrank_eq X]
  have hc1 : hA1.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA1, card_over X 1, finrank_eq X]
  have hg0v : ∀ v ∈ hA0.toFinset, (gAt X v : ℝ) = (D.host.g 0 : ℝ) := by
    intro v hv
    rw [gAt, if_pos (show ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal from hA0.mem_toFinset.1 hv)]
  have hg1v : ∀ v ∈ hA1.toFinset, (gAt X v : ℝ) = (D.host.g 1 : ℝ) := by
    intro v hv
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := hA1.mem_toFinset.1 hv
    rw [gAt, if_neg (fun h0 => not_both X v h0 h1)]
  show ∏ p : ↥(typSet X.B.I.F (D.host.g 0) (D.host.g 1)), (gAt X p.1 : ℝ) = _
  rw [Finset.prod_coe_sort (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (fun v => (gAt X v : ℝ)), hT,
    Finset.prod_union hdisj, Finset.prod_congr rfl hg0v, Finset.prod_congr rfl hg1v, Finset.prod_const,
    Finset.prod_const, hc0, hc1, ← mul_pow]
  unfold Lat.gS
  push_cast
  rfl

theorem totally_complex_quadratic : QuadraticInfinitePlaces (D := D) := by
  unfold QuadraticInfinitePlaces Formalism.HermitianLatticesTheory.fDeg
  have : IsTotallyComplex D.host.E := (Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D).1.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
  have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [Formalism.BasicNotions.Examples₂.finrank_FE D.host] at h4
  omega

theorem field_dictionary_of_leaves (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := fieldDict_of X u u' h3 h4 h5 (totally_complex_quadratic (D := D)) (different_generator_unit X) (typed_generator_product X)

theorem discriminant_sq_relation : VInvEqHalfRootDiscriminant (D := D) := by
  unfold VInvEqHalfRootDiscriminant Formalism.HermitianLatticesTheory.vInv
  have h6 : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F := totally_complex_quadratic
  rw [h6, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  congr 1
  push_cast
  rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  have hf : (0 : ℝ) < Module.finrank ℚ D.host.F := by exact_mod_cast Module.finrank_pos
  field_simp
  norm_num

end Formalism.L2.SG.Pf.AlTieFD
