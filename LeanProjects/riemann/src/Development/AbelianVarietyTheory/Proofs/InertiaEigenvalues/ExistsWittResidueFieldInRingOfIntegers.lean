import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Res

open IsLocalRing

theorem exists_teich {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (x : O) :
    ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ t - x ∈ maximalIdeal O := by
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  obtain ⟨t, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X)
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq)) x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue O _)
      simp [Polynomial.derivative_X_pow, FiniteField.cast_card_eq_zero])
  exact ⟨t, by simpa [sub_eq_zero] using h1, h2⟩

theorem sol_mem_range {O F : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] [Field F] (f : O →+* F) (hf : Function.Injective f) (y : F)
    (hy : y ^ Fintype.card (ResidueField O) = y) : ∃ t, f t = y := by
  classical
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  have : ∀ r : ResidueField O, ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ residue O t = r := fun r => by
    obtain ⟨x, rfl⟩ := residue_surjective r
    obtain ⟨t, h1, h2⟩ := exists_teich x
    exact ⟨t, h1, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  choose t h1 h2 using this
  have hinj : Function.Injective fun r => f (t r) := fun r s h => by
    rw [← h2 r, ← h2 s, hf h]
  set P : Polynomial F := Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hd : P.natDegree = Fintype.card (ResidueField O) := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hm : ∀ z : F, z ^ Fintype.card (ResidueField O) = z → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hz]
  have hs : Finset.univ.image (fun r => f (t r)) = P.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hz
      exact hm _ (by rw [← map_pow, h1])
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hd]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  obtain ⟨r, -, hr⟩ := Finset.mem_image.1 (hs ▸ hm y hy)
  exact ⟨_, hr⟩

theorem exists_witt_residue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (a : ℕ) (_ : NeZero a) (w : Wq l a →ₐ[ℤ_[l]] ↥(OL K)), Kunr l a ≤ K.1 ∧ (∀ c, intToOC K (w c) = Per.θ l (wA l a c)) ∧ ∀ x : ↥(OL K), ∃ c, ¬ IsUnit (x - w c) := by
  intro l hl K
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hfin : Module.Finite ℤ_[l] ↥(OL K) := finite_OL K
  have hfin' : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥K.1) := hfin
  have hdvr : IsDiscreteValuationRing ↥(OL K) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥K.1
  have hfa := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥K.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥K.1
  have hc : IsAdicComplete (maximalIdeal ↥(OL K)) ↥(OL K) :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _
  have hF : Finite (ResidueField ↥(OL K)) :=
    ResidueField.finite_of_finite (R := ℤ_[l]) (Finite.of_equiv _ PadicInt.residueField.symm.toEquiv)
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have hch : CharP (ResidueField ↥(OL K)) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue ↥(OL K)), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] ↥(OL K)),
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff]
    exact PadicInt.p_nonunit
  obtain ⟨a, -, ha⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  have hne : NeZero (a : ℕ) := ⟨a.ne_zero⟩
  let f : ↥(OL K) →+* Om l := K.1.val.toRingHom.comp (OL K).val.toRingHom
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hle : Kunr l a ≤ K.1 := IntermediateField.adjoin_le_iff.2 fun y hy => by
    obtain ⟨t, rfl⟩ := sol_mem_range f hf y (by rw [ha]; exact hy)
    exact (t : ↥K.1).2
  have : HasUnr a K := ⟨hle⟩
  refine ⟨a, hne, thetaW a K, hle, intToOC_thetaW a K, fun x => ?_⟩
  obtain ⟨t, h1, h2⟩ := exists_teich x
  rw [ha] at h1
  suffices ∃ c, thetaW a K c = t by
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, fun h => h2 (by simpa using h.neg)⟩
  rcases eq_or_ne t 0 with rfl | h0
  · exact ⟨0, map_zero _⟩
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h3 := one_lt_pow_l l a
  have : NeZero (l ^ (a : ℕ) - 1) := ⟨by omega⟩
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one (ξ := f t) (by
    rw [← map_pow, ← map_one f]
    congr 1
    exact mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, one_mul, h1]))
  refine ⟨WittVector.teichmuller l z ^ k, intToOC_injective K ?_⟩
  rw [intToOC_thetaW, map_pow, map_pow, wA_teich, WittVector.fontaineTheta_teichmuller]
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
  exact (map_pow (algebraMap (Om l) ℂ_[l]) ω k).symm.trans (congrArg _ hk)

end GlobalTheory.BSP.Res
