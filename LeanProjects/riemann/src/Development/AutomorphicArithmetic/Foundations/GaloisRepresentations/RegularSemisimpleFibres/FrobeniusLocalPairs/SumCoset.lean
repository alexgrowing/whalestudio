import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private lemma UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk {G : Type} [Group G] (T K : Subgroup G)
    (q : DoubleCoset.Quotient (T : Set G) (K : Set G)) (g : G) :
    (∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y) ↔ DoubleCoset.mk T K g = q := by
  have h := DoubleCoset.eq T K (Quotient.out q) g
  rw [DoubleCoset.out_eq'] at h
  exact h.symm.trans eq_comm

theorem UpperTheory.Gal.InertialTypesAlt.L.sumCoset :
    UpperTheory.Gal.InertialTypesAlt.L.SumCoset := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hcomm ν hν F hF hFT hFC
  obtain ⟨hsf, hinv, hrinv⟩ := haarComm_holds G T hTc hcomm ν hν
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hrinv
  have hInt := quotInt_holds G μ hμ T hTc ν hν hinv F hF hFT hFC ρ hρ
  obtain ⟨C, hC, hFC'⟩ := hFC
  have hFm : Measurable F := hF.measurable
  have hmk : ∀ h ∈ T, ∀ g : G, DoubleCoset.mk T K (h * g) = DoubleCoset.mk T K g :=
    fun h hh g => ((DoubleCoset.eq T K g (h * g)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm
  set Q : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)) :=
    {q | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0} with hQ
  have hkey : ∀ g, F g ≠ 0 → DoubleCoset.mk T K g ∈ Q := by
    intro g hg
    obtain ⟨t, ht, y, hy, he⟩ :=
      (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K (DoubleCoset.mk T K g) g).2 rfl
    refine ⟨y, hy, ?_⟩
    have e : Quotient.out (DoubleCoset.mk T K g) * y = t⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
      exact he.symm
    rw [e, hFT t⁻¹ (T.inv_mem ht) g]
    exact hg
  have hfin : Q.Finite := by
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun c : G => {z : G | c⁻¹ * z ∈ K})
      (fun c => hKo.preimage (continuous_mul_left c⁻¹))
      (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [K.one_mem]⟩)
    refine (s.finite_toSet.image (DoubleCoset.mk T K)).subset ?_
    rintro q ⟨y, hy, hq⟩
    obtain ⟨t, ht, c, hc, he⟩ := hFC' _ hq
    obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (hs hc)
    refine ⟨i, hi, ?_⟩
    rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
    refine ⟨t, ht, i⁻¹ * c * y⁻¹, K.mul_mem hci (K.inv_mem hy), ?_⟩
    calc Quotient.out q = Quotient.out q * y * y⁻¹ := by group
      _ = t * c * y⁻¹ := by rw [he]
      _ = t * i * (i⁻¹ * c * y⁻¹) := by group
  refine ⟨hfin, ?_⟩
  have hS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      {g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y} = {g | DoubleCoset.mk T K g = q} :=
    fun q => Set.ext (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K q)
  simp_rw [hS]
  have hSo : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      IsOpen {g | DoubleCoset.mk T K g = q} := by
    intro q
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨{z | g⁻¹ * z ∈ K}, fun z hz => ?_, hKo.preimage (continuous_mul_left g⁻¹),
      by simp [K.one_mem]⟩
    show DoubleCoset.mk T K z = q
    rw [← (show DoubleCoset.mk T K g = q from hg), eq_comm, DoubleCoset.eq]
    exact ⟨1, T.one_mem, g⁻¹ * z, hz, by group⟩
  have hSinv : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ∀ h ∈ T, ∀ g : G,
      {g | DoubleCoset.mk T K g = q}.indicator F (h * g) =
        {g | DoubleCoset.mk T K g = q}.indicator F g := by
    intro q h hh g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hmk h hh g, hFT h hh g]
  have hq_eq : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) =
        ∫ g, {g | DoubleCoset.mk T K g = q}.indicator
          (fun g => F g * ((ρ g).toReal : ℂ)) g ∂μ := by
    intro q
    rw [quotIndep_holds G μ hμ T ν hsf hinv _ (hFm.indicator (hSo q).measurableSet) (hSinv q) ρ hρ]
    congr 1
    funext g
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (T : Set G) (K : Set G) =>
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F)) ⊆
        ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    by_contra hqQ
    apply hq
    have h0 : {g | DoubleCoset.mk T K g = q}.indicator F = 0 := by
      funext g
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.zero_apply]
      split_ifs with hg
      · by_contra hne
        exact hqQ (hg ▸ hkey g hne)
      · rfl
    show quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = 0
    rw [h0]
    simp [quotIntegral]
  rw [quotIndep_holds G μ hμ T ν hsf hinv F hFm hFT ρ hρ, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_congr rfl (fun q _ => hq_eq q),
    ← integral_finset_sum _ (fun q _ => hInt.indicator (hSo q).measurableSet)]
  congr 1
  funext g
  by_cases hg : F g = 0
  · simp [Set.indicator_apply, hg]
  · rw [Finset.sum_eq_single (DoubleCoset.mk T K g)]
    · simp [Set.indicator_apply]
    · intro b _ hb
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (fun h => hb h.symm)]
    · intro hn
      exact absurd (hfin.mem_toFinset.2 (hkey g hg)) hn
