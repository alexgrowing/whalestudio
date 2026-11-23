import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinprodLocalSumsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RestrProd

theorem twOrb_restrProd : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  intro ι G _ _ _ H _ _ _ _ p K KH δ f hpc hinj hglue hfin hK hcpt hKc hcomm hloc hstab hsupp hgood
  have hT : ∀ x, x ∈ twCent (MonoidHom.id G) δ ↔ ∀ i, p i x ∈ twCent (MonoidHom.id (H i)) (p i δ) := by
    intro x
    simp only [GlobalTheory.TwOrbConj.mem_twCent, MonoidHom.id_apply]
    constructor
    · intro h i
      rw [← map_mul, h, map_mul]
    · intro h
      apply hinj
      intro i
      rw [map_mul, h i, map_mul]
  have hC := GlobalTheory.T.mem_compactPart_centralizer_iff_local ι G H p KH _ _ hpc hfin hcpt hKc hT hcomm
  have hCT : ∀ i, cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ twCent (MonoidHom.id (H i)) (p i δ) :=
    fun i => (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have havg1 : ∀ (M : Type) [Group M], avg (fun _ : M => (1 : ℂ)) = 1 := by
    intro M _
    have hR : rStab (fun _ : M => (1 : ℂ)) = ⊤ := by
      ext k
      simp [GlobalTheory.TwOrbConj.mem_rStab]
    unfold avg
    rw [hR, Subgroup.index_top]
    haveI : Subsingleton (M ⧸ (⊤ : Subgroup M)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (M ⧸ (⊤ : Subgroup M)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
    simp [finsum_unique]
  have hs : ∀ g, GlobalTheory.TwOrbConj.summand (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) g =
      ∏ᶠ i, GlobalTheory.TwOrbConj.summand (MonoidHom.id (H i)) (KH i) (p i δ) (f i) (p i g) := by
    intro g
    have hrel := GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct ι G H p K _ _ KH _ _ g hglue hfin hK hT hC hCT (fun i => hloc i (p i g))
      (hgood.mono fun i h => h.2.2.2)
    have hu1 : ∀ᶠ i in cofinite, ∀ k : KH i, f i ((p i g * k)⁻¹ * p i δ * (p i g * k)) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg k
      rw [h.2.1]
      apply Set.indicator_of_mem
      exact (KH i).mul_mem ((KH i).mul_mem ((KH i).inv_mem ((KH i).mul_mem hg k.2)) h.1) ((KH i).mul_mem hg k.2)
    have havg := GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod ι G H p K KH hK (fun i k => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) hglue
      (fun i => hstab i (p i g)) hu1
    have hr1 : ∀ᶠ i in cofinite, (((twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) : ℕ) : ℂ) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg
      rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2), Nat.cast_one]
    have ha1 : ∀ᶠ i in cofinite, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = 1 := by
      filter_upwards [hu1] with i h
      rw [show (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = fun _ => 1 from funext h]
      exact havg1 _
    have e1 : avg (fun k : K => ∏ᶠ i, f i (p i ((g * ↑k)⁻¹ * δ * (MonoidHom.id G) (g * ↑k)))) =
        ∏ᶠ i, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) := by
      rw [← havg]
      congr 1
      funext k
      simp [map_mul, map_inv]
    unfold GlobalTheory.TwOrbConj.summand
    simp only [MonoidHom.id_apply] at e1 ⊢
    have hN : Function.HasFiniteMulSupport fun i => (twCent (MonoidHom.id (H i)) (p i δ) ⊓
        (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) := by
      have : ∀ᶠ i in cofinite, (twCent (MonoidHom.id (H i)) (p i δ) ⊓
          (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) = 1 := by
        filter_upwards [hgood, hfin g] with i h hg
        rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2)]
      exact Filter.eventually_cofinite.1 this
    have hcast := map_finprod (Nat.castRingHom ℂ) hN
    simp only [eq_natCast] at hcast
    rw [e1, hrel, hcast, ← finprod_mul_distrib (Filter.eventually_cofinite.1 hr1) (Filter.eventually_cofinite.1 ha1)]
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  simp only [GlobalTheory.TwOrbConj.twOrb_eq]
  refine GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums ι G H p _ K _ KH _ _ hglue hfin hK hT ?_ ?_ ?_ hs
  · intro i t ht k hk x
    exact GlobalTheory.TwOrbConj.summand_rep _ _ _ _ x ht hk
  · intro i
    refine (hsupp i).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    have h0 : (fun k : KH i => f i ((Quotient.out q * k)⁻¹ * p i δ * (MonoidHom.id (H i)) (Quotient.out q * k))) =
        fun _ => 0 := by
      funext k
      by_contra hk
      exact hcon ⟨k, k.2, hk⟩
    unfold GlobalTheory.TwOrbConj.summand
    rw [h0]
    simp [avg]
  · filter_upwards [hgood] with i h x
    rw [h.2.1]
    exact GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator (H i) (KH i) (p i δ) h.1 h.2.2.2 h.2.2.1 x

end GlobalTheory.RestrProd
