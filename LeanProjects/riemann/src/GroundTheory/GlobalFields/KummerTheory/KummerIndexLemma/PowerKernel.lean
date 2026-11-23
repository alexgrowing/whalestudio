import Mathlib
import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.Places
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
import GroundTheory.GlobalFields.SplittingFromInequality

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh Module
  Filter IntermediateField AdeleBaseChange SemiLocal IdeleNorm

open scoped NumberField.LiesOver

namespace KummerIndex

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem finiteProj_mem_localUnits {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K}
    (h : IdeleGroup.ord v x = 0) : IdeleGroup.finiteProj v x ∈ localUnits v := by
  have hx := (IdeleGroup.ord_eq_zero_iff v x).1 h
  rw [localUnits, Submonoid.mem_units_iff]
  have h2 : ((IdeleGroup.finiteProj v x)⁻¹ : (v.adicCompletion K)ˣ) =
      IdeleGroup.finiteProj v x⁻¹ := (map_inv _ _).symm
  rw [h2, IdeleGroup.coe_finiteProj, IdeleGroup.coe_finiteProj]
  exact hx

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (b : (v.adicCompletion K)ˣ) : b ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  classical
  let y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ := fun w ↦
    Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
      v.adicCompletion K →* w.1.adicCompletion L) b
  refine ⟨y, ?_⟩
  rw [← Finset.univ_prod_mulSingle y, map_prod]
  simp_rw [y, finiteLocalNorm_mulSingle_algebraMap]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_eq]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (w : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L w) : (infiniteLocalNorm L w).range = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨w'⟩ := nonempty_infinitePlacesOver L w
  have hd := (InfinitePlace.splitsCompletely_iff_forall_finrank w).1 h w'
  refine ⟨Pi.mulSingle w' (Units.map (algebraMap w.Completion
    (w' : InfinitePlace L).Completion : w.Completion →* (w' : InfinitePlace L).Completion) u), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  simp [LocalField.normUnits, Algebra.norm_algebraMap, hd]

end LocalNorms

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.mem_unitsPow_of_forall_mem_unitsPowIn
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : (IdeleGroup.diagonal K).range ⊔
      IdeleGroup.sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v))
    {y : Kˣ}
    (hyE : y ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hyS : ∀ v ∈ S, y ∈ unitsPowIn K p (v.adicCompletion K))
    (hyinf : ∀ w : InfinitePlace K, y ∈ unitsPowIn K p w.Completion) :
    y ∈ unitsPow K p := by
  classical
  by_contra hy
  let Ω := AlgebraicClosure K
  let F := kummerExtension K p Ω (radicalGroup K p y)
  have hfinF : finrank K F = p := finrank_kummerExtension_radicalGroup Ω hy
  have : IsCyclic Gal(F/K) := isCyclic_kummerExtension_radicalGroup Ω hy
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω y
  have hgen : IntermediateField.adjoin K {α} = ⊤ := by
    have hdvd : finrank K (IntermediateField.adjoin K {α}) ∣ p := by
      have := IntermediateField.finrank_dvd_of_le_right (K := K)
        (le_top : IntermediateField.adjoin K {α} ≤ ⊤)
      rwa [IntermediateField.finrank_top', hfinF] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hpp
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h1
      have hmem : α ∈ (⊥ : IntermediateField K F) :=
        h1 ▸ IntermediateField.mem_adjoin_simple_self K α
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
      have hcp : c ^ p = (y : K) := by
        apply (algebraMap K F).injective
        rw [map_pow, hc, hα]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow (Fact.out : p.Prime).ne_zero] at hcp
        exact y.ne_zero hcp.symm
      exact hy (mem_unitsPow.2 ⟨Units.mk0 c hc0, Units.ext (by simp [hcp])⟩)
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hpp, IntermediateField.finrank_top', hfinF])
  suffices h : (ideleNorm K F).range ⊔ (IdeleGroup.diagonal K).range = ⊤ by
    have h1 := hFI.finrank_eq_one_of_sup_eq_top h
    rw [hfinF] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hsplit : ∀ v ∈ S, (finiteLocalNorm F v).range = ⊤ := fun v hv ↦
    range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
      ((splitsCompletely_kummerExtension_iff v).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyS v hv) (unitsPow_le_unitsPowIn K p _) hc)))
  have hinf : ∀ w, (infiniteLocalNorm F w).range = ⊤ := fun w ↦
    range_infiniteLocalNorm_eq_top_of_splitsCompletely w
      ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyinf w) (unitsPow_le_unitsPowIn K p _) hc))
  have hunr : ∀ v, v ∉ S → v ∉ T →
      (integerUnitsOver F v).map (finiteLocalNorm F v) = localUnits v := by
    intro v hvS hvT
    obtain ⟨w⟩ := nonempty_placesOver F v
    have := w.1.isPrime
    refine map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w ?_
    refine Kummer.ramificationIdx_eq_one_of_pow_eq y hα hgen v (fun h ↦ hvS (hpS v h)) ?_
      w.1.asIdeal
    rw [valuation_eq_one_of_mem_unit hyE (by simp [hvS, hvT]), WithZero.log_one]
    exact dvd_zero _
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, s, hs, rfl⟩ := IdeleGroup.exists_diagonal_mul_of_sup_eq_top _ hS x
  have hsv : ∀ v ∉ S, IdeleGroup.finiteProj v s ∈ localUnits v := fun v hv ↦
    finiteProj_mem_localUnits ((IdeleGroup.mem_sIdeles _).1 hs v (by simpa using hv))
  obtain ⟨δ, hδ, hδT⟩ := hsurj (fun v ↦ IdeleGroup.finiteProj v s)
    (fun v hv ↦ hsv v (Finset.disjoint_right.1 hST hv))
  set t := IdeleGroup.diagonal K δ⁻¹ * s with ht_def
  have hloc : ∀ v, v ∉ S → IdeleGroup.finiteProj v t ∈ localUnits v := by
    intro v hvS
    rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal]
    exact mul_mem (units_map_mem_localUnits v (valuation_eq_one_of_mem_unit (inv_mem hδ)
      (by simpa using hvS))) (hsv v hvS)
  have ht : t ∈ (ideleNorm K F).range := by
    rw [mem_range_ideleNorm_iff]
    refine ⟨fun v ↦ ?_, fun w ↦ by rw [hinf w]; exact Subgroup.mem_top _, ?_⟩
    · by_cases hvS : v ∈ S
      · rw [hsplit v hvS]
        exact Subgroup.mem_top _
      by_cases hvT : v ∈ T
      · have hpow : IdeleGroup.finiteProj v t ∈ unitsPow (v.adicCompletion K) p := by
          rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal, map_inv]
          exact QuotientGroup.eq.1 (hδT v hvT)
        obtain ⟨b, hb⟩ := mem_unitsPow.1 hpow
        have hnorm := pow_finrank_mem_range_finiteLocalNorm (L := F) v b
        rw [hfinF, hb] at hnorm
        exact hnorm
      · exact Subgroup.map_le_range _ _ (hunr v hvS hvT ▸ hloc v hvS)
    · filter_upwards [(S.finite_toSet.union T.finite_toSet).eventually_cofinite_notMem] with v hv
      simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
      rw [hunr v hv.1 hv.2]
      exact hloc v hv.1
  have hs_eq : s = t * IdeleGroup.diagonal K δ := by
    rw [ht_def, map_inv, mul_comm, mul_inv_cancel_left]
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ⟨δ, rfl⟩))

end KummerIndex

end GroundTheory.Global
