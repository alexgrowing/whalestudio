import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem exists_continuous_div {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] {X : Type} [TopologicalSpace X]
    {π : O} (hπ : π ≠ 0) (u : X → O) (hu : Continuous u) (hd : ∀ x, π ∣ u x) :
    ∃ w : X → O, Continuous w ∧ ∀ x, u x = π * w x := by
  choose w hw using hd
  have hemb : Topology.IsClosedEmbedding (fun a : O => π * a) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (mul_right_injective₀ hπ)
  refine ⟨w, hemb.isEmbedding.continuous_iff.2 ?_, hw⟩
  have : ((fun a : O => π * a) ∘ w) = u := funext fun x => (hw x).symm
  rw [this]; exact hu

theorem phi_quot_pow_injective :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G],
      PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) →
      ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ,
      Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p O _ _ _ _ _ G _ _ _ hO ε hε z hz k
  haveI : CompactSpace O := hO.compact
  haveI : T2Space O := hO.t2
  haveI hdisc := (quot_pow_maximalIdeal_discrete_finite hO k).1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hI : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hπ : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
  generalize IsLocalRing.maximalIdeal O ^ k = I at hI hdisc
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hm' : cocycles2Map (twist ε O) (twist ε (O ⧸ I))
      (LinearMap.toSpanSingleton O (O ⧸ I) (Ideal.Quotient.mk I a)) (cont_span _ _)
      (span_twist ε _ _) z₀ ∈ (B2 (twist ε (O ⧸ I))).comap (Z2 (twist ε (O ⧸ I))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 hm
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hm'
  have hcf' : ∀ g h : G, (ε g : O) • c h - c (g * h) + c g =
      z₀.1 (g, h) • Ideal.Quotient.mk I a := fun g h => congrFun hcf (g, h)
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  have hcs : Continuous (fun g => s (c g)) := continuous_of_discreteTopology.comp hc
  set u : G × G → O := fun q =>
    a * z₀.1 q - ((ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1)) with hu
  have huc : Continuous u :=
    (continuous_const.mul z₀.2.1).sub
      ((((hε.comp continuous_fst).mul (hcs.comp continuous_snd)).sub
        (hcs.comp (continuous_fst.mul continuous_snd))).add (hcs.comp continuous_fst))
  have hud : ∀ q, ϖ ^ k ∣ u q := by
    rintro ⟨g, h⟩
    rw [← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
    have e := hcf' g h
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at e
    simp only [hu, map_sub, map_add, map_mul, hs]
    rw [e]; ring
  obtain ⟨w, hwc, hw⟩ := exists_continuous_div hπ u huc hud
  have hwZ : w ∈ Z2 (twist ε O) := by
    refine ⟨hwc, fun g h l => ?_⟩
    apply mul_left_cancel₀ hπ
    have e : (ε g : O) * z₀.1 (h, l) - z₀.1 (g * h, l) + z₀.1 (g, h * l) - z₀.1 (g, h) = 0 :=
      z₀.2.2 g h l
    have e1 := hw (h, l)
    have e2 := hw (g * h, l)
    have e3 := hw (g, h * l)
    have e4 := hw (g, h)
    simp only [hu, map_mul, Units.val_mul, mul_assoc] at e1 e2 e3 e4
    show ϖ ^ k * ((ε g : O) * w (h, l) - w (g * h, l) + w (g, h * l) - w (g, h)) = ϖ ^ k * 0
    linear_combination a * e - (ε g : O) * e1 + e2 - e3 + e4
  obtain ⟨b, hb⟩ := hz.2 (Submodule.Quotient.mk ⟨w, hwZ⟩)
  have key : a • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) =
      (ϖ ^ k * b) • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) := by
    simp only at hb
    rw [mul_smul, hb, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => s (c g), hcs, funext fun q => ?_⟩
    have e := hw q
    show (ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1) = a * z₀.1 q - ϖ ^ k * w q
    rw [← e, hu]; ring
  have hab : a = ϖ ^ k * b := hz.1 key
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

end GlobalTheory.NatQuot
